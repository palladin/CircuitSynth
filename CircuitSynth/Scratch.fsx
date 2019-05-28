#I "/Users/nickpalladinos/Projects/CircuitSynth/CircuitSynth"
#load "Init.fsx"
#load "Utils.fsx"
#load "Core.fsx"

open System
open System.Diagnostics
open System.Collections.Generic
open Microsoft.Z3
open Utils
open Init
open Core

let arityOfOps = [|2;
                   2;
                   1;
                   2;
                 |]
let ops : (bool [] -> bool) [] = 
    [|(fun args -> args.[0] || args.[1]);
      (fun args -> args.[0] && args.[1]);
      (fun args -> not args.[0]);
      (fun args -> xor args.[0] args.[1])
    |]

let opExprs : (BoolExpr -> BoolExpr [] -> BoolExpr) [] = 
    [|(fun var args -> Eq [|var|] [|Or [|args.[0]; args.[1]|]|]);
      (fun var args -> Eq [|var|] [|And [|args.[0]; args.[1]|]|]);
      (fun var args -> Eq [|var|] [|Not args.[0]|]);
      (fun var args -> Eq [|var|] [|Xor args.[0] args.[1]|]);
    |]

let opStrs : (string [] -> string) [] = 
    [|(fun args -> sprintf "%s or %s" args.[0] args.[1]);
      (fun args -> sprintf "%s and %s" args.[0] args.[1]);
      (fun args -> sprintf "not %s" args.[0]);
      (fun args -> sprintf "%s xor %s" args.[0] args.[1])
    |]

let rec run : int -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> 
              (bool [] -> bool) [] ->
              (string [] -> string) [] -> 
              (int -> bool) -> 
              int -> int -> int -> int -> int -> int [] -> int [] -> int -> int [] -> ((int -> bool) * (bool[] -> bool) * (string [] -> string) * (BoolExpr -> BoolExpr [] -> BoolExpr)) = 
    fun numOfVars opExprs ops opStrs verify n numOfTries numOfOps numOfInstrsIndex numOfSamples arityOfOps ignore result baseSample ->
        let final = int (2.0 ** (float numOfVars))
        let stats = Array.init final (fun _ -> 0)
        if n = numOfTries || result = final then 
            ((fun i -> ops.[0] (toBits' numOfVars i)), ops.[0], opStrs.[0], opExprs.[0])
        else
            let rec run' : int -> int -> (Status * int * Instrs' * TimeSpan) [] -> (Status * int * Instrs' * TimeSpan * int []) = 
                fun numOfSamples numOfInstrsIndex old ->
                    //let baseSample = randoms (int DateTime.Now.Ticks) 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray
                    let baseSample = stats |> Array.mapi (fun i c -> (i, c)) |> Array.sortBy snd |> Array.map fst
                    let sample = getSample verify baseSample numOfSamples
                    let sample = Array.append sample ignore
                    if sample.Length <> (sample |> Array.distinct |> Array.length) then
                        failwithf "Duplicate elements - base %A - sample %A " baseSample sample
                    if old.Length <> 0 then
                        let (_, _, instrs', _) = old.[0]
                        let f = evalInstrs' ops instrs'
                        for i in [|0..final - 1|] do
                            if f <| toBits' numOfVars i = verify i then
                                stats.[i] <- stats.[i] + 1
                        //printfn "Stats %A " (stats |> Array.mapi (fun i c -> (i, c)) |> Array.sortBy snd)

                    let result =
                        seq {
                            for numOfInstrs in {numOfInstrsIndex..100} do
                                let availableOpExprs = 
                                    if opExprs.Length > numOfOps then 
                                        Array.append [|0|] 
                                                        ([|1..numOfOps|] |> Array.map (fun i -> opExprs.Length - i))
                                    else 
                                        opExprs |> Array.mapi (fun i _ -> i)
                                let watch = new Stopwatch()
                                watch.Start()
                                let (status, result, instrs') = find numOfVars opExprs ops opStrs availableOpExprs verify sample [|0..final - 1|] arityOfOps numOfInstrs
                                watch.Stop()
                                printfn "%d %d %d %A %A %A" sample.Length n numOfInstrs availableOpExprs (status, result) watch.Elapsed
                                yield (numOfInstrs, status, result, instrs', watch.Elapsed)
                        }
                        |> Seq.filter (fun (_, status, _, _, _) -> status <> Status.UNSATISFIABLE)
                        |> Seq.take 6
                        |> Seq.filter (fun (_, status, _, _, _) -> status = Status.SATISFIABLE)
                        |> Seq.tryHead
                    match result with
                    | Some (numOfInstrs, Status.SATISFIABLE, result, instrs', elapsed) when result = final -> 
                        printfn "%s" <| strInstrs opStrs arityOfOps instrs'
                        (Status.SATISFIABLE, result, instrs', elapsed, sample)
                    | Some (numOfInstrs, Status.SATISFIABLE, result, instrs', elapsed) ->
                        printfn "%s" <| strInstrs opStrs arityOfOps instrs'
                        run' (numOfSamples + 1) numOfInstrs (Array.append [|(Status.SATISFIABLE, result, instrs', elapsed)|] old)
                    | None ->
                        if old.Length = 0 then failwith "UNKNOWN"
                        let (status, result, instrs', elapsed) = old.[0]
                        printfn "%s" <| strInstrs opStrs arityOfOps instrs'
                        (status, result, instrs', elapsed, sample)
                    | _ -> failwith "oups"
            let (status, result, instrs', elapsed, sample) = run' numOfSamples numOfInstrsIndex [||]
            printfn "%d %A %A" n (status, result) elapsed
            
            let opExprs = (Array.append [|compileInstrs' opExprs arityOfOps instrs'|] opExprs) 
            let ops = (Array.append [|evalInstrs' ops instrs'|] ops)
            let opStrs = (Array.append [|fun args -> sprintf "func%d(%s)" numOfVars (String.concat "," args)|] opStrs)
            let arityOfOps = Array.append [|numOfVars|] arityOfOps
            run numOfVars opExprs ops opStrs verify (n + 1) numOfTries numOfOps numOfInstrsIndex numOfSamples arityOfOps sample result baseSample

let freshVars numOfVars = [|0..numOfVars - 1|] |> Array.map (fun i -> Var ("x" + string i))

let seed = int DateTime.Now.Ticks
let random = new Random(seed)


let numOfTries = 1
let numOfOps = opExprs.Length
let numOfInstrsIndex = 1
let numOfSamples = 1
let numOfVars = 8
let final = int (2.0 ** (float numOfVars))

let xors = (fun i -> xors <| toBits' numOfVars i)
let isEven = (fun i -> i % 2 = 0)
let equalTo n = (fun i -> i = n)


let allBoolExprs : int -> BoolExpr' [] -> seq<BoolExpr' []> = 
    fun n exprs ->
        let i = ref -1
        let lookupMap = exprs |> toMapBoolExpr
        let map = new Dictionary<string, string>()
        let rec allBoolExprs' : int -> string -> seq<BoolExpr' []> = 
            fun n name ->
                match Map.tryFind name lookupMap with
                | None -> Seq.empty
                | Some expr ->
                    match expr with
                    | And' _ | Or' _ | Not' _ when n = 0 -> 
                            if not <| map.ContainsKey(name) then 
                                incr i
                                map.Add(name, sprintf "y%d" !i)
                            seq { yield [|Var' (name, map.[name])|] }
                    | Var' (v, x) when n = 0 && x.StartsWith("x") -> 
                            if not <| map.ContainsKey(x) then 
                                incr i
                                map.Add(x, sprintf "y%d" !i)
                            seq { yield [|Var' (v, map.[x])|] }
                    | And' (v, x, y) | Or' (v, x, y) as expr -> 
                            seq { for (i, j) in split (n - 1) do 
                                    for xs in allBoolExprs' i x do
                                        for ys in allBoolExprs' j y do
                                            yield  Array.append [|expr|] (Array.append xs ys) } 
                            |> Seq.filter (fun x -> countOps' x = n)
                    | Not' (v, x) as expr -> 
                            seq { for xs in allBoolExprs' (n - 1) x -> Array.append [|expr|] xs }
                            |> Seq.filter (fun x -> countOps' x = n)
                    | Var' (v, x) as expr -> 
                        seq { for xs in allBoolExprs' n x -> Array.append [|expr|] xs }
                        |> Seq.filter (fun x -> countOps' x = n)
        allBoolExprs' n (topVarBoolExpr' exprs)
        |> Seq.filter (fun x -> countOps' x = n)
        //|> Seq.collect (fun expr -> seq { yield expr; yield Not' expr })
        |> Seq.map Array.distinct
        



let getVars : string -> BoolExpr' [] -> string [] = fun prefix exprs ->
    exprs 
    |> Seq.filter (function Var' (_, x) when x.StartsWith(prefix) -> true | _ -> false) 
    |> Seq.map (function Var' (_, x) -> x) 
    |> Seq.distinct
    |> Seq.toArray


let countVars : string -> BoolExpr' [] -> int = fun prefix exprs ->
    exprs |> getVars prefix |> Seq.length
    
let updateVars : BoolExpr' [] -> BoolExpr' [] = fun exprs ->
    let vars = exprs |> getVars "y"
    let vars' = exprs |> getVars "y" |> Array.mapi (fun i _ -> sprintf "x%d" i) 
    exprs |> Array.map (function | Var' (v, x) when x.StartsWith("y") -> Var' (v, vars'.[Array.findIndex ((=) x) vars])
                                 | And' _ | Or' _ | Not' _  | Var' _ as expr -> expr)
    
let matchBoolExpr : int -> BoolExpr' [] -> BoolExpr' [] -> (BoolExpr' [] * BoolExpr' []) [] = 
    fun numOfOps xs ys ->
        let xs = [|0..xs.Length - 1|]
                 |> Seq.collect (fun i -> allBoolExprs numOfOps xs.[i..xs.Length - 1])
                 |> Seq.map updateVars
                 |> Seq.toArray
        let ys = [|0..ys.Length - 1|]
                 |> Seq.collect (fun i -> allBoolExprs numOfOps ys.[i..ys.Length - 1])
                 |> Seq.map updateVars
                 |> Seq.toArray
        let result = 
            xs 
            |> Seq.collect (fun x -> ys |> Seq.map (fun y -> (x, y)))
            |> Seq.filter (fun (x, y) -> countVars "x" x = countVars "x" y)
            |> Seq.toArray
        result
        //let equals = 
        //    result 
        //    |> Seq.filter (fun (x, y) -> x = y)
        //    |> Seq.toArray
        //let result' = result |> Array.filter (fun (x, y) -> not (x = y))
        //let numOfVars = if result'.Length = 0 then 0 else (result' |> Array.map (fun (x, y) -> max (countVars "x" x) (countVars "x" y)) |> Array.max)
        //let bools = equivs (freshVars numOfVars) (result' |> Array.map (fun (expr, _) -> toBoolExpr expr)) (result' |> Array.map (fun (_, expr) -> toBoolExpr expr))
        //let equivs = 
        //    result' 
        //    |> Seq.mapi (fun i (x, y) -> (bools.[i], x, y))
        //    |> Seq.filter (fun (b, x, y) -> b)
        //    |> Seq.map (fun (b, x, y) -> (x, y))
        //    |> Seq.toArray
        //Array.append equals equivs

       

let rec exec : int list -> (int -> bool) -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> 
              (bool [] -> bool) [] ->
              (string [] -> string) [] -> int [] -> 
              (BoolExpr -> BoolExpr [] -> BoolExpr) = 
    fun ns f opExprs ops opStrs arityOfOps ->
        match ns with
        | (n :: ns) ->
            printfn "n: %d -------------------------------" n
            let (_, op, opStr, opExpr) = run n opExprs ops opStrs f 0 numOfTries opExprs.Length numOfInstrsIndex numOfSamples arityOfOps [||] 0 [|0..int (2.0 ** (float n)) - 1|]
            let ops = Array.append [|op|] ops
            let opStrs = Array.append [|opStr|] opStrs
            let opExprs = Array.append [|opExpr|] opExprs
            let arityOfOps = Array.append [|n|] arityOfOps 
            exec ns f opExprs ops opStrs arityOfOps 
        | [] -> opExprs.[0] 

let exprf : BoolExpr -> BoolExpr [] -> BoolExpr = 
    exec [8..8] (equalTo 100) opExprs ops opStrs arityOfOps 

let exprf' : BoolExpr -> BoolExpr [] -> BoolExpr = 
    exec [2..8] (equalTo 100) opExprs ops opStrs arityOfOps 

let expr = exprf (Var "res") (freshVars 8) 
let expr' = expr |> toBoolExpr' 
(expr |> string) = (expr' |> toBoolExpr |> string)

let expr'' = expr' |> allBoolExprs 4 |> Seq.map updateVars |> Seq.toArray

matchBoolExpr 4 expr' expr'

equiv' (freshVars 8) exprf exprf'




writeTruthTable "tt.csv" 8 [|0..255|] xors
