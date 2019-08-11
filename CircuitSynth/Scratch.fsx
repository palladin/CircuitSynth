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
        //           2;
                 |]
let ops : (bool [] -> bool) [] = 
    [|(fun args -> args.[0] || args.[1]);
      (fun args -> args.[0] && args.[1]);
      (fun args -> not args.[0]);
      //(fun args -> xor args.[0] args.[1])
    |]

let opExprs : (BoolExpr -> BoolExpr [] -> BoolExpr) [] = 
    [|(fun var args -> Eq [|var|] [|Or [|args.[0]; args.[1]|]|]);
      (fun var args -> Eq [|var|] [|And [|args.[0]; args.[1]|]|]);
      (fun var args -> Eq [|var|] [|Not args.[0]|]);
      //(fun var args -> Eq [|var|] [|Xor args.[0] args.[1]|]);
    |]

let opStrs : (string [] -> string) [] = 
    [|(fun args -> sprintf "%s or %s" args.[0] args.[1]);
      (fun args -> sprintf "%s and %s" args.[0] args.[1]);
      (fun args -> sprintf "not %s" args.[0]);
      //(fun args -> sprintf "%s xor %s" args.[0] args.[1])
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


let rndBoolExpr : int -> BoolExpr' [] -> seq<BoolExpr'> = 
    fun n exprs ->
        let lookupMap = exprs |> toMapBoolExpr
        let rec rndBoolExpr' : string -> seq<BoolExpr'> = 
            fun name ->
                match Map.tryFind name lookupMap with
                | None -> Seq.empty
                | Some expr ->
                    match expr with
                    | And' (v, x, y) | Or' (v, x, y) as expr -> 
                        seq { yield expr; yield! [|x; y|] |> Seq.filter (fun _ -> rndBit ()) |> Seq.map rndBoolExpr' |> merge' } 
                    | Not' (v, x) as expr -> 
                        seq { yield expr; yield! [|x|] |> Seq.collect rndBoolExpr'  } 
                    | Var' (v, x) as expr -> failwith "oups"
        rndBoolExpr' (getVarBoolExpr' exprs.[n])


let removeVars : BoolExpr' [] -> BoolExpr' [] = fun exprs -> 
    let dict = toDictBoolExpr exprs
    let f : string -> string = fun name -> 
        if dict.ContainsKey(name) then
            match dict.[name] with
            | Var' (v, x) -> 
                dict.Remove(v) |> ignore 
                x
            | _ -> name
        else name
    for expr in exprs do
        match expr with
        | And' (v, x, y) -> dict.[v] <- And' (v, f x, f y)
        | Or' (v, x, y) -> dict.[v] <- Or' (v, f x, f y)
        | Not' (v, x) -> dict.[v] <- Not' (v, f x)
        | Var' (v, _) -> dict.Remove(v) |> ignore
    [| for keyValue in dict do yield keyValue.Value  |]

let updateLeafVars : BoolExpr' [] -> BoolExpr' [] = fun exprs ->
    let exprs = exprs |> Seq.toArray
    let lookupMap = exprs |> toMapBoolExpr
    let dict = new Dictionary<string, string>()
    let i = ref -1
    let f : string -> string = fun name -> 
        match Map.tryFind name lookupMap with
        | None -> 
            if dict.ContainsKey(name) then
                dict.[name]
            else 
                incr i;
                let v = sprintf "x%d" !i
                dict.Add(name, v)
                v
        | Some _ ->
            name
    for i = 0 to exprs.Length - 1 do
        match exprs.[i] with
        | And' (v, x, y) -> exprs.[i] <- And' (v, f x, f y)
        | Or' (v, x, y) -> exprs.[i] <- Or' (v, f x, f y)
        | Not' (v, x) -> exprs.[i] <- Not' (v, f x)
        | Var' (_, _) -> failwith "oups"
    exprs


let n = 5
let (_, op, opStr, opExpr) = run n opExprs ops opStrs isPowerOfTwo 0 numOfTries opExprs.Length 15 numOfSamples arityOfOps [||] 0 [|0..int (2.0 ** (float n)) - 1|]
let (_, op', opStr', opExpr') = run n opExprs ops opStrs isPowerOfTwo 0 numOfTries opExprs.Length 13 numOfSamples arityOfOps [||] 0 [|0..int (2.0 ** (float n)) - 1|]


let vars = freshVars 8
let expr = opExpr (Var "res") vars |> toBoolExpr' |> removeVars 



let exprs = rndBoolExpr 0 expr |> take' 5 |> Array.ofSeq 
exprs |> updateLeafVars


equiv' (freshVars 8) opExpr (expr |> toBoolExpr)



writeTruthTable "tt.csv" 8 [|0..255|] xors
