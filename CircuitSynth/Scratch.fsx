#I "/Users/nickpalladinos/Projects/CircuitSynth/CircuitSynth"
#load "Init.fsx"
#load "Utils.fsx"
#load "Core.fsx"
#load "BoolExpr.fsx"

open System
open System.Diagnostics
open System.Collections.Generic
open Microsoft.Z3
open Utils
open Init
open Core
open BoolExpr



type Ops = { OpExprs : (BoolExpr -> BoolExpr [] -> BoolExpr) [];
             Ops : (bool [] -> bool) [];
             OpStrs : (string [] -> string) [];
             ArityOps : int [] }

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

let opStruct : Ops = { OpExprs = opExprs; Ops = ops; OpStrs = opStrs; ArityOps = arityOfOps  }

let rec run : int -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> 
              (bool [] -> bool) [] ->
              (string [] -> string) [] -> 
              (int -> bool) -> 
              int -> int -> int -> int -> int -> int [] -> int [] -> int -> int [] -> ((int -> bool) * (bool[] -> bool) * (string [] -> string) * (BoolExpr -> BoolExpr [] -> BoolExpr)) = 
    fun numOfVars opExprs ops opStrs verify n numOfTries numOfOps numOfInstrsIndex numOfSamples arityOfOps ignore result baseSample ->
        let final = int (2.0 ** (float numOfVars))
        let stats = Array.init final (fun i ->  0)

        let rec run' : int -> int -> (Status * int * Instrs' * TimeSpan) [] -> (Status * int * Instrs' * TimeSpan * int []) = 
            fun numOfSamples numOfInstrsIndex old ->
                //let baseSample = randoms (int DateTime.Now.Ticks) 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray
                let sample = (baseSample, stats) ||> Array.zip |> Array.map (fun (i, c)  -> (i, c)) |> Array.sortBy snd |> Array.map fst
                let sample = getSample verify sample numOfSamples
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
                    |> Seq.take numOfTries
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

        let opExpr = compileInstrs' opExprs arityOfOps instrs' 
        let ops = evalInstrs' ops instrs'
        let opStr = toOpStr numOfVars
        let arityOfOp = numOfVars
        ((fun i -> ops (toBits' numOfVars i)), ops, opStr, opExpr)



let numOfTries = 1
let numOfOps = opExprs.Length
let numOfInstrsIndex = 1
let numOfSamples = 1
let numOfVars = 5
let final = int (2.0 ** (float numOfVars))

let xors = (fun i -> xors <| toBits' numOfVars i)
let isEven = (fun i -> i % 2 = 0)
let equalTo n = (fun i -> i = n)


let rndBoolExpr : int -> BoolExpr' [] -> BoolExpr' [] = 
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
        rndBoolExpr' (getVarBoolExpr' exprs.[rand.Next(0, exprs.Length)]) |> take' n |> Array.ofSeq

let baseSample () = randoms 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray

let population : (int -> bool) -> Ops -> BoolExpr' [] [] = fun f opStruct -> 
    setTimeout(20.0)
    [| for i = 1 to 10 do 
        let (f, op, opStr, opExpr) = run numOfVars opStruct.OpExprs opStruct.Ops opStruct.OpStrs f 0 numOfTries opStruct.OpExprs.Length 1 numOfSamples opStruct.ArityOps [||] 0 (baseSample ())
        let vars = freshVars 8
        let expr = opExpr (Var "res") vars |> toBoolExpr' |> removeVars |> updateVars
        yield expr |]


let randomSubExprs : BoolExpr' [] [] -> BoolExpr' [] [] = fun exprs -> 
    [| for expr in exprs  do yield [|1..expr.Length|] |> Seq.map (fun _ -> tryWith (fun () -> rndBoolExpr (rand.Next(3, expr.Length)) expr |> updateVars) [||]) |> Seq.distinct |] 
    |> Seq.concat
    |> Seq.filter (fun expr -> expr.Length > 1)
    |> Seq.toArray

let matches : BoolExpr' [] [] -> (int * int * BoolExpr' []) [] = fun exprs -> 
    let dict = new Dictionary<int, int>()
    [| for i = 0 to exprs.Length - 1 do
        if dict.ContainsKey(i) then
            yield i, -1, [||]
        else
            dict.Add(i, i)
            let c = 
                [| for j = i + 1 to exprs.Length - 1 do
                    let v = equiv' (freshVars numOfVars) (exprs.[i] |> toBoolExpr) (exprs.[j] |> toBoolExpr) 
                    if v && (not <| dict.ContainsKey(j)) then
                        dict.Add(j, j)
                    yield v |] 
                |> Seq.filter id
                |> Seq.length  
            yield i, c, exprs.[i]|] |> Array.sortBy (fun (_, c, _) -> -c)


let updateOps : BoolExpr' [] [] -> int -> Ops -> Ops = fun exprs n ops -> 
    ([|0..exprs.Length - 1|], exprs)
    ||> Array.zip
    |> Array.take n 
    |> Array.fold (fun ops (i, expr) -> 
                                   { OpExprs = Array.append [|toBoolExpr expr|] ops.OpExprs;
                                     Ops = Array.append [|eval' expr|] ops.Ops;
                                     OpStrs = Array.append [|toOpStr i|] ops.OpStrs;
                                     ArityOps = Array.append [|countVars expr|] ops.ArityOps } ) ops



let exprs = population isPowerOfTwo opStruct
let exprs' = randomSubExprs exprs


let matches' = matches exprs'

let opStruct' = updateOps (matches' |> Array.map (fun (_, _, expr) -> expr)) 6 opStruct

setTimeout(180.0)
let (f, op, opStr, opExpr) = run numOfVars opStruct'.OpExprs opStruct'.Ops opStruct'.OpStrs isPowerOfTwo 0 3 opStruct'.OpExprs.Length 1 numOfSamples opStruct'.ArityOps[||] 0 (baseSample ())

run numOfVars opStruct.OpExprs opStruct.Ops opStruct.OpStrs isPrime 0 10 opStruct.OpExprs.Length 1 numOfSamples opStruct.ArityOps[||] 0 (baseSample ())


writeTruthTable "tt.csv" 8 [|0..255|] xors
