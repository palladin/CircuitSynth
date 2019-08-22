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

let getOpStruct : unit -> Ops = fun () -> { OpExprs = opExprs; Ops = ops; OpStrs = opStrs; ArityOps = arityOfOps  }


let numOfTries = 1
let numOfOps = opExprs.Length
let numOfInstrsIndex = 1
let numOfSamples = 1
let numOfVars = 3
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
                    | Func' (v, args, iops) ->
                        seq { yield expr; yield! args |> Seq.filter (fun _ -> rndBit ()) |> Seq.map rndBoolExpr' |> merge' } 
        rndBoolExpr' (getVarBoolExpr' exprs.[rand.Next(0, exprs.Length)]) |> take' n |> Array.ofSeq

let baseSample () = randoms 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray

let population : (int -> bool) -> Ops -> BoolExpr' [] [] = fun f opStruct -> 
    [| for i = 1 to 10 do 
        let (result, f, op, opStr, opExpr, instrs') = run numOfVars opStruct f 3 1 numOfSamples (baseSample ())
        let expr = compileInstrsToBoolExprs opStruct.ArityOps instrs' 
        yield expr |]



let randomSubExprs : BoolExpr' [] [] -> BoolExpr' [] [] = fun exprs -> 
    [| for expr in exprs  do yield Seq.initInfinite id |> Seq.map (fun _ -> tryWith (fun () -> rndBoolExpr (rand.Next(2, expr.Length)) expr |> updateVars) [||]) |> take' 100 |] 
    |> Seq.concat
    |> Seq.filter (fun expr -> expr.Length > 1)
    |> Seq.distinct
    |> Seq.toArray

let matches : Ops -> BoolExpr' [] [] -> (int * int * BoolExpr' []) [] = fun opStruct exprs -> 
    let dict = new Dictionary<int, int>()
    [| for i = 0 to exprs.Length - 1 do
        if dict.ContainsKey(i) then
            yield i, -1, [||]
        else
            dict.Add(i, i)
            let c = 
                [| for j = i + 1 to exprs.Length - 1 do
                    let v = equiv' (freshVars numOfVars) (toBoolExpr opStruct.OpExprs exprs.[i]) (toBoolExpr opStruct.OpExprs exprs.[j]) 
                    if v && (not <| dict.ContainsKey(j)) then
                        dict.Add(j, j)
                    yield v |] 
                |> Seq.filter id
                |> Seq.length  
            yield i, c, exprs.[i]|] 
    |> Array.sortBy (fun (_, c, _) -> -c)


let updateOps : BoolExpr' [] [] -> Ops -> Ops = fun exprs ops -> 
    ([|0..exprs.Length - 1|], exprs)
    ||> Array.zip
    |> Array.fold (fun ops' (i, expr) -> 
                                   { OpExprs = Array.append ops'.OpExprs [|toBoolExpr ops.OpExprs expr|] ;
                                     Ops = Array.append ops'.Ops [|eval' ops.Ops expr|] ;
                                     OpStrs = Array.append ops'.OpStrs [|toOpStr i|] ;
                                     ArityOps = Array.append ops'.ArityOps [|countVars expr|]  } ) ops


let rec exec : (int -> bool) -> Ops -> seq<unit> = fun f opStruct -> 
    seq {
        setTimeout(20.0)
        let exprs = population f opStruct
        printfn "%A" exprs
        yield ()
        let exprs' = randomSubExprs exprs
        printfn "%A" exprs'
        yield ()
        let matches' = matches opStruct exprs'
        printfn "%A" matches'
        yield ()
        let opStruct' = updateOps (matches' |> Array.filter (fun (_, c, _) -> c > 0) |> Array.take 1 |> Array.map (fun (_, _, expr) -> expr)) opStruct
        setTimeout(120.0)
        let (result, _, _, _, opExpr', instrs') = run numOfVars opStruct' f 3  1 numOfSamples (baseSample ())
        let expr' = compileInstrsToBoolExprs opStruct'.ArityOps instrs'
        printfn "%A" expr'
        yield ()
        let result' = verify numOfVars f (fun i -> let g = eval' opStruct'.Ops expr' in g (toBits' numOfVars i))
        printfn "%d - %d" result result'
        yield ()
        if result <> result' then
            failwith "oups"
        yield! exec f opStruct' 
    }

let enum = (exec xors <| getOpStruct ()).GetEnumerator()

enum.MoveNext()

setTimeout(120.0)
let (_, _, _, _, _, instrs') = run numOfVars (getOpStruct ()) (equalTo 12) 10 1 numOfSamples (baseSample ())

let expr' = compileInstrsToBoolExprs (getOpStruct ()).ArityOps instrs' 
verify numOfVars (equalTo 12) (fun i -> let g = eval' (getOpStruct ()).Ops expr'  in g (toBits' numOfVars i))

writeTruthTable "tt.csv" 8 [|0..255|] xors
