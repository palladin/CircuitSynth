#I "/Users/nickpalladinos/Projects/CircuitSynth/CircuitSynth"
#load "Init.fsx"
#load "Utils.fsx"
#load "CoreTypes.fsx"
#load "Core.fsx"
#load "BoolExpr.fsx"

open System
open System.Diagnostics
open System.Collections.Generic
open Microsoft.Z3
open Utils
open Init
open CoreTypes
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

let opExprs' : BoolExpr' [] [] = 
    [|[|Or' (string (FreshVar ()), "x0", "x1")|];
      [|And' (string (FreshVar ()), "x0", "x1")|];
      [|Not' (string (FreshVar ()), "x0")|];
    |]

let opStrs : (string [] -> string) [] = 
    [|(fun args -> sprintf "%s or %s" args.[0] args.[1]);
      (fun args -> sprintf "%s and %s" args.[0] args.[1]);
      (fun args -> sprintf "not %s" args.[0]);
      //(fun args -> sprintf "%s xor %s" args.[0] args.[1])
    |]

let getOpStruct : unit -> Ops = fun () -> { OpExprs = opExprs; 
                                            Ops = ops;
                                            OpStrs = opStrs; 
                                            OpExprs' = opExprs';
                                            ArityOps = arityOfOps;
                                            Active = [|true; true; true|]  }


let numOfTries = 1
let numOfOps = opExprs.Length
let numOfInstrsIndex = 1
let numOfSamples = 1
let numOfVars = 6
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
                        seq { yield expr; yield! args |> randomize |> Seq.filter (fun _ -> rndBit ()) |> Seq.map rndBoolExpr' |> merge' } 
        rndBoolExpr' (getVarBoolExpr' exprs.[rand.Next(0, exprs.Length)]) |> take' n |> Array.ofSeq

let baseSample : (int -> bool) -> unit -> int [] = fun f () -> 
    let sample = randoms 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray
    getSample f sample final

let population : (int -> bool) -> (unit -> int[]) -> Ops -> (int * BoolExpr' []) [] = fun f samplef opStruct -> 
    [| for i = 1 to 10 do 
        let (result, pos, f, op, opStr, opExpr, instrs', _) = run numOfVars opStruct f 5 1 numOfSamples samplef
        let expr = compileInstrsToBoolExprs opStruct.ArityOps instrs' 
        yield (result, expr) |]

let ranges : (int -> bool) -> Ops -> seq<int * BoolExpr' []> = fun f opStruct -> 
    seq {
        let posRef = ref 0
        let flag = ref false
        while not !flag do
            let (result, pos, _, _, _, _, instrs', _) = run numOfVars opStruct f 3 1 1 (fun () -> [|!posRef  .. final - 1|])
            posRef := !posRef + (pos - 1)
            if !posRef = final - 1 || result = final  then
                flag := true
            let expr = compileInstrsToBoolExprs opStruct.ArityOps instrs' 
            yield (result, expr)
    }

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
            yield (-1, -1, [||])
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
            yield (c, countOps' exprs.[i], exprs.[i]) |] 
    |> Array.filter (fun (c, cp,  _) -> c > 0) 
    |> Array.filter (fun (c, cp,  _) -> cp > 1) 
    |> Array.sortBy (fun (c, cp, _) -> (cp, c))
    |> Array.rev


let updateOps : BoolExpr' [] [] -> Ops -> Ops = fun exprs ops -> 
    ([|0..exprs.Length - 1|], exprs)
    ||> Array.zip
    |> Array.fold (fun ops' (i, expr) -> 
                                   { OpExprs = Array.append ops'.OpExprs [|toBoolExpr ops.OpExprs expr|] ;
                                     Ops = Array.append ops'.Ops [|eval' ops.Ops expr|] ;
                                     OpStrs = Array.append ops'.OpStrs [|toOpStr ops'.OpStrs.Length|] ;
                                     OpExprs' = Array.append ops'.OpExprs' [|expr|] ;
                                     ArityOps = Array.append ops'.ArityOps [|countVars expr|] ;
                                     Active = Array.append ops'.Active [|true|] } ) ops


let rec exec : int -> (int -> bool) -> Ops -> seq<unit> = fun i f opStruct -> 
    seq {
        setTimeout(20.0 * float i)
        //let (_, _, _, _, _, _, stats) = run numOfVars opStruct f 3 1 numOfSamples (baseSample f)
        //printfn "%A" stats
        //yield ()
        //let samplef = (fun () -> stats |> Array.map fst |> (fun s -> getSample f s final))
        //let samplef = (fun () -> getSample f ([|0..final - 1|] |> randomize) final)
        //let results = population f samplef opStruct
        //for (result, expr) in ranges f opStruct  do
        //    yield ()
        let results = ranges f opStruct |> Seq.toArray
        printfn "%A" results
        let exprs = results |> Array.map snd 
        yield ()
        let exprs' = randomSubExprs exprs
        printfn "%A" exprs'
        yield ()
        let matches' = matches opStruct exprs'
        printfn "%A" matches'
        yield ()
        for i = 3 to opStruct.Ops.Length - 1 do
            opStruct.Active.[i] <- false
        let opStruct' = updateOps (matches' |> (*take' 3 |> Seq.toArray |>*) Array.map (fun (_, _, expr) -> expr)) opStruct
        //setTimeout(120.0)
        //let (result, _,  _, _, _, opExpr', instrs', _) = run numOfVars opStruct' f 5 1 numOfSamples samplef
        //let expr' = compileInstrsToBoolExprs opStruct'.ArityOps instrs'
        //printfn "%A" expr'
        //yield ()
        //let result' = verify numOfVars f (fun i -> let g = eval' opStruct'.Ops expr' in g (toBits' numOfVars i))
        //printfn "%d - %d" result result'
        //yield ()
        //if result <> result' then
        //    failwith "oups"
        //if result' <> final then
        yield! exec (i + 1) f opStruct' 
    }

let enum = (exec 1 isPrime <| getOpStruct ()).GetEnumerator()


enum.MoveNext()


while enum.MoveNext() do
    ()

    

setTimeout(120.0)
let _ = run numOfVars (getOpStruct ()) isPrime 3 1 numOfSamples (fun () -> [|0 .. final - 1|])
//let (_, _, _, _, _, _, _) = run numOfVars (getOpStruct ()) isPowerOfTwo 10 1 numOfSamples (fun () -> stats |> Array.map fst)



//let expr' = compileInstrsToBoolExprs (getOpStruct ()).ArityOps instrs' 
//verify numOfVars (equalTo 12) (fun i -> let g = eval' (getOpStruct ()).Ops expr'  in g (toBits' numOfVars i))

writeTruthTable "tt.csv" 8 [|0..255|] xors



