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
let final = twoPower numOfVars

let xors = (fun i -> xors <| toBits' numOfVars i)
let isEven = (fun i -> i % 2 = 0)
let equalTo n = (fun i -> i = n)


let getBoolExpr' : BoolExpr' -> BoolExpr' [] -> BoolExpr' [] = fun root exprs ->
    let lookupMap = exprs |> toMapBoolExpr
    let rec run : string -> BoolExpr' [] = fun name ->
        match Array.tryFind (fun (key, _) -> key = name) lookupMap with
        | Some (_, expr) -> 
            match expr with
            | And' (v, x, y) -> 
                Array.append [|And' (v, x, y)|] ([|x; y|] |> Array.map run |> Array.concat)
            | Or' (v, x, y) -> 
                Array.append [|Or' (v, x, y)|] ([|x; y|] |> Array.map run |> Array.concat)
            | Not' (v, x) ->
                Array.append [|Not' (v, x)|] (run x) 
            | Func' (v, args, iop) -> 
                Array.append [|Func' (v, args, iop)|] (args |> Array.map run |> Array.concat)
            | _ -> failwith "oups"
        | None when name.StartsWith("x") -> [||]
        | None -> failwithf "not found %s" name
    run (getVarBoolExpr' root) |> Array.distinct


let rndBoolExpr : BoolExpr' [] -> seq<BoolExpr'> = 
    fun exprs ->
        let lookupMap = exprs |> toMapBoolExpr
        let rootExpr = exprs.[rand.Next(0, exprs.Length)]
        let rootExprs = getBoolExpr' rootExpr exprs
        let rec rndBoolExpr' : string -> seq<BoolExpr'> = 
            fun name ->
                match Array.tryFind (fun (key, _) -> key = name) lookupMap with
                | None -> Seq.empty
                | Some (_, expr) ->
                    match expr with
                    | And' (v, x, y) | Or' (v, x, y) as expr -> 
                        seq { yield expr; yield! [|x; y|] 
                                                 |> randomize 
                                                 |> Seq.map rndBoolExpr' 
                                                 |> merge' } 
                    | Not' (v, x) as expr -> 
                        seq { yield expr; yield! [|x|] 
                                                 |> Seq.collect rndBoolExpr'  } 
                    | Var' (v, x) as expr -> failwith "oups"
                    | Func' (v, args, iops) ->
                        seq { yield expr; yield! args |> randomize |> Seq.map rndBoolExpr' |> merge' } 
        rndBoolExpr' (getVarBoolExpr' rootExpr) 

let baseSample : (int -> bool) -> unit -> int [] = fun f () -> 
    let sample = randoms 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray
    getSample f sample final

let population : (int -> bool) -> (unit -> int[]) -> Ops -> (int * BoolExpr' []) [] = fun f samplef opStruct -> 
    [| for i = 1 to 10 do 
        let (result, pos, f, op, opStr, opExpr, instrs', expr) = run numOfVars opStruct f 5 1 numOfSamples samplef
        yield (result, expr) |]

let ranges : (int -> bool) -> Ops -> seq<int * BoolExpr' []> = fun f opStruct -> 
    seq {
        
        let values = 
            [|0 .. final - 1|]
            |> Array.filter f

        printfn "Values: %A" values
        for n = 1 to values.Length do
            let (result, pos, _, _, _, _, instrs', expr) = 
                run numOfVars opStruct (fun i -> values |> Array.take n |> Array.exists (fun j -> j = i)) 3 1 1 (fun () -> [|0  .. final - 1|])
            yield (result, expr)
    }

let randomSubExprs : BoolExpr' [] [] -> seq<BoolExpr' []> = fun exprs -> 
    seq { for expr in exprs  do yield Seq.initInfinite id |> Seq.map (fun _ -> tryWith (fun () -> rndBoolExpr expr |> Seq.distinct |> take' (rand.Next(1, expr.Length + 1)) |> Seq.toArray) [||]) }
    |> Seq.concat
    |> Seq.filter (fun expr -> expr.Length > 1)
    |> Seq.distinct

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


let collapse : BoolExpr' [] [] -> BoolExpr' [] -> BoolExpr' [] = fun ops exprs -> 
    let run' : BoolExpr' [] -> BoolExpr' [] = fun exprs -> 
        exprs |> Array.map (function | And' (v, x, y) -> [|And' (v, x, y)|]
                                     | Or' (v, x, y) -> [|Or' (v, x, y)|]
                                     | Not' (v, x) -> [|Not' (v, x)|]
                                     | Func' (v, args, iop) -> 
                                        let exprs' = subs args ops.[iop]
                                        exprs'.[0] <- updateVarBoolExpr' exprs'.[0] v
                                        exprs'
                                     | _ -> failwith "oups")
              |> Array.concat
    fixedPoint (fun exprs -> run' exprs) exprs


let updateOps : BoolExpr' [] [] -> Ops -> Ops = fun exprs ops -> 
    ([|0..exprs.Length - 1|], exprs)
    ||> Array.zip
    |> Array.fold (fun ops' (i, expr) -> 
                                   { OpExprs = Array.append ops'.OpExprs [|compileToBoolExpr (collapse ops.OpExprs' expr)|] ;
                                     Ops = Array.append ops'.Ops [|eval' ops.Ops expr|] ;
                                     OpStrs = Array.append ops'.OpStrs [|toOpStr ops'.OpStrs.Length|] ;
                                     OpExprs' = Array.append ops'.OpExprs' [|expr|] ;
                                     ArityOps = Array.append ops'.ArityOps [|countVars expr|] ;
                                     Active = Array.append ops'.Active [|true|] } ) ops



let rec exec : int -> (int -> bool) -> Ops -> seq<unit> = fun i f opStruct -> 
    seq {
        setTimeout(20.0 * float 1)

        //for (result, expr) in ranges f opStruct  do
        //    yield ()

        let results = ranges f opStruct |> Seq.toArray
        printfn "%A" results
        let exprs = results |> Array.map snd 
        yield ()
        let exprs' = randomSubExprs exprs |> Seq.take 10 |> Seq.toArray
        printfn "%A" exprs'
        yield ()
        let matches' = matches opStruct exprs'
        printfn "%A" matches'
        yield ()

        //for i = 3 to opStruct.Ops.Length - 1 do
            //opStruct.Active.[i] <- false

        let matchedExprs = matches' |> Array.map (fun (_, _, expr) -> expr)
        //let opStruct' = updateOps matchedExprs opStruct

        setTimeout(20.0 * float 1)
        let ranks = 
            [| for matchedExpr in matchedExprs do
                let opStruct' = updateOps [|matchedExpr|] opStruct
                let (result, _,  _, _, _, opExpr', instrs', expr') = run numOfVars opStruct' f 3 1 1 (fun () -> [|0 .. final - 1|])
                yield (result, matchedExpr) |] 
            |> Array.sortBy (fun (result, _) -> -result)

        printfn "%A" ranks
        yield ()
        let opStruct' = updateOps (ranks |> Array.map snd |> take' 1 |> Seq.toArray) opStruct
        //let expr' = compileInstrsToBoolExprs opStruct'.ArityOps instrs'
        //printfn "%A" expr'
        //yield ()
        //let result' = verify numOfVars f (fun i -> let g = eval' opStruct'.Ops expr' in g (toBits' numOfVars i))
        //printfn "%d - %d" result result'
        //yield ()
        //if result <> result' then
         //   failwith "oups"
        //if result' <> final then
        yield! exec (i + 1) f opStruct' 
    }

//let enum = (exec 1 isPowerOfTwo <| getOpStruct ()).GetEnumerator()


//enum.MoveNext()


//while enum.MoveNext() do
//    ()




let cleanupBoolExpr' : BoolExpr' [] -> BoolExpr' [] = fun exprs ->
    let lookupMap = exprs |> toMapBoolExpr
    let rec run : string -> BoolExpr' [] = fun name ->
        match Array.tryFind (fun (key, _) -> key = name) lookupMap with
        | Some (_, expr) -> 
            match expr with
            | And' (v, x, y) -> 
                Array.append [|And' (v, x, y)|] ([|x; y|] |> Array.map run |> Array.concat)
            | Or' (v, x, y) -> 
                Array.append [|Or' (v, x, y)|] ([|x; y|] |> Array.map run |> Array.concat)
            | Not' (v, x) ->
                Array.append [|Not' (v, x)|] (run x) 
            | Func' (v, args, iop) -> 
                Array.append [|Func' (v, args, iop)|] (args |> Array.map run |> Array.concat)
            | _ -> failwith "oups"
        | None when name.StartsWith("x") -> [||]
        | None -> failwithf "not found %s" name
    run (getVarBoolExpr' exprs.[0]) |> Array.distinct




let f : int -> bool = isPowerOfTwo

let values = 
    [|0 .. final - 1|]
    |> Array.filter f


//let (_, _,  _, _, _, _, _, falseExpr) = run numOfVars (getOpStruct ()) (fun _ -> false) 3 1 1 (fun () -> [|0 .. final - 1|])

//let opStruct = updateOps [|falseExpr|] (getOpStruct ())
let opStruct = (getOpStruct ())


//setTimeout(120.0)
//let _ = run' numOfVars opStruct isPowerOfTwo 20 1 [|0 .. final - 1|] 


let exprs = 
    values
    |> Array.mapi (fun i n -> 
            let (_, _,  _, _, _, _, _, expr') = run numOfVars opStruct (equalTo n) 3 1 1 (fun () -> getSample f [|0 .. final - 1|] final)
            //let (result, expr') = run' numOfVars opStruct (equalTo n) 3 1 [|0 .. final - 1|]
            expr')

let expr =
    Array.reduce (fun (expr : BoolExpr' []) (expr' : BoolExpr' []) ->  
                    Array.append 
                        [|Or'(string (FreshVar ()), getVarBoolExpr' expr.[0], getVarBoolExpr' expr'.[0])|]
                        (Array.append expr expr')) exprs

expr.Length


verify numOfVars (fun i -> values |> Array.exists (fun j -> j = i))
                 (fun i -> let g = eval' [||] expr in g (toBits' numOfVars i))

let rec rndShuffle : int -> int -> BoolExpr' [] -> seq<BoolExpr' []> = fun numOfVars n expr ->
    seq {
        setTimeout(20.0)
        if n = 0 then 
            yield expr
        else
            printfn "rndShuffle n: %d" n
            printfn "rndShuffle expr: %d" expr.Length

            let rndExpr = randomSubExprs [|expr|] 
                          |> Seq.filter (fun expr -> (expr |> getLeafVars |> Array.length) <= numOfVars)
                          |> Seq.filter (fun expr -> expr.Length = 3)
                          |> Seq.head

            let rndExprNumOfVars = rndExpr |> getLeafVars |> Array.length
            let rndFinal = twoPower rndExprNumOfVars
            printfn "rndShuffle rndExpr: %d" rndExpr.Length

            let freshRndExpr = rndExpr |> updateVars
            //let (result, _,  _, _, _, _, _, newExpr) = 
            //    run rndExprNumOfVars opStruct (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) 5 1 1 (fun () -> [|0 .. rndFinal - 1|] |> randomize)
            let (result, newExpr) = 
                run' rndExprNumOfVars opStruct (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) rndExpr.Length [|0 .. rndFinal - 1|]
            
            if result <> rndFinal then
                failwithf "rndShuffle %d - %d" result rndFinal
            else
                let _ = 
                    verify numOfVars (fun i -> let g = eval' [||] freshRndExpr in g (toBits' rndExprNumOfVars i))
                                     (fun i -> let g = eval' [||] newExpr in g (toBits' rndExprNumOfVars i))

                printfn "rndShuffle newExpr: %d" newExpr.Length

                if newExpr.Length > rndExpr.Length then
                    yield! rndShuffle numOfVars (n - 1) expr
                else
                    let subsNewExpr = subs (rndExpr |> getLeafVars) newExpr
                    let expr' = cleanupBoolExpr' (replaceBoolExpr' (getVarBoolExpr' rndExpr.[0]) subsNewExpr expr)

                    let _ =
                        verify numOfVars (fun i -> let g = eval' [||] expr  in g (toBits' numOfVars i))
                                         (fun i -> let g = eval' [||] expr' in g (toBits' numOfVars i))

                    printfn "rndShuffle expr': %d" expr'.Length

                    if expr'.Length <= expr.Length then
                        yield! rndShuffle numOfVars (n - 1) expr'
                    else
                        yield! rndShuffle numOfVars (n - 1) expr
    }


let rec minimize : int -> int -> BoolExpr' [] -> seq<BoolExpr' []> = fun numOfVars n expr ->
    seq {
        setTimeout(20.0)
        if n = 0 then 
            yield expr
        else
            printfn "n: %d" n
            printfn "expr: %d" expr.Length

            let rndExpr = randomSubExprs [|expr|] 
                          |> Seq.filter (fun expr -> (expr |> getLeafVars |> Array.length) <= numOfVars)
                          //|> Seq.filter (fun expr -> expr.Length <= 4)
                          //|> take' 1000
                          //|> Seq.sortBy (fun expr -> (-expr.Length, (expr |> getLeafVars |> Array.length)))
                          |> Seq.head

            let rndExprNumOfVars = rndExpr |> getLeafVars |> Array.length
            let rndFinal = twoPower rndExprNumOfVars
            printfn "rndExpr vars: %d" rndExprNumOfVars
            printfn "rndExpr vars: %A" (rndExpr |> getLeafVars)
            printfn "rndExpr: %d" rndExpr.Length
            yield expr

            let freshRndExpr = rndExpr |> updateVars
            printfn "freshRndExpr: %A" freshRndExpr
            //let (result, _,  _, _, _, _, _, newExpr) = 
            //    run rndExprNumOfVars opStruct (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) 5 1 1 (fun () -> [|0 .. rndFinal - 1|] |> randomize)
            let (result, newExpr) = 
                run' rndExprNumOfVars opStruct (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) rndExpr.Length [|0 .. rndFinal - 1|]
            
            if result <> rndFinal then
                printfn "%d - %d" result rndFinal
                yield! minimize numOfVars (n - 1) expr
            else
                let _ = 
                    verify numOfVars (fun i -> let g = eval' [||] freshRndExpr in g (toBits' rndExprNumOfVars i))
                                     (fun i -> let g = eval' [||] newExpr in g (toBits' rndExprNumOfVars i))

                printfn "newExpr: %d" newExpr.Length
                printfn "newExpr: %A" newExpr
                yield expr

                if newExpr.Length > rndExpr.Length then
                    yield! minimize numOfVars (n - 1) expr
                else
                    let subsNewExpr = subs (rndExpr |> getLeafVars) newExpr
                    let expr' = cleanupBoolExpr' (replaceBoolExpr' (getVarBoolExpr' rndExpr.[0]) subsNewExpr expr)

                    let _ =
                        verify numOfVars (fun i -> let g = eval' [||] expr  in g (toBits' numOfVars i))
                                         (fun i -> let g = eval' [||] expr' in g (toBits' numOfVars i))

                    printfn "expr': %d" expr'.Length

                    yield expr

                    if expr'.Length <= expr.Length then
                        yield! minimize numOfVars (n - 1) expr'
                    else
                        yield! minimize numOfVars (n - 1) expr
    }

let expr' = rndShuffle numOfVars 200 expr |> Seq.last

let enum = (minimize numOfVars 200 expr').GetEnumerator()

enum.MoveNext()

while enum.MoveNext() do
    ()




writeTruthTable @"c:\downloads\tt.csv" numOfVars [|0 .. final - 1|] isPowerOfTwo


//setTimeout(120.0)
//let (_, _,  _, _, _, _, _, expr'') = run numOfVars opStruct isPowerOfTwo 20 23 1 (fun () -> [|0 .. final - 1|])

