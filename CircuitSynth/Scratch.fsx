//#I "/Users/nickpalladinos/Projects/CircuitSynth/CircuitSynth"
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
                   2;
                 |]
let ops : (bool [] -> bool) [] = 
    [|(fun args -> args.[0] || args.[1]);
      (fun args -> args.[0] && args.[1]);
      (fun args -> not args.[0]);
      (fun args -> not (args.[0] || args.[1]))
    |]

let opExprs : (BoolExpr -> BoolExpr [] -> BoolExpr) [] = 
    [|(fun var args -> Eq [|var|] [|Or [|args.[0]; args.[1]|]|]);
      (fun var args -> Eq [|var|] [|And [|args.[0]; args.[1]|]|]);
      (fun var args -> Eq [|var|] [|Not args.[0]|]);
      (fun var args -> Eq [|var|] [|Not <| Or [|args.[0]; args.[1]|]|]);
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
      (fun args -> sprintf "%s nor %s" args.[0] args.[1])
    |]

let getOpStruct : unit -> Ops = fun () -> { OpExprs = opExprs; 
                                            Ops = ops;
                                            OpStrs = opStrs; 
                                            OpExprs' = opExprs';
                                            ArityOps = arityOfOps;
                                            Active = [|true; true; true; true|]  }


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
        let complRootExprs = exprs |> Array.filter (fun e -> not <| Array.contains e rootExprs)
        let rec rndBoolExpr' : string -> seq<BoolExpr'> = 
            fun name ->
                match Array.tryFind (fun (key, _) -> key = name) lookupMap with
                | None -> Seq.empty
                | Some (_, expr) ->
                    match expr with
                    | And' (v, x, y) | Or' (v, x, y) as expr -> 
                        seq { yield expr; yield! [|x; y|] 
                                                 |> randomize
                                                 |> Seq.filter (fun v -> if v.StartsWith("x") then true else countRefs v complRootExprs = 0)
                                                 |> Seq.map rndBoolExpr' 
                                                 |> merge' } 
                    | Not' (v, x) as expr -> 
                        seq { yield expr; yield! [|x|] 
                                                 |> Seq.filter (fun v -> if v.StartsWith("x") then true else countRefs v complRootExprs = 0)
                                                 |> Seq.collect rndBoolExpr'  } 
                    | Var' (v, x) as expr -> failwith "oups"
                    | Func' (v, args, iops) ->
                        seq { yield expr; yield! args |> randomize |> Seq.map rndBoolExpr' |> merge' } 
        rndBoolExpr' (getVarBoolExpr' rootExpr) 

let baseSample : (int -> bool) -> unit -> int [] = fun f () -> 
    let sample = randoms 0 (final - 1) |> Seq.distinct |> Seq.take final |> Seq.toArray
    getSample f sample final

let population : int -> (int -> bool) -> Ops -> (unit -> int[]) -> (int * Instrs' * BoolExpr' []) [] = fun n f opStruct samplef -> 
    [| for i = 1 to n do 
        let (result, pos, f, op, opStr, opExpr, instrs', expr) = run numOfVars opStruct f [||] 3 1 numOfSamples 30 samplef
        yield (result, instrs', expr) |]

let ranges : int -> (int -> bool) -> Ops -> Instrs' -> seq<Instrs' * BoolExpr' []> = fun takeN f opStruct fixedInstrs -> 
    seq {
        
        let values = 
            [|0 .. final - 1|]
            |> Array.filter f

        printfn "Values: %A" values
        let posRef = ref 1
        let flag = ref true
        let i = ref 1
        while !flag do
            let skipN = rand.Next(0, values.Length)
            printfn "%d - %d" !i skipN 
            let (result, _, _, _, _, _, instrs', expr) = 
              tryWith (fun () ->  run numOfVars opStruct 
                                        (fun i -> values |> Array.skip skipN |> take' takeN |> Array.ofSeq |> Array.exists (fun j -> j = i)) 
                                        fixedInstrs 3 1 64 30 (fun () -> [|0  .. final - 1|]))
                      (-1, -1, Unchecked.defaultof<_>, Unchecked.defaultof<_>, Unchecked.defaultof<_>, Unchecked.defaultof<_>, [||], [||])
            posRef := expr.Length
            incr i
            if !i > 10 then
                flag := false
            if result = final then
                yield (instrs', expr)
            else
                flag := false
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



let rec exec' : int -> Instrs' -> Instrs' -> (int -> bool) -> Ops -> seq<BoolExpr'[]> = fun i fixedInstrs accInstrs f opStruct -> 
    seq {
        setTimeout(60.0 * float 1)
        
        let data = 
            [|0 .. final - 1|]
            |> Array.filter f
            |> Array.take i
        
        
        printfn "i: %d" i
        printfn "Data: %A" data
        printfn "FixedInstrs length: %A" fixedInstrs.Length
        printfn "AccInstrs length: %A" accInstrs.Length

        yield [||]

        
        let (_, _, _, _, _, _, instrs, expr) = 
            run numOfVars opStruct (fun i -> data |> Array.exists (fun j -> j = i))
                                   fixedInstrs 1 1 1 100 (fun () -> [|0 .. final - 1|]) 
        //let (_, instrs, expr) = 
        //    run' numOfVars opStruct (fun i -> data |> Array.exists (fun j -> j = i)) 1 [|0 .. final - 1|] fixedInstrs
        //let (_, _, _, _, _, _, instrs, _) = 
        //    run numOfVars opStruct (fun i -> data |> Array.exists (fun j -> j = i))
        //                           accInstrs 1 1 1 100 (fun () -> [|0 .. final - 1|]) 

        yield [||]

        if instrs.Length = 0 then
            yield! exec' i accInstrs accInstrs f opStruct 
        else 
            if i <> ([|0 .. final - 1|] |> Array.filter f |> Array.length) then
                yield! exec' (i + 1) fixedInstrs instrs f opStruct 
    }


let rec exec : int -> Instrs' -> Instrs' -> (int -> bool) -> int[] -> Ops -> seq<BoolExpr'[]> = fun i fixedInstrs accInstrs f data opStruct -> 
    seq {
        setTimeout(60.0 * float 1)
        
        let values = 
            [|0 .. final - 1|]
            |> Array.filter f
            |> Array.filter (fun i -> not <| Array.contains i data)
        
        
        printfn "i: %d" i
        printfn "Data: %A" data
        printfn "Values: %A" values
        printfn "FixedInstrs length: %A" fixedInstrs.Length
        printfn "AccInstrs length: %A" accInstrs.Length

        yield [||]

        let mutable minV = 0
        let mutable minInstrs = [||]
        let mutable min = 100
        let vs = new ResizeArray<int * int>()
        for v in values do
            //let (_, instrs, _) = run' numOfVars opStruct (fun i -> Array.append [|v|] data |> Array.exists (fun j -> j = i)) min [|0 .. final - 1|] fixedInstrs
            let (_, _, _, _, _, _, instrs, _) = run numOfVars opStruct (fun i -> Array.append [|v|] data |> Array.exists (fun j -> j = i)) fixedInstrs 1 1 1 (min - 1) (fun () -> [|0 .. final - 1|])
            if instrs.Length <> 0 then
                vs.Add((v, instrs.Length))
                if instrs.Length < min then
                    minV <- v
                    minInstrs <- instrs
                    min <- instrs.Length

        for (v, c) in vs do
            printfn "%d - %d" v c

        //let (_, _, _, _, _, _, instrs, expr) = 
        //    run numOfVars opStruct (fun i -> data |> Array.exists (fun j -> j = i))
        //                           fixedInstrs 1 1 1 100 (fun () -> [|0 .. final - 1|]) 
        //let (_, instrs, expr) = 
        //    run' numOfVars opStruct (fun i -> data |> Array.exists (fun j -> j = i)) 1 [|0 .. final - 1|] fixedInstrs
        //let (_, _, _, _, _, _, instrs, _) = 
        //    run numOfVars opStruct (fun i -> data |> Array.exists (fun j -> j = i))
        //                           accInstrs 1 1 1 100 (fun () -> [|0 .. final - 1|]) 

        yield [||]

        if minInstrs.Length = 0 then
            yield! exec i accInstrs accInstrs f data opStruct 
        else 
            let data = Array.append [|minV|] data
            if i <> ([|0 .. final - 1|] |> Array.filter f |> Array.length) then
                yield! exec (i + 1) fixedInstrs minInstrs f data opStruct 


    }

let expr = exec' 1 [||] [||] isPrime (getOpStruct ()) |> Seq.last 
expr.Length

let enum = (exec 1 [||] [||] isPowerOfTwo [||] (getOpStruct ())).GetEnumerator()

//for i = 1 to 32 do
enum.MoveNext() |> ignore


setTimeout(20.0)
run' numOfVars (getOpStruct ()) isEven 25 [|0 .. final - 1|] [||]

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




let opStruct = (getOpStruct ())


let rec minimize : int -> int -> BoolExpr' [] -> seq<BoolExpr' []> = fun numOfVars n expr ->
    seq {
        setTimeout(120.0)
        if n = 0 then 
            yield expr
        else
            printfn "n: %d" n
            printfn "expr: %d" expr.Length

            let rndExpr = randomSubExprs [|expr|] 
                          |> Seq.filter (fun expr -> (expr |> getLeafVars |> Array.length) <= numOfVars)
                          //|> Seq.filter (fun expr -> expr.Length < 10)
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
            let (result, _,  _, _, _, _, _, newExpr) = 
                run rndExprNumOfVars opStruct (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) [||] 5 1 1 (rndExpr.Length - 1) (fun () -> [|0 .. rndFinal - 1|])
            //let newExpr = exec 1 [||] [||] (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) opStruct |> Seq.last
            //let (result, newExpr) = 
            //    run' rndExprNumOfVars opStruct (fun i -> eval' [||] freshRndExpr (toBits' rndExprNumOfVars i)) rndExpr.Length [|0 .. rndFinal - 1|]

            if result <> rndFinal then
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


let enum' = minimize numOfVars 200 expr

let enum'' = enum'.GetEnumerator()

for i = 1 to 200 do
    enum''.MoveNext() |> ignore


writeTruthTable @"c:\downloads\tt.csv" 6 [|0 .. (twoPower 6) - 1|] (fun i -> i % 3 = 0)


//setTimeout(120.0)
//let (_, _,  _, _, _, _, _, expr'') = run numOfVars opStruct isPowerOfTwo 20 23 1 (fun () -> [|0 .. final - 1|])

