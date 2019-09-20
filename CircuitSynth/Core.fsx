
#load "Init.fsx"
#load "Utils.fsx"
#load "CoreTypes.fsx"

open System
open System.Diagnostics
open System.Collections.Generic
open System.IO
open Microsoft.Z3
open Utils
open Init
open CoreTypes



let toBits : int -> int -> BoolExpr [] =
    fun bitSize i ->
        [| for c in Convert.ToString(i, 2).PadLeft(bitSize, '0') -> if c = '1' then True else False |]

let toBits' : int -> int -> bool [] =
    fun bitSize i ->
        [| for c in Convert.ToString(i, 2).PadLeft(bitSize, '0') -> if c = '1' then true else false |]


let toInt : Model -> BoolExpr [] -> int = 
    fun model bits ->
        Convert.ToInt32([| for bit in bits do
                                yield if string <| model.Evaluate(bit) = "true" then "1" else "0"|] |> String.concat "", 2)

let toBool : Model -> BoolExpr -> bool = 
    fun model bit ->
        if string <| model.Evaluate(bit) = "true" then true else false

let createVars : int -> int -> Vars = 
    fun bitSize numOfVars -> 
        [| for i in [|0..numOfVars - 1|] do
                yield { Pos = toBits bitSize i; Value = FreshVar () } |]

let lookupVarValue : BoolExpr -> BoolExpr [] -> Vars -> BoolExpr = 
    fun var varPos vars -> 
        (vars, False) ||> Array.foldBack (fun entry s -> If (Eq entry.Pos varPos) (Eq [|var|] [|entry.Value|]) s)  

let lookupInstrValue : BoolExpr -> BoolExpr [] -> Instrs -> BoolExpr = 
    fun value instrPos instrs -> 
        (instrs, False) ||> Array.foldBack (fun instr s -> If (Eq instr.Pos instrPos) (Eq [|value|] [|instr.Value|]) s) 


let createInstrs : int -> int -> int -> int -> int [] -> int -> Instrs = 
    fun numOfVars varBitSize instrBitSize opBitSize arityOfOps numOfInstrs ->
        let numOfArgs = if numOfVars < 2 then 2 else numOfVars
        [| for i in [|0..numOfInstrs - 1|] do
                yield { Pos = toBits instrBitSize i; Value = FreshVar (); Op = VarPos opBitSize (sprintf "OpVar-%d" i)
                        Args = [|0..numOfArgs - 1|] 
                               |> Array.map (fun argIndex -> { IsVar = Var (sprintf "IsVar-%d-%d" i argIndex); 
                                                               VarPos = VarPos varBitSize (sprintf "VarPos-%d-%d" i argIndex); 
                                                               InstrPos = VarPos instrBitSize (sprintf "InstrPos-%d-%d" i argIndex) } ) } |]

                    
let checkInstrs : int [] -> int [] -> int -> Vars -> Instrs -> BoolExpr = 
    fun availableOpExprs arityOfOps numOfOps vars instrs -> 
        let rec check : Instr list -> Instr list -> BoolExpr = fun acc instrs -> 
            match instrs with
            | [] -> True
            | instr :: instrs ->
                let opBitSize = instr.Op.Length
                let checkArity = if acc.Length = 0 then True
                                 else
                                    [| for instr' in acc do
                                        for i in [|0..numOfOps - 1|] do
                                            let arityChecks = instr'.Args 
                                                              |> Array.take arityOfOps.[availableOpExprs.[i]] 
                                                              |> Array.map (fun arg -> And [|Not arg.IsVar; Eq arg.InstrPos instr.Pos|])
                                                              |> Or
                                            yield If (Eq instr'.Op (toBits opBitSize availableOpExprs.[i])) arityChecks False 
                                    |]
                                    |> Or
                let checkOpVar = (False, [|0..numOfOps - 1|]) ||> Array.fold (fun s i -> Or [|Eq instr.Op (toBits opBitSize availableOpExprs.[i]); s|])
                let checkVars = instr.Args |> Array.map (fun arg -> (False, vars) ||> Array.fold (fun s entry -> Or [|Eq arg.VarPos entry.Pos; s|])) 
                let checkInstrs = instr.Args |> Array.map (fun arg -> (False, [| for instr in instrs -> instr.Pos |]) ||> Array.fold (fun s bits -> Or [|Eq arg.InstrPos bits; s|])) 
                let combineChecks = (instr.Args, checkVars, checkInstrs) |||> Array.zip3 |> Array.map (fun (arg, checkVar, checkInstr) -> If arg.IsVar checkVar checkInstr) |> And
                And [| checkArity;
                       checkOpVar;
                       combineChecks;
                       check (instr :: acc) instrs |]
        check [] <| Array.toList instrs

let evalInstrs : int [] -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> Vars -> Instrs -> BoolExpr = fun availableOpExprs ops vars instrs ->
    And [| for instr in instrs do
                let opBitSize = instr.Op.Length
                let freshVars = instr.Args |> Array.map (fun _ -> FreshVar ())
                let args = (freshVars, instr.Args) 
                           ||> Array.zip 
                           |> Array.map (fun (freshVar, arg) -> If arg.IsVar (lookupVarValue freshVar arg.VarPos vars)
                                                                             (lookupInstrValue freshVar arg.InstrPos instrs))
                let resultVars = ops |> Array.map (fun _ -> FreshVar ())
                let resultOps = availableOpExprs |> Array.map (fun i -> ops.[i] resultVars.[i] freshVars)
                let value =
                    availableOpExprs 
                    |> Array.map (fun i -> If (Eq instr.Op (toBits opBitSize i)) resultVars.[i] False)
                    |> Or

                yield And [|And resultOps; Eq [|instr.Value|] [|value|]; And args |] |]

let rec simplify : BoolExpr -> BoolExpr = fun expr ->
    let goal = ctx.MkGoal()
    goal.Add(expr)
    let applyResult = ctx.MkTactic("ctx-solver-simplify").Apply(goal)
    let expr' = 
        if applyResult.Subgoals.[0].Formulas.Length = 0 then
            expr
        else if applyResult.Subgoals.[0].Formulas.Length = 1 then
            applyResult.Subgoals.[0].Formulas.[0]
        else 
            applyResult.Subgoals.[0].Formulas |> Array.reduce (fun left right -> And [|left; right|])
    expr'

let equiv' : BoolExpr [] -> (BoolExpr -> BoolExpr [] -> BoolExpr) -> (BoolExpr -> BoolExpr [] -> BoolExpr) -> bool = 
    fun freshVars f g ->
        let solver = ctx.MkSolver("QF_FD")
        let res = Var "res"
        let res' = Var "res'"
        let test = Not <| Eq [|res|] [|res'|] 
        solver.Assert(f res freshVars)
        solver.Assert(g res' freshVars)
        solver.Assert(test)
        //printfn "%s" <| solver.ToString()
        match solver.Check() with
        | Status.UNSATISFIABLE -> true 
        | Status.SATISFIABLE -> false
        | _-> failwith "UNKNOWN"

let equivs : BoolExpr [] -> BoolExpr [] -> BoolExpr [] -> bool [] = 
    fun freshVars fs gs ->
        let solver = ctx.MkSolver("UFBV")

        let asserts : (BoolExpr * BoolExpr) [] = 
            [| for (f, g) in (fs, gs) ||> Array.zip do
                let var = FreshVar ()
                yield (var, Eq [|var|] [|ctx.MkForall(freshVars |> Array.map (fun expr -> expr :> _), Eq [|f|] [|g|]) :> BoolExpr|])
            |]
        asserts |> Seq.iter (fun (_, assert') -> solver.Assert(assert'))
        //printfn "%s" <| solver.ToString()
        match solver.Check() with
        | Status.SATISFIABLE -> asserts |> Array.map (fun (var,_ ) -> toBool solver.Model var)
        | Status.UNSATISFIABLE -> [||]
        | _-> failwith "UNKNOWN"

let toInstrs' : Model -> Instrs -> Instrs' = fun model instrs ->
    [| for instr in instrs do
            yield { Pos = toInt model instr.Pos; Op = toInt model instr.Op;
                    Args = instr.Args |> Array.map (fun arg -> { IsVar = toBool model arg.IsVar;
                                                                 VarPos = toInt model arg.VarPos;
                                                                 InstrPos = toInt model arg.InstrPos }) } |]


let strInstrs : (string [] -> string) [] -> int [] -> Instrs' -> string = fun ops args instrs ->
    let instrs = Array.rev instrs
    [| for instr  in instrs do 
            let args = instr.Args |> Array.take args.[instr.Op] |> Array.map (fun arg -> if arg.IsVar then "var-" + arg.VarPos.ToString() else "temp-" + arg.InstrPos.ToString())
            let value = ops.[instr.Op] args
            yield sprintf "temp-%d = %s" instr.Pos value |] |> String.concat "\n"
    

let evalInstrs' : (bool [] -> bool) [] -> Instrs' -> bool[] -> bool = fun ops instrs vars ->
    let rec eval : int -> bool = fun i -> 
            let instr = instrs.[i]
            let args = instr.Args |> Array.map (fun arg -> if arg.IsVar then vars.[arg.VarPos] else eval arg.InstrPos)
            ops.[instr.Op] args
    eval 0

let (|And1|_|) : BoolExpr ->  BoolExpr option = fun expr ->
    match expr with
    | _ when expr.IsAnd && expr.NumArgs = 1u -> Some (expr.Args.[0] :?> _)
    | _ -> None

let (|And|_|) : BoolExpr -> (BoolExpr * BoolExpr) option = fun expr ->
    match expr with
    | _ when expr.IsAnd && expr.NumArgs = 2u -> Some (expr.Args.[0] :?> _, expr.Args.[1] :?> _)
    | _ -> None

let (|AndStar|_|) : BoolExpr -> BoolExpr [] option = fun expr ->
    match expr with
    | _ when expr.IsAnd -> Some (expr.Args |> Array.map (fun expr -> expr :?> _))
    | _ -> None

let (|Or|_|) : BoolExpr -> (BoolExpr * BoolExpr) option = fun expr ->
    match expr with
    | _ when expr.IsOr && expr.NumArgs = 2u -> Some (expr.Args.[0] :?> _, expr.Args.[1] :?> _)
    | _ -> None

let (|Not|_|) : BoolExpr -> BoolExpr option = fun expr ->
    match expr with
    | _ when expr.IsNot && expr.NumArgs = 1u -> Some (expr.Args.[0] :?> _)
    | _ -> None

let (|Var|_|) : BoolExpr -> string option = fun expr ->
    match expr with
    | _ when expr.IsBool && expr.IsConst -> Some (string expr)
    | _ -> None

let (|Eq|_|) : BoolExpr -> (BoolExpr * BoolExpr) option = fun expr ->
    match expr with
    | _ when expr.IsEq -> Some (expr.Args.[0] :?> _, expr.Args.[1] :?> _)
    | _ -> None

let rec countOps : BoolExpr -> int = fun expr ->
    match expr with
    | Eq (Var _, And (Var _, Var _)) -> 1
    | Eq (Var _, Or (Var _, Var _)) -> 1
    | Eq (Var _, Not (Var _)) -> 1
    | Eq (Var _, Var _) -> 0
    | And1 x -> countOps x
    | And (x, y) | Or (x, y) -> countOps x  + countOps y 
    | AndStar xs -> xs |> Array.map countOps |> Array.sum
    | Not x  -> countOps x 
    | Var _ -> 0
    | _ -> failwithf "oups %A - %d" expr expr.NumArgs

        
let compileInstrs' : (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> int [] -> Instrs' -> (BoolExpr -> BoolExpr [] -> BoolExpr) = 
    fun opExprs args instrs resultVar vars -> 
        let resultVars = instrs |> Array.map (fun _ -> FreshVar ())
        let rec compile : int -> BoolExpr -> BoolExpr = fun i resultVar -> 
            let instr = instrs.[i]
            let argVars = instr.Args |> Array.take args.[instr.Op] |> Array.map (fun _ -> FreshVar ())
            let args = instr.Args |> Array.take args.[instr.Op] |> Array.mapi (fun i arg -> if arg.IsVar then Eq [|argVars.[i]|] [|vars.[arg.VarPos]|] else Eq [|argVars.[i]|] [|resultVars.[arg.InstrPos]|])
            And [|opExprs.[instr.Op] resultVar argVars; And args|]
        let exprs = resultVars |> Array.mapi (fun i resultVar -> compile i resultVar)
        And <| Array.append [|Eq [|resultVar|] [|resultVars.[0]|]|] exprs
        
    
let toVars' : Model -> Vars -> bool[] = fun model vars ->
    [| for entry in vars do 
            yield toBool model entry.Value |]
            

let writeTruthTable : string -> int -> int [] -> (int -> bool) -> unit = 
    fun fileName bitSize data f ->
    let vars = [|1..bitSize|] |> Array.map (fun i -> string i + "x") |> String.concat ","
    let header = sprintf "%s,,F0" vars
    use writer = File.CreateText(fileName)
    printfn "%s" header
    writer.WriteLine(header)
    for i in data do
        let bits = toBits' bitSize i 
        let bits = bits |> Array.map (fun bit -> if bit then "1" else "0") |> String.concat ","
        let row = sprintf "%s,,%s" bits (if f i then "1" else "0")
        printfn "%s" row
        writer.WriteLine(row)
    ()

let toFuncBoolExpr : int -> int [] -> (int -> bool) -> (BoolExpr[] -> BoolExpr) =
    fun bitSize data f vars -> 
        data
        |> Array.filter f
        |> Array.map (fun i -> toBits' bitSize i 
                               |> Array.mapi (fun i bit -> if bit then vars.[i] else Not vars.[i])
                               |> Array.reduce (fun x y -> And [|x; y|]))
        |> Array.reduce (fun x y -> Or [|x; y|])

let verify : int -> (int -> bool) -> (int -> bool) -> int = fun numOfVars f g ->
    let final = int (2.0 ** (float numOfVars))
    let result =
        [|0..(final - 1)|] 
        |> Array.filter (fun i -> f i = g i)
        |> Array.length
    if final = result then
        result
    else failwithf "%d - %d" final result



let freshVars numOfVars = [|0..numOfVars - 1|] |> Array.map (fun i -> Var ("x" + string i))
let toOpStr : int -> string [] -> string = fun i args -> sprintf "func%d(%s)" i (String.concat "," args)

let evalQuantifierInstrs : int [] -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> Vars -> Instrs -> BoolExpr -> BoolExpr = 
    fun availableOpExprs ops vars instrs result ->
        let check = 
            And [| for instr in instrs do
                        let opBitSize = instr.Op.Length
                        let freshVars = instr.Args |> Array.map (fun _ -> FreshVar ())
                        let args = (freshVars, instr.Args) 
                                   ||> Array.zip 
                                   |> Array.map (fun (freshVar, arg) -> If arg.IsVar (lookupVarValue freshVar arg.VarPos vars)
                                                                                     (lookupInstrValue freshVar arg.InstrPos instrs))
                        let resultVars = availableOpExprs |> Array.map (fun _ -> FreshVar ())
                        let resultOps = availableOpExprs |> Array.map (fun i -> ops.[i] resultVars.[i] freshVars)
                        let value =
                            availableOpExprs 
                            |> Array.map (fun i -> If (Eq instr.Op (toBits opBitSize i)) resultVars.[i] False)
                            |> Or

                        yield ctx.MkExists(Array.append freshVars resultVars |> Array.map (fun var -> var :> _), And [|And resultOps; Eq [|instr.Value|] [|value|]; And args |]) :> _ |]
        let instrVars = instrs |> Array.map (fun instr -> instr.Value :> Expr)
        ctx.MkExists(instrVars, And [|Eq [|instrs.[0].Value|] [|result|]; check|]) :> _


let find' : int -> Ops -> (int -> bool) -> int [] -> int -> (Status * Instrs') = 
    fun numOfVars opStruct verify testData numOfInstrs ->
        let opExprs = opStruct.OpExprs
        let ops = opStruct.Ops
        let opStrs = opStruct.OpStrs 
        let arityOfOps = opStruct.ArityOps
        let availableOpExprs = 
            opStruct.Active 
            |> Array.mapi (fun i b -> (i, b))
            |> Array.filter (fun (_, b) -> b)
            |> Array.map (fun (i, _) -> i)

        let varBitSize = 8
        let instrBitSize = 8
        let opBitSize = 8
        let numOfOps = availableOpExprs.Length
        let verify' = toFuncBoolExpr numOfVars testData verify
        
        //let t = ctx.MkTactic("qffd")
        let solver = ctx.MkSolver("UFBV")
        let p = ctx.MkParams()
        //solver.Parameters <- p.Add("acce", true).Add("abce", true).Add("cce", true)

        let vars = createVars varBitSize numOfVars
        let freshVars = vars |> Array.map (fun var -> var.Value)
        let instrs = createInstrs numOfVars varBitSize instrBitSize opBitSize arityOfOps numOfInstrs
        let check = checkInstrs availableOpExprs arityOfOps numOfOps vars instrs
        let eval = evalQuantifierInstrs availableOpExprs opExprs vars instrs (verify' freshVars)
        
        solver.Assert(ctx.MkForall(freshVars |> Array.map (fun var -> var :> _), 
                                   And [|eval; check|]))
                                   
        let status = solver.Check() 
        if not (status = Status.SATISFIABLE) then
            (status, null)
        else
            let model = solver.Model
            let instrs' = toInstrs' model instrs

            //printfn "%s" (strInstrs opStrs arityOfOps instrs')
            let flag = 
                testData 
                |> Array.map (fun i -> verify i = evalInstrs' ops instrs' (toBits' numOfVars i) )
                |> Array.reduce (&&)
            if not flag then
                Printf.failwithf "Invalid Instrs %s" (strInstrs opStrs arityOfOps instrs')

            (status, instrs')


let find : int -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> 
           (bool [] -> bool) [] ->
           (string [] -> string) [] ->
           int [] ->
           (int -> bool) ->
           int [] -> int [] -> int [] -> int -> Instrs' -> (Status * int * Instrs') = 
    fun numOfVars opExprs ops opStrs availableOpExprs verify sample test arityOfOps numOfInstrs fixedInstrs ->
        let varBitSize = 5
        let instrBitSize = 8
        let opBitSize = 5
        let numOfOps = availableOpExprs.Length

        //let t = ctx.MkTactic("qffd")
        let solver = ctx.MkSolver("QF_FD")
        let p = ctx.MkParams()
        //solver.Parameters <- p.Add("acce", true).Add("abce", true).Add("cce", true)

        for i in sample do
            let vars = createVars varBitSize numOfVars
            let instrs = createInstrs numOfVars varBitSize instrBitSize opBitSize arityOfOps numOfInstrs

            let eval = evalInstrs availableOpExprs opExprs vars instrs

            let bits = toBits' numOfVars i
            let freshVars = [|0..numOfVars - 1|] |> Array.map (fun _ -> FreshVar ())
            let inputVarCheck = freshVars |> Array.mapi (fun i var -> And [| lookupVarValue var (toBits varBitSize i) vars; Eq [|var|] [|Val bits.[i]|]|])

            let test = Eq [|instrs.[0].Value|] [|Val (verify i)|]
            solver.Assert(And [|eval; And inputVarCheck; test|])    

        let vars = createVars varBitSize numOfVars
        let instrs = createInstrs numOfVars varBitSize instrBitSize opBitSize arityOfOps numOfInstrs
        let check = checkInstrs availableOpExprs arityOfOps numOfOps vars instrs
        solver.Assert(check)
        
        for fixedInstr in fixedInstrs do
            let fixedOp = Eq (VarPos opBitSize (sprintf "OpVar-%d" fixedInstr.Pos)) (toBits opBitSize fixedInstr.Op)
            for (argIndex, fixedArg) in fixedInstr.Args |> Array.mapi (fun i arg -> (i, arg)) do

                if not fixedArg.IsVar then
                    let isVar = if fixedArg.IsVar then True else False
                    let fixedIsVar = Eq [|Var (sprintf "IsVar-%d-%d" fixedInstr.Pos argIndex)|] [|isVar|]
                    let fixedVarPos = Eq (VarPos varBitSize (sprintf "VarPos-%d-%d" fixedInstr.Pos argIndex)) (toBits varBitSize fixedArg.VarPos)
                    let fixedInstrPos = Eq (VarPos instrBitSize (sprintf "InstrPos-%d-%d" fixedInstr.Pos argIndex)) (toBits instrBitSize fixedArg.InstrPos)

                    solver.Assert(fixedIsVar)
                    solver.Assert(fixedVarPos)
                    solver.Assert(fixedInstrPos)
                ()
            solver.Assert(fixedOp)
            ()

        //printfn "Cubes: %d" <| (solver.Cube() |> Seq.length)
        //File.WriteAllText("dump.txt", solver.ToString())
        let status = solver.Check() 
        if not (status = Status.SATISFIABLE) then
            (status, -1, null)
        else
            let model = solver.Model
            let instrs' = toInstrs' model instrs
            
            let flag = 
                sample 
                |> Array.map (fun i -> verify i = evalInstrs' ops instrs' (toBits' numOfVars i) )
                |> Array.reduce (&&)
            if not flag then
                Printf.failwithf "Invalid Instrs %s" (strInstrs opStrs arityOfOps instrs')

            let result = 
                test 
                |> Array.filter (fun i -> verify i = evalInstrs' ops instrs' (toBits' numOfVars i) )
                |> Array.length
            (status, result, instrs')

let compileInstrsToBoolExprs : int [] -> Instrs' -> BoolExpr' [] = fun args instrs ->
    let dict = new Dictionary<string, string>()
    let g : string -> string = fun v -> if not <| dict.ContainsKey(v) then 
                                            let fresh = string (FreshVar ())
                                            dict.Add(v, fresh)
                                            fresh
                                          else dict.[v]
    let f : Arg' -> string = fun arg -> 
        if arg.IsVar then "x" + arg.VarPos.ToString() 
        else g ("temp-" + arg.InstrPos.ToString())
    [| for instr in instrs do 
            yield
                match instr.Op with
                | 0 -> Or' (g (sprintf "temp-%d" instr.Pos), f instr.Args.[0], f instr.Args.[1])
                | 1 -> And' (g (sprintf "temp-%d" instr.Pos), f instr.Args.[0], f instr.Args.[1])
                | 2 -> Not' (g (sprintf "temp-%d" instr.Pos), f instr.Args.[0])
                | _ -> Func' (g (sprintf "temp-%d" instr.Pos), instr.Args |> Array.take args.[instr.Op] |> Array.map f, instr.Op) |] 


let rec run : int -> Ops -> (int -> bool) -> Instrs' -> int -> int -> int -> (unit -> int []) -> 
              (int * int * (int -> bool) * (bool[] -> bool) * (string [] -> string) * 
               (BoolExpr -> BoolExpr [] -> BoolExpr) * Instrs' * BoolExpr' []) = 
    fun numOfVars opStruct verify fixedInstrs numOfTries numOfInstrsIndex pos baseSample ->
        let final = int (2.0 ** (float numOfVars))
        let values = [|0..final - 1|]
        let stats = Array.init final (fun i ->  0)
        let opExprs = opStruct.OpExprs
        let opStrs = opStruct.OpStrs
        let ops = opStruct.Ops
        let arityOfOps = opStruct.ArityOps
        let numOfOps = opStruct.OpExprs.Length
        let baseSample = baseSample ()
        let posRef = ref pos
        let notFound = ref [||]


        let rec run' : int -> (Status * int * Instrs' * TimeSpan) [] -> (Status * int * Instrs' * TimeSpan * int []) = 
            fun numOfInstrsIndex old ->
                let notFound = if old.Length <> 0 then
                                    let (_, _, instrs', _) = old.[0]
                                    let f = evalInstrs' ops instrs'
                                    [|0..final - 1|] |> Array.filter (fun i -> f <| toBits' numOfVars i <> verify i)
                                else [||]
                printfn "notFound: %A" notFound
                for i in notFound do
                    stats.[i] <- stats.[i] + 1
                let sample = (baseSample, stats) ||> Array.zip |> Array.map (fun (i, c)  -> (i, c)) |> Array.sortBy (fun (i, c) -> -c) |> Array.map fst
                //let sample = getSample verify sample numOfSamples
                //let sample = baseSample//Array.append notFound baseSample |> Array.distinct
                let sample = getSample verify sample final |> Seq.take !posRef |> Seq.toArray 
                //printfn "Sample: %A" sample
                if sample.Length <> (sample |> Array.distinct |> Array.length) then
                    failwithf "Duplicate elements - base %A - sample %A " baseSample sample


                
                let result =
                    seq {
                        for numOfInstrs in {numOfInstrsIndex..100} do
                            let availableOpExprs = 
                                opStruct.Active 
                                |> Array.mapi (fun i b -> (i, b))
                                |> Array.filter (fun (_, b) -> b)
                                |> Array.map (fun (i, _) -> i)

                            let watch = new Stopwatch()
                            watch.Start()
                            let (status, result, instrs') = find numOfVars opExprs ops opStrs availableOpExprs verify sample [|0..final - 1|] arityOfOps numOfInstrs fixedInstrs 
                            watch.Stop()
                            printfn "%d %d %A %A %A" sample.Length numOfInstrs availableOpExprs (status, result) watch.Elapsed
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
                    //printfn "%s" <| strInstrs opStrs arityOfOps instrs'
                    incr posRef
                    run' numOfInstrs (Array.append [|(Status.SATISFIABLE, result, instrs', elapsed)|] old)
                | None ->
                    if old.Length = 0 then failwith "UNKNOWN"
                    let (status, result, instrs', elapsed) = old.[0]
                    //printfn "%s" <| strInstrs opStrs arityOfOps instrs'
                    (status, result, instrs', elapsed, sample)
                | _ -> failwith "oups"
        let (status, result, instrs', elapsed, sample) = run' numOfInstrsIndex [||]
        printfn "%A %A" (status, result) elapsed

        let opExpr = compileInstrs' opExprs arityOfOps instrs' 
        let expr' = compileInstrsToBoolExprs arityOfOps instrs'
        let ops = evalInstrs' ops instrs'
        let opStr = toOpStr numOfVars
        let arityOfOp = numOfVars
        let stats' = stats |> Array.mapi (fun i c -> (i, c)) |> Array.sortBy snd

        (result, !posRef, (fun i -> ops (toBits' numOfVars i)), ops, opStr, opExpr, instrs', expr')


let run' : int -> Ops -> (int -> bool) -> int -> int [] -> (int * BoolExpr' []) = 
    fun numOfVars opStruct verify numOfInstrs testData ->
        let availableOpExprs = 
                opStruct.Active 
                |> Array.mapi (fun i b -> (i, b))
                |> Array.filter (fun (_, b) -> b)
                |> Array.map (fun (i, _) -> i)
        let rec run'' : int -> (int * BoolExpr' []) = fun numOfInstrsIndex -> 
            let watch = new Stopwatch()
            watch.Start()
            let (status, instrs') = find' numOfVars opStruct verify testData numOfInstrsIndex
            watch.Stop()
            printfn "%d %A %A %A" numOfInstrsIndex availableOpExprs status watch.Elapsed
            match status with
            | Status.SATISFIABLE -> 
                let expr' = compileInstrsToBoolExprs opStruct.ArityOps instrs'
                (testData.Length, expr')
            | Status.UNSATISFIABLE -> 
                run'' (numOfInstrsIndex + 1) 
            | Status.UNKNOWN when numOfInstrsIndex = numOfInstrs -> 
                (0, [||])
            | Status.UNKNOWN -> 
                run'' (numOfInstrsIndex + 1) 
            | _ -> failwith "oups"
        run'' 1