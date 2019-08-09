
#load "Init.fsx"
#load "Utils.fsx"

open System
open System.IO
open Microsoft.Z3
open Utils
open Init


type VarEntry = { Pos : BoolExpr []; Value : BoolExpr }
type Vars = VarEntry [] 
type Arg = { IsVar : BoolExpr; VarPos : BoolExpr []; InstrPos : BoolExpr [] } 
type Instr = { Pos : BoolExpr []; Value : BoolExpr; Op : BoolExpr [];
               Args : Arg [] }
type Instrs =  Instr []

type Arg' = { IsVar : bool; VarPos : int; InstrPos : int }
type Instr' = { Pos : int; Op : int;
                Args : Arg' [] }
type Instrs' =  Instr' []

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


let createInstrs : int -> int -> int -> int [] -> int -> Instrs = 
    fun varBitSize instrBitSize opBitSize arityOfOps numOfInstrs ->
        let numOfArgs = arityOfOps |> Array.max
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
                let resultVars = availableOpExprs |> Array.map (fun _ -> FreshVar ())
                let resultOps = availableOpExprs |> Array.map (fun i -> ops.[i] resultVars.[i] freshVars)
                let value =
                    availableOpExprs 
                    |> Array.map (fun i -> If (Eq instr.Op (toBits opBitSize i)) resultVars.[i] False)
                    |> Or
                
                yield And [|And resultOps; Eq [|instr.Value|] [|value|]; And args |] |]


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
    [|0..(final - 1)|] 
    |> Array.filter (fun i -> f i = g i)
    |> Array.length



let rec split : int -> seq<int * int> = fun n -> 
    seq { for i in {0..n} -> (i, n - i) }

type BoolExpr' = 
    | And' of string * string * string
    | Or' of string * string * string
    | Not' of string * string
    | Var' of string * string 

let rec toBoolExprs : BoolExpr -> BoolExpr [] = fun expr -> 
    if not expr.IsAnd then [|expr|]
    else
        let notand = 
            expr.Args 
            |> Array.filter (fun expr -> not expr.IsAnd)
            |> Array.map (fun expr -> expr :?> BoolExpr)

        let and' = 
            expr.Args 
            |> Array.filter (fun expr -> expr.IsAnd) 
            |> Array.collect (fun expr -> expr.Args) 
            |> Array.map (fun expr -> expr :?> BoolExpr)
            |> Array.collect toBoolExprs

        Array.append notand and'

let toBoolExpr' : BoolExpr -> BoolExpr' []  = fun expr ->
    let f : BoolExpr -> BoolExpr' = fun expr ->
        match expr with
        | Eq (Var v, And (Var x, Var y)) -> And' (v, x, y)
        | Eq (Var v, Or (Var x, Var y)) -> Or' (v, x, y)
        | Eq (Var v, Not (Var x)) -> Not' (v, x)
        | Eq (Var x, Var y) -> Var' (x, y)
        | _ -> failwithf "oups %A - %d" expr expr.NumArgs

    expr |> toBoolExprs |> Array.map f


let toBoolExpr : BoolExpr' [] -> BoolExpr = fun exprs ->
    exprs |> Array.map (function | And' (v, x, y) -> Eq [|Var v|] [|And [|Var x; Var y|]|]
                                 | Or' (v, x, y) -> Eq [|Var v|] [|Or [|Var x; Var y|]|]
                                 | Not' (v, x) -> Eq [|Var v|] [|Not (Var x)|]
                                 | Var' (v, x) -> Eq [|Var v|] [|(Var x)|]) 
          |> And 
    
let toMapBoolExpr : BoolExpr' [] -> Map<string, BoolExpr'> = fun exprs ->
    exprs |> Array.map (fun expr -> match expr with 
                                     | And' (v, x, y) -> (v, expr)
                                     | Or' (v, x, y) -> (v, expr)
                                     | Not' (v, x) -> (v, expr)
                                     | Var' (v, x) -> (v, expr))
          |> Map.ofArray
          
    

let countOps' : BoolExpr' [] -> int = fun exprs ->
    exprs |> Array.map (function | And' (v, x, y) -> 1
                                 | Or' (v, x, y) -> 1
                                 | Not' (v, x) -> 1
                                 | Var' (v, x) -> 0)
          |> Array.sum

let topVarBoolExpr' : BoolExpr' [] -> string = fun exprs ->
    match exprs |> Array.head with 
    | And' (v, x, y) | Or' (v, x, y) -> v 
    | Not' (v, x) | Var' (v, x) -> v

let eval' : (string * bool) [] -> BoolExpr' [] -> bool = fun map exprs ->
    let lookupMap = exprs |> toMapBoolExpr
    let rec run : string -> bool = fun name ->
        match Map.find name lookupMap with
        | And' (v, x, y) -> 
            run x && run y 
        | Or' (v, x, y) -> 
            run x || run y 
        | Not' (v, x) ->
            run x |> not
        | Var' (v, x) when x.StartsWith("x") -> map |> Array.find (fun (key, _) -> key = x) |> snd
        | Var' (v, x) -> run x
    run (topVarBoolExpr' exprs)


let getVars : string -> BoolExpr' [] -> string [] = fun prefix exprs ->
    exprs 
    |> Seq.filter (function Var' (_, x) when x.StartsWith(prefix) -> true | _ -> false) 
    |> Seq.map (function Var' (_, x) -> x | _ -> failwith "oups") 
    |> Seq.distinct
    |> Seq.toArray


let countVars : string -> BoolExpr' [] -> int = fun prefix exprs ->
    exprs |> getVars prefix |> Seq.length

let updateVars : BoolExpr' [] -> BoolExpr' [] = fun exprs ->
    let vars = exprs |> getVars "y"
    let vars' = exprs |> getVars "y" |> Array.mapi (fun i _ -> sprintf "x%d" i) 
    exprs |> Array.map (function | Var' (v, x) when x.StartsWith("y") -> Var' (v, vars'.[Array.findIndex ((=) x) vars])
                                 | And' _ | Or' _ | Not' _  | Var' _ as expr -> expr)



let find : int -> (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> 
           (bool [] -> bool) [] ->
           (string [] -> string) [] ->
           int [] ->
           (int -> bool) ->
           int [] -> int [] -> int [] -> int -> (Status * int * Instrs') = 
    fun numOfVars opExprs ops opStrs availableOpExprs verify sample test arityOfOps numOfInstrs ->
        let varBitSize = 3
        let instrBitSize = 8
        let opBitSize = 4
        let numOfOps = availableOpExprs.Length

        //let t = ctx.MkTactic("qffd")
        let solver = ctx.MkSolver("QF_FD")
        let p = ctx.MkParams()
        //solver.Parameters <- p.Add("acce", true).Add("abce", true).Add("cce", true)

        for i in sample do
            let vars = createVars varBitSize numOfVars
            let instrs = createInstrs varBitSize instrBitSize opBitSize arityOfOps numOfInstrs

            let eval = evalInstrs availableOpExprs opExprs vars instrs

            let bits = toBits' numOfVars i
            let freshVars = [|0..numOfVars - 1|] |> Array.map (fun _ -> FreshVar ())
            let inputVarCheck = freshVars |> Array.mapi (fun i var -> And [| lookupVarValue var (toBits varBitSize i) vars; Eq [|var|] [|Val bits.[i]|]|])

            let test = Eq [|instrs.[0].Value|] [|Val (verify i)|]
            solver.Assert(And [|eval; And inputVarCheck; test|])    

        let vars = createVars varBitSize numOfVars
        let instrs = createInstrs varBitSize instrBitSize opBitSize arityOfOps numOfInstrs
        let check = checkInstrs availableOpExprs arityOfOps numOfOps vars instrs
        solver.Assert(check)

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




let randoms : int -> int -> int -> seq<int> = fun seed min max ->
    let random = new Random(seed)
    seq { while true do
            yield random.Next(min, max + 1) }

let getSample : (int -> bool) -> int [] -> int -> int [] = 
    fun verify baseSample numOfSamples ->
        let sample =
            (baseSample |> Seq.filter verify, baseSample |> Seq.filter (not << verify))
            ||> merge
            |> Seq.take numOfSamples
            |> Seq.toArray  
        sample

