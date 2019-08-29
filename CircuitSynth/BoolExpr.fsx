#load "Init.fsx"
#load "Utils.fsx"
#load "CoreTypes.fsx"
#load "Core.fsx"

open System
open System.Collections.Generic
open System.IO
open Microsoft.Z3
open Utils
open Init
open CoreTypes
open Core




let toBoolExpr' : BoolExpr -> BoolExpr' []  = fun expr ->

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
            
    let f : BoolExpr -> BoolExpr' = fun expr ->
        match expr with
        | Eq (Var v, And (Var x, Var y)) -> And' (v, x, y)
        | Eq (Var v, Or (Var x, Var y)) -> Or' (v, x, y)
        | Eq (Var v, Not (Var x)) -> Not' (v, x)
        | Eq (Var x, Var y) -> Var' (x, y)
        | _ -> failwithf "oups %A - %d" expr expr.NumArgs
        
    expr |> toBoolExprs |> Array.map f

let getVarBoolExpr' : BoolExpr' -> string = fun expr ->
    match expr with 
    | And' (v, x, y) | Or' (v, x, y) -> v 
    | Not' (v, x) | Var' (v, x) -> v
    | Func' (v, _,  _) -> v

let toBoolExpr : (BoolExpr -> BoolExpr [] -> BoolExpr) [] -> BoolExpr' [] -> BoolExpr -> BoolExpr [] -> BoolExpr = 
    fun opExprs exprs res vars ->
        let dict = new Dictionary<string, BoolExpr>()
        for i = 0 to vars.Length - 1 do
            dict.Add("x" + string i, vars.[i]) 
        let f : string -> BoolExpr = fun v -> if not <| dict.ContainsKey(v) then 
                                                let fresh = FreshVar ()
                                                dict.Add(v, fresh)
                                                fresh
                                              else dict.[v]
        let exprs' = 
            exprs |> Array.map (function | And' (v, x, y) -> Eq [|f v|] [|And [|f x; f y|]|]
                                         | Or' (v, x, y) -> Eq [|f v|] [|Or [|f x; f y|]|]
                                         | Not' (v, x) -> Eq [|f v|] [|Not (f x)|]
                                         | Func' (v, args, iop) -> opExprs.[iop] (f v) (args |> Array.map f)
                                         | _ -> failwith "oups") 

        And <| Array.append [|Eq [|res|] [|f <| getVarBoolExpr' exprs.[0]|]|] exprs'
    
let toMapBoolExpr : BoolExpr' [] -> Map<string, BoolExpr'> = fun exprs ->
    exprs |> Array.map (fun expr -> match expr with 
                                     | And' (v, x, y) -> (v, expr)
                                     | Or' (v, x, y) -> (v, expr)
                                     | Not' (v, x) -> (v, expr)
                                     | Var' (v, x) -> (v, expr)
                                     | Func' (v, _, _) -> (v, expr))
          |> Map.ofArray

let toDictBoolExpr : BoolExpr' [] -> Dictionary<string, BoolExpr'> = fun exprs ->
    let dict = new Dictionary<string, BoolExpr'>()
    let vars = 
        exprs |> Array.map (fun expr -> match expr with 
                                         | And' (v, x, y) -> (v, expr)
                                         | Or' (v, x, y) -> (v, expr)
                                         | Not' (v, x) -> (v, expr)
                                         | Var' (v, x) -> (v, expr)
                                         | Func' (v, _, _) -> (v, expr))
    for (v, expr) in vars do
        dict.Add(v, expr)
    dict
          
    

let countOps' : BoolExpr' [] -> int = fun exprs ->
    exprs |> Array.map (function | And' (v, x, y) -> 1
                                 | Or' (v, x, y) -> 1
                                 | Not' (v, x) -> 1
                                 | Var' (v, x) -> 0
                                 | Func' _ -> 1)
          |> Array.sum

let countVars : BoolExpr' [] -> int = fun exprs ->
    exprs |> Array.map (function | And' (v, x, y) -> [|x; y|]
                                 | Or' (v, x, y) -> [|x; y|]
                                 | Not' (v, x) -> [|x|]
                                 | Func' (v, args, _) -> args
                                 | _ -> failwith "oups")
          |> Array.concat
          |> Array.filter (fun x -> x.StartsWith("x"))
          |> Array.distinct
          |> Array.length


let eval' : (bool [] -> bool) [] -> BoolExpr' [] -> bool [] -> bool = fun ops exprs vars ->
    let numOfVars = vars.Length
    let map = ([|0..numOfVars - 1|] |> Array.map (fun i -> "x" + string i), vars) ||> Array.zip  
    let lookupMap = exprs |> toMapBoolExpr
    let rec run : string -> bool = fun name ->
        let f : string -> bool = fun x -> 
            if x.StartsWith("x") then  
                map |> Array.find (fun (key, _) -> key = x) |> snd
            else run x
        match Map.tryFind name lookupMap with
        | Some expr -> 
            match expr with
            | And' (v, x, y) -> 
                f x && f y
            | Or' (v, x, y) -> 
                f x || f y 
            | Not' (v, x) ->
                f x |> not
            | Func' (v, args, iop) -> 
                ops.[iop] (args |> Array.map f)
            | _ -> failwith "oups"
        | None -> failwithf "not found %s" name
    run (getVarBoolExpr' exprs.[0])

let removeVars : BoolExpr' [] -> BoolExpr' [] = fun exprs -> 
    let dict = toDictBoolExpr exprs
    let rec f : string -> string = fun name -> 
        if dict.ContainsKey(name) then
            match dict.[name] with
            | Var' (v, x) when x.StartsWith("x") ->
                x
            | Var' (v, x) -> 
                f x
            | _ -> name
        else name
    for expr in exprs do
        match expr with
        | And' (v, x, y) -> dict.[v] <- And' (v, f x, f y)
        | Or' (v, x, y) -> dict.[v] <- Or' (v, f x, f y)
        | Not' (v, x) -> dict.[v] <- Not' (v, f x)
        | Var' (v, _) -> dict.Remove(v) |> ignore
        | Func' (v, args, iop) -> dict.[v] <- Func' (v, args |> Array.map f, iop)
    [| for keyValue in dict do yield keyValue.Value  |]

let updateVars : BoolExpr' [] -> BoolExpr' [] = fun exprs ->
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
        | Some _ -> name
    for i = 0 to exprs.Length - 1 do
        match exprs.[i] with
        | And' (v, x, y) -> exprs.[i] <- And' (f v, f x, f y)
        | Or' (v, x, y) -> exprs.[i] <- Or' (f v, f x, f y)
        | Not' (v, x) -> exprs.[i] <- Not' (f v, f x)
        | Var' (_, _) -> failwith "oups"
        | Func' (v, args, iop) -> exprs.[i] <- Func' (f v, args |> Array.map f, iop)
    exprs



let subs : string [] -> BoolExpr' [] -> BoolExpr' [] = fun args exprs -> 
    let vars = [|0..args.Length - 1|] |> Array.map (fun i -> "x" + string i)
    let map = (vars, args) ||> Array.zip |> Map.ofArray 
    let f : string -> string = fun v ->  
        match Map.tryFind v map with
        | Some v' -> v'
        | None -> v
    exprs |> Array.map (function | And' (v, x, y) -> And' (v, f x, f y)
                                 | Or' (v, x, y) -> Or' (v, f x, f y)
                                 | Not' (v, x) -> Not' (v, f x)
                                 | Func' (v, args, iop) -> Func' (v, args |> Array.map f, iop)
                                 | _ -> failwith "oups")





