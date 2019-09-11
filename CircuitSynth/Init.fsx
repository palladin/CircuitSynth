
#r "bin/Microsoft.Z3.dll"
#r "Newtonsoft.Json.dll"

#time

open System
open Microsoft.Z3



let rand = new System.Random()

let setTimeout : float -> unit = fun secs -> 
    let timeout = TimeSpan.FromSeconds(secs).TotalMilliseconds
    Microsoft.Z3.Global.SetParameter("timeout", string timeout)

Microsoft.Z3.Global.ToggleWarningMessages(true)
Microsoft.Z3.Global.SetParameter("parallel.enable", "true")
Microsoft.Z3.Global.SetParameter("model_validate", "true")
setTimeout(20.0)
Microsoft.Z3.Global.SetParameter("model", "true")
printfn "%s" <| Microsoft.Z3.Version.ToString()

let ctx = new Context()

// helpers
let True : BoolExpr = ctx.MkTrue()
let False : BoolExpr = ctx.MkFalse()
let Val : bool -> BoolExpr = fun b -> if b then True else False  
let FreshVar : unit -> BoolExpr = let i = ref 0 in fun () -> incr i; ctx.MkBoolConst(sprintf "temp-%d" !i)
let Var : string -> BoolExpr = fun name -> ctx.MkBoolConst(name)
let VarPos : int -> string -> BoolExpr [] = fun bitSize name -> [| for i in [1..bitSize] -> ctx.MkBoolConst(sprintf "%s-%d" name i) |]
let FreshVarPos : int -> BoolExpr [] = let i = ref 0 in fun bitSize -> incr i; VarPos bitSize (sprintf "tempPos-%d" !i)
let If : BoolExpr -> BoolExpr -> BoolExpr -> BoolExpr = fun p t e -> ctx.MkITE(p, t, e) :?> BoolExpr
let And : BoolExpr [] -> BoolExpr = fun bools -> ctx.MkAnd(bools)
let Or : BoolExpr [] -> BoolExpr = fun bools -> ctx.MkOr(bools)
let Xor : BoolExpr -> BoolExpr -> BoolExpr = fun a b -> ctx.MkXor(a, b)
let Xors : BoolExpr [] -> BoolExpr = fun bools -> bools |> Array.reduce Xor
let Not : BoolExpr -> BoolExpr = fun bool -> ctx.MkNot(bool)
let Eq : BoolExpr [] -> BoolExpr [] -> BoolExpr = fun ls rs -> 
    (ls, rs) ||> Array.zip |> Array.map (fun (l, r) -> ctx.MkEq(l, r)) |> And