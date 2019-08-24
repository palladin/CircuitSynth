#load "Init.fsx"

open Init
open System
open Microsoft.Z3

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

type BoolExpr' = 
    | And' of string * string * string
    | Or' of string * string * string
    | Not' of string * string
    | Var' of string * string 
    | Func' of string * string [] * int 

type Ops = { OpExprs : (BoolExpr -> BoolExpr [] -> BoolExpr) [];
             Ops : (bool [] -> bool) [];
             OpStrs : (string [] -> string) [];
             OpExprs' : BoolExpr' [] [];
             ArityOps : int [] }
