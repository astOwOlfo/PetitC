type ident = string

type loc = Lexing.position * Lexing.position

let zero_position: Lexing.position = {
  Lexing.pos_fname = "";
  Lexing.pos_lnum = 0;
  Lexing.pos_bol = 0;
  Lexing.pos_cnum = 0
}

let zero_loc = (zero_position, zero_position)


type unop =
  | Dereference
  | AddressOf
  | UnaryMinus
  | UnaryPlus
  | Not
  | PreIncrement
  | PostIncrement
  | PreDecrement
  | PostDecrement

type binop =
  | Assign
  | Plus
  | Minus
  | Times
  | Div
  | Mod
  | Eq
  | Ne
  | Lt
  | Le
  | Gt
  | Ge
  | And
  | Or

type _type =
  | Int of loc
  | Bool of loc
  | Ptr of loc * _type
  | Void of loc

type expr =
  | Const of loc * int64
  | Null of loc
  | Var of loc * ident
  | UnOp of loc * unop * expr
  | BinOp of loc * binop * expr * expr
  | Call of loc * ident * expr list
  | Sizeof of loc * _type

type instr =
  | Expr of loc * expr
  | If of loc * expr * instr
  | IfElse of loc * expr * instr * instr
  | While of loc * expr * instr
  | For of loc * var_decl option * expr option * expr list * instr
  | Break of loc
  | Continue of loc
  | Block of loc * instr_or_decl list
  | Return of loc
  | ReturnExpr of loc * expr
  | NOP of loc

and var_decl =
  | VarDecl of loc * _type * ident * expr option

and func_decl =
  | FuncDecl of loc * _type * ident * (_type * ident) list * instr_or_decl list

and instr_or_decl =
  | Instr of loc * instr
  | DeclVar of loc * var_decl
  | DeclFunc of loc * func_decl

type file = func_decl list

let expr_loc : expr -> loc = function
  | Const (loc, _) | Null loc | Var (loc, _) | UnOp (loc, _, _)
  | BinOp (loc, _, _, _) | Call (loc, _, _) | Sizeof (loc, _) -> loc
