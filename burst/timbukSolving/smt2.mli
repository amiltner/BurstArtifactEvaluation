type ident = string

type logic =
  | QF_UF

type typ =
  | Int
  | Sort of ident

type const =
  | IntConst of int
  | SortConst of ident * ident

type value =
  | Var of ident
  | Const of const

type expr =
  | Leq of value * value
  | Geq of value * value
  | Eq of value * value
  | Neq of value * value
  | Not of expr
  | And of expr list
  | Or of expr list
  | Impl of expr * expr

type command =
  | SetLogic of logic
  | DeclareSort of ident * int
  | DeclareConst of ident * typ
  | DeclareFun of ident * typ (* arity 0 *)
  | DefineFun of ident * const
  | Assert of expr
  | Forall of (ident * typ) * expr
  | Minimize of ident
  | Check
  | GetModel

type t = command list

val print: t -> Format.formatter -> unit

type model = command list

type result =
  | Sat
  | Unsat
  | Unknown
