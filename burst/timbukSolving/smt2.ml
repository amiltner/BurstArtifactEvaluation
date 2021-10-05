type ident = string

type logic =
  | QF_UF

type typ =
  | Int
  | Sort of ident

type const =
  | IntConst of int
  | SortConst of ident * ident (* sort, value *)

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
  | DeclareFun of ident * typ
  | DefineFun of ident * const
  | Assert of expr
  | Forall of (ident * typ) * expr
  | Minimize of ident
  | Check
  | GetModel

type t = command list

let const_typ = function
  | IntConst _ -> Int
  | SortConst (id, _) -> Sort id

let print t out =
  let typename = function
    | Int -> "Int"
    | Sort name -> name
  in
  let logicname = function
    | QF_UF -> "QF_UF"
  in
  let print_const c out =
    match c with
    | IntConst i ->
      Format.fprintf out "%d" i
    | SortConst (_, id) ->
      Format.fprintf out "%s" id
  in
  let print_value v out =
    match v with
    | Var id -> Format.fprintf out "%s" id
    | Const c -> Format.fprintf out "%t" (print_const c)
  in
  let print_binding (x, typ) out =
    Format.fprintf out "(%s %s)" x (typename typ)
  in
  let rec print_expression e out =
    match e with
    | Leq (a, b) ->
      Format.fprintf out "(<= %t %t)" (print_value a) (print_value b)
    | Geq (a, b) ->
      Format.fprintf out "(>= %t %t)" (print_value a) (print_value b)
    | Eq (a, b) ->
      Format.fprintf out "(= %t %t)" (print_value a) (print_value b)
    | Neq (a, b) ->
      Format.fprintf out "(not (= %t %t))" (print_value a) (print_value b)
    | Not e ->
      Format.fprintf out "(not %t)" (print_expression e)
    | And l ->
      Format.fprintf out "(and ";
      List.iter (fun e -> print_expression e out) l;
      Format.fprintf out ")"
    | Or l ->
      Format.fprintf out "(or ";
      List.iter (fun e -> print_expression e out) l;
      Format.fprintf out ")"
    | Impl (a, b) ->
      Format.fprintf out "(=> %t %t)" (print_expression a) (print_expression b)
  in
  let print_command = function
    | SetLogic logic ->
      Format.fprintf out "(set-logic %s)\n" (logicname logic)
    | DeclareSort (id, arity) ->
      Format.fprintf out "(declare-sort %s %d)\n" id arity
    | DeclareConst (id, typ) ->
      Format.fprintf out "(declare-const %s %s)\n" id (typename typ)
    | DeclareFun (id, typ) ->
      Format.fprintf out "(declare-fun %s () %s)\n" id (typename typ)
    | DefineFun (id, const) ->
      Format.fprintf out "(define-fun %s () %s %t)\n" id (typename (const_typ const)) (print_const const)
    | Assert e ->
      Format.fprintf out "(assert %t)\n" (print_expression e)
    | Forall (x, e) ->
      Format.fprintf out "(forall (%t) %t)\n" (print_binding x) (print_expression e)
    | Minimize id ->
      Format.fprintf out "(minimize %s)\n" id
    | Check ->
      Format.fprintf out "(check-sat)\n"
    | GetModel ->
      Format.fprintf out "(get-model)\n"
  in
  List.iter print_command t

type model = command list

type result =
  | Sat
  | Unsat
  | Unknown
