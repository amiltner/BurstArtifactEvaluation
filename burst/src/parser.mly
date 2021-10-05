%{
open MyStdLib
open Lang

let rec appify (e:Expr.t) (es:Expr.t list) : Expr.t =
  match es with
  | [] -> e
  | e'::es -> appify (Expr.mk_app e e') es

let mk_unctor_or_ctor_by_name
      (c:String.t)
      (e:Expr.t)
    : Expr.t =
  if String.length c > 3 && String.equal (String.sub c 0 3) "Un_" then
    let c = String.sub c 3 (String.length c - 3) in
    Expr.mk_unctor (Id.create c) e
  else
    Expr.mk_ctor (Id.create c) e
%}

%token <string> LID
%token <string> UID
%token <string> STR
                (*%token <int> PROJ*)

%token <int> INT

%token FUN
%token MATCH
%token WITH
%token TYPE
%token OF
%token LET
%token LBRACKET
%token RBRACKET
(*%token IN*)
(*%token REC*)
%token UNIT

%token EQ
%token FATEQ
%token NEQ
%token EQUIV
%token ARR
%token COMMA
%token COLON
%token SIG
%token END
%token FORALL
%token VAL
%token BINDING
%token WILDCARD
%token MU
%token FIX
%token SYNTH
%token SATISFYING
%token SEMI
%token STAR
%token PIPE
%token LPAREN
%token RPAREN
%token DOT
%token EOF
%token INCLUDE

%start unprocessed_problem
%start exp
%start imports_decls_start
%type <Problem.t_unprocessed> unprocessed_problem
%type <Lang.Expr.t> exp
%type <string list * Declaration.t list> imports_decls_start

%%

unprocessed_problem:
    | ids=imports_decls SYNTH st=typ SATISFYING ds=decl_list s=spec EOF
      { (fst ids,snd ids,st,ds,s) }

imports_decls_start:
    | ids=imports_decls EOF
      { ids }

imports_decls:
    | is=imports ds=decl_list
      { (is,ds) }

imports:
    | INCLUDE s=STR is=imports
      { s::is }
    | { [] }

spec:
    | exs=examples
      {Problem.UIOEs exs}
    | EQUIV e=exp
      {Problem.UEquiv e}
    | e=exp
      {Problem.UPost e}

examples:
  | exs=nonempty_examples
    { exs }
  | { [] }

nonempty_examples:
  | ex=example COMMA exs=examples
    { ex::exs }
  | ex=example
    { [ex] }

example:
  | LBRACKET es=exp_list RBRACKET ARR e=exp
    { (es,e) }

exp_list:
  | es=nonempty_exp_list
    { es }
  | { [] }

nonempty_exp_list:
  | e=exp COMMA es=exp_list
    { e::es }
  | e=exp
    { [e] }

(***** Declarations {{{ *****)

decl_list:
  | (* empty *)
    { [] }
  | d=decl ds=decl_list
    { d::ds }

decl:
  | TYPE i=LID EQ t=typ
    { Declaration.type_dec (Id.create i) t }
  | LET i=LID EQ e=exp SEMI SEMI
    { Declaration.expr_dec (Id.create i) e }

(*datatype:
  | TYPE d=LID EQ cs=ctors
    { DData (d, List.rev cs) }*)

(*letbind:
  | LET x=LID COLON t=typ EQ e=exp SEMI SEMI
    { DLet (x, false, [], t, e) }
  | LET x=LID args=arg_list COLON t=typ EQ e=exp SEMI SEMI
    { DLet (x, false, List.rev args, t, e) }
  | LET REC x=LID args=arg_list COLON t=typ EQ e=exp SEMI SEMI
    { DLet (x, true, List.rev args, t, e) }*)

(*ctors:  (* NOTE: reversed *)
  | (* empty *)
    { [] }
  | cs=ctors c=ctor
    { c::cs }*)

(*ctor:
  | PIPE c=UID OF t=typ
    { (c, t)  }
  | PIPE c=UID
    { (c, TUnit) }  *)

(*synth_problem:
  | LET x=LID COLON t=typ IMPLIES LBRACE es=evidencelist RBRACE EQ HOLE
    { (x, t, es) }*)

(***** }}} *****)

(***** Types {{{ *****)

typ:
  | t=typ_arrow   { t }
  | t=typ_tuple   { t }
  | t=typ_base    { t }
  | t=typ_paren   { t }
  | t=typ_unit    { t }
  | t=typ_mu      { t }
  | t=typ_variant { t }

typ_mu:
  | MU i=LID DOT t=typ { Type.mk_mu (Id.create i) t }

typ_variant:
  | t=typ_single_variant ts=typ_variant
    { Type.mk_variant (t::(Type.destruct_variant_exn ts)) }
  | t=typ_single_variant
    { Type.mk_variant [t] }

typ_single_variant:
  | PIPE i=UID OF t=typ_non_variant
    { (Id.create i,t) }
  | PIPE i=UID
    { (Id.create i,Type.mk_tuple []) }

typ_non_variant:
  | t=typ_arrow   { t }
  | t=typ_tuple   { t }
  | t=typ_base    { t }
  | t=typ_paren   { t }
  | t=typ_unit    { t }
  | t=typ_mu      { t }

typ_arrow:
  | t=typ_non_arrow ARR t2=typ { Type.mk_arrow t t2 }

typ_non_arrow:
  | t=typ_tuple { t }
  | t=typ_base  { t }
  | t=typ_paren { t }
  | t=typ_unit  { t }

typ_tuple:
  | ts=typ_tuple_list { Type.mk_tuple ts }

(* STAR binds more tightly than ARR, so we can't have an arrow type on the left. *)
typ_tuple_list:
  | t=typ_base  STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_paren STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_unit  STAR ts=typ_tuple_list_one { t :: List.rev ts }

typ_tuple_list_one: (* NOTE: reversed *)
  | t=typ_base  { [t] }
  | t=typ_paren { [t] }
  | t=typ_unit  { [t] }
  | ts=typ_tuple_list_one STAR t=typ_base  { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_paren { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_unit  { t :: ts }

typ_base:
  | d=LID { Type.mk_named (Id.create d) }

typ_paren:
  | LPAREN t=typ RPAREN { t }

typ_unit:
  | UNIT { Type.mk_tuple [] }

(***** }}} *****)

(***** Expressions {{{ *****)

exp:
  | e=exp_app
    { e }

exp_app:
  | e=exp_base es=exp_app_list
    { appify e (List.rev es) }
  | e=exp_base
    { e }

exp_app_list:     (* NOTE: reversed *)
  | e=exp_base
    { [e] }
  | es=exp_app_list e=exp_base
    { e::es }

arg:
  | LPAREN x=LID COLON t=typ RPAREN
    { (Id.create x, t) }

(*arg_list:   (* NOTE: reversed *)
  | (* Empty *)
    { [] }
  | xs=arg_list x=arg
    { x :: xs }*)

exp_base:
  | x=LID
    { Expr.mk_var (Id.create x) }
  | FUN x=arg ARR e=exp_base
    { Expr.mk_func x e }
  | FIX a=arg EQ e=exp_base
    { Expr.mk_fix (fst a) (snd a) e }
  (*| LET f=LID xs=arg_list COLON t=typ EQ e1=exp IN e2=exp
    { ELet (f, false, List.rev xs, t, e1, e2) }
  | LET REC f=LID xs=arg_list COLON t=typ EQ e1=exp IN e2=exp
    { ELet (f, true, List.rev xs, t, e1, e2) }*)
  | c=INT
    { Expr.from_int c }
  | c=UID
    {
      mk_unctor_or_ctor_by_name c Expr.mk_unit
    }
  | c=UID LPAREN e=exp RPAREN
                     { mk_unctor_or_ctor_by_name c e }
  | c1=UID c2=UID                                         (* Sugar: ctor with ctor argument.   *)
                { mk_unctor_or_ctor_by_name c1 (mk_unctor_or_ctor_by_name c2 Expr.mk_unit) }
  | c=UID x=LID                                           (* Sugar: ctor with var argument.    *)
              { mk_unctor_or_ctor_by_name c (Expr.mk_var (Id.create x)) }
  | c=UID LPAREN RPAREN                                   (* Sugar: ctor with unit argument.   *)
        { mk_unctor_or_ctor_by_name c Expr.mk_unit }
  | c=UID LPAREN e=exp COMMA es=exp_comma_list_one RPAREN (* Sugar: ctor with tuple argument.  *)
                                  { mk_unctor_or_ctor_by_name c (Expr.mk_tuple (e :: List.rev es)) }
  | MATCH e=exp WITH bs=branches
    { Expr.mk_match e (List.rev bs) }
  | LPAREN e=exp COMMA es=exp_comma_list_one RPAREN
    { Expr.mk_tuple (e :: List.rev es) }
  | e=exp_base DOT n=INT
    { Expr.mk_proj n e }
  | e1=exp_base FATEQ e2=exp_base
    { Expr.mk_eq true e1 e2 }
  | e1=exp_base NEQ e2=exp_base
    { Expr.mk_eq false e1 e2 }
  | LPAREN e=exp RPAREN
    { e }
  | LPAREN RPAREN
    { Expr.mk_unit }

exp_comma_list_one:    (* NOTE: reversed *)
  | e=exp
    { [e] }
  | es=exp_comma_list_one COMMA e=exp
    { e :: es }


branches:   (* NOTE: reversed *)
  | (* empty *)
    { [] }
  | bs=branches b=branch
    { b::bs }

branch:
  | PIPE p=pattern ARR e=exp
    { (p, e) }

pattern:
  | c=UID
    { (Pattern.Ctor (Id.create c,Pattern.Wildcard)) }
  | c=UID p=pattern
    { (Pattern.Ctor (Id.create c,p)) }
  | WILDCARD
    { Pattern.Wildcard }
  | LPAREN RPAREN
    { Pattern.Tuple [] }
  | LPAREN p=pattern COMMA ps=pattern_list RPAREN
    { Pattern.Tuple (p :: List.rev ps) }
  | x=LID
    { Pattern.Var (Id.create x) }

pattern_list: (* Reversed *)
  | p=pattern
    { [p] }
  | ps=pattern_list COMMA p=pattern
    { p::ps }

(*evidence:
  | v=ev_val
    { v }

ev_val:
  | v=ev_val_ios
    { v }
  | v=ev_val_base
    { v }

ev_val_ios:
  | v=ev_val_io
    { EPFun [v] }
  | v1=ev_val_io PIPE vs=ev_val_ios_one
    { EPFun (v1 :: List.rev vs) }

ev_val_ios_one:   (* NOTE: reversed *)
  | v=ev_val_io
    { [v] }
  | v=ev_val_io PIPE vs=ev_val_ios_one
    { v :: vs }

ev_val_io:
  | v1=ev_val_base FATARR v2=ev_val_io_one
    { (v1, v2) }

ev_val_io_one:
  | v=ev_val_base
    { v }
  | v1=ev_val_base FATARR v2=ev_val_io_one
    { EPFun [(v1, v2)] }

ev_val_base:
  | x=LID
    { EVar x }
  | FUN x=arg ARR e=exp
    { EFun (x, e) }
  | c=UID LPAREN v=ev_val RPAREN
    { ECtor (c, v) }
  | c1=UID c2=UID                                         (* Sugar: ctor with ctor argument.  *)
    { ECtor (c1, ECtor (c2, EUnit)) }
  | c=UID x=LID                                           (* Sugar: ctor with var argument.   *)
    { ECtor (c, EVar x) }
  | c=UID LPAREN RPAREN                                   (* Sugar: ctor with unit argument.  *)
    { ECtor (c, EUnit) }
  | c=UID LPAREN v=ev_val COMMA vs=ev_val_list_one RPAREN (* Sugar: ctor with tuple argument. *)
    { ECtor (c, ETuple (v :: List.rev vs)) }
  | c=INT
    { ctor_of_int c }
  | c=UID
    { ECtor (c, EUnit) }
  | LBRACKET l=ev_val_semi_list RBRACKET
    { list_of_exps l }
  | LPAREN v=ev_val RPAREN
    { v }
  | LPAREN RPAREN
    { EUnit }
  | LPAREN v=ev_val COMMA vs=ev_val_list_one RPAREN
    { ETuple (v:: List.rev vs) }
  | LBRACE lvs=ev_lvals_list RBRACE
    { ERcd (List.rev lvs) }

ev_val_semi_list:
  | (* empty *)
    { [] }
  | v=ev_val
    { [v] }
  | v=ev_val SEMI vs=ev_val_semi_list_one
    { v :: List.rev vs }

ev_val_semi_list_one:
  | v=ev_val
    { [v] }
  | vs=ev_val_semi_list_one SEMI v=ev_val
    { v::vs }

ev_val_list_one:
  | v=ev_val
    { [v] }
  | vs=ev_val_list_one COMMA v=ev_val
    { v::vs }

ev_lvals_list:
  | l=LID EQ v=ev_val
    { [(l,v)] }
  | vs=ev_lvals_list SEMI l=LID EQ v=ev_val
    { (l,v)::vs }

evidencelist:
  | (* empty *)
    { [] }
  | v=evidence
    { [v] }
  | v=evidence SEMI vs=evidencelist_one
    { v :: List.rev vs }

evidencelist_one:    (* NOTE: reversed *)
  | v=evidence
    { [v] }
  | vs=evidencelist_one SEMI v=evidence
    { v::vs }*)

(***** }}} *****)

