%{
open Lang

let rec ctor_of_int (n:int) : exp =
  if n = 0
  then ECtor("O", EUnit)
  else ECtor("S", ctor_of_int (n-1))

let rec list_of_exps (l:exp list) : exp =
  match l with
  | [] -> ECtor("Nil", EUnit)
  | e::es -> ECtor("Cons", ETuple [e; (list_of_exps es)])

let rec appify (e:exp) (es:exp list) : exp =
  match es with
  | [] -> e
  | e'::es -> appify (EApp (e, e')) es
%}

%token <string> LID
%token <string> UID
%token <int> PROJ

%token <int> INT

%token FUN
%token MATCH
%token WITH
%token TYPE
%token OF
%token LET
%token IN
%token REC
%token UNIT

%token HOLE
%token IMPLIES
%token EQ
%token ARR
%token FATARR
%token COMMA
%token COLON
%token SEMI
%token STAR
%token PIPE
%token LPAREN
%token RPAREN
%token LBRACE
%token RBRACE
%token LBRACKET
%token RBRACKET
%token UNDERSCORE
%token DOT

%token EOF

%start prog
%start decls
%type <Lang.prog> prog
%type <Lang.decl list> decls

%%

prog:
  | decls synth_problem EOF
    { (List.rev $1, $2) }

(***** Declarations {{{ *****)

decls:  (* NOTE: reversed *)
  | (* empty *)
    { [] }
  | ds=decls d=datatype
    { d::ds }
  | ds=decls l=letbind
    { l::ds }

datatype:
  | TYPE d=LID EQ cs=ctors
    { DData (d, List.rev cs) }

letbind:
  | LET x=LID COLON t=typ EQ e=exp SEMI SEMI
    { DLet (x, false, [], t, e) }
  | LET x=LID args=arg_list COLON t=typ EQ e=exp SEMI SEMI
    { DLet (x, false, List.rev args, t, e) }
  | LET REC x=LID args=arg_list COLON t=typ EQ e=exp SEMI SEMI
    { DLet (x, true, List.rev args, t, e) }

ctors:  (* NOTE: reversed *)
  | (* empty *)
    { [] }
  | cs=ctors c=ctor
    { c::cs }

ctor:
  | PIPE c=UID OF t=typ
    { (c, t)  }
  | PIPE c=UID
    { (c, TUnit) }  

synth_problem:
  | LET x=LID COLON t=typ IMPLIES LBRACE es=evidencelist RBRACE EQ HOLE
    { (x, t, es) }

(***** }}} *****)

(***** Types {{{ *****)

typ:
  | t=typ_arrow { t }
  | t=typ_tuple { t }
  | t=typ_base  { t }
  | t=typ_paren { t }
  | t=typ_unit  { t }
  | t=typ_rcd   { t }

typ_rcd:
  | LBRACE ts=typ_rcd_list RBRACE
      { TRcd (List.rev ts) }

typ_rcd_list:
  | l=LID COLON t=typ
      { [(l,t)] }
  | ts=typ_rcd_list SEMI l=LID COLON t=typ
      { (l,t)::ts }

typ_arrow:
  | t=typ_non_arrow ARR t2=typ { TArr (t, t2) }

typ_non_arrow:
  | t=typ_tuple { t }
  | t=typ_rcd   { t }
  | t=typ_base  { t }
  | t=typ_paren { t }
  | t=typ_unit  { t }

typ_tuple:
  | ts=typ_tuple_list { TTuple (ts) }

(* STAR binds more tightly than ARR, so we can't have an arrow type on the left. *)
typ_tuple_list: 
  | t=typ_base  STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_paren STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_unit  STAR ts=typ_tuple_list_one { t :: List.rev ts }
  | t=typ_rcd   STAR ts=typ_tuple_list_one { t :: List.rev ts }

typ_tuple_list_one: (* NOTE: reversed *)
  | t=typ_base  { [t] }
  | t=typ_paren { [t] }
  | t=typ_unit  { [t] }
  | t=typ_rcd   { [t] }
  | ts=typ_tuple_list_one STAR t=typ_base  { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_paren { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_unit  { t :: ts }
  | ts=typ_tuple_list_one STAR t=typ_rcd   { t :: ts }

typ_base:
  | d=LID { TBase d }

typ_paren:
  | LPAREN t=typ RPAREN { t }

typ_unit:
  | UNIT { TUnit }

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
    { (x, t) }

arg_list:   (* NOTE: reversed *)
  | (* Empty *)
    { [] }
  | xs=arg_list x=arg
    { x :: xs }

exp_base:
  | x=LID
    { EVar x }
  | FUN x=arg ARR e=exp
    { EFun (x, e) }
  | LET f=LID xs=arg_list COLON t=typ EQ e1=exp IN e2=exp
    { ELet (f, false, List.rev xs, t, e1, e2) }
  | LET REC f=LID xs=arg_list COLON t=typ EQ e1=exp IN e2=exp
    { ELet (f, true, List.rev xs, t, e1, e2) }
  | c=INT
    { ctor_of_int c }
  | c=UID
    { ECtor (c, EUnit) }
  | c=UID LPAREN e=exp RPAREN
    { ECtor (c, e) }
  | c1=UID c2=UID                                         (* Sugar: ctor with ctor argument.   *)
    { ECtor (c1, ECtor (c2, EUnit)) }
  | c=UID x=LID                                           (* Sugar: ctor with var argument.    *)
    { ECtor (c, EVar x) }
  | c=UID LPAREN RPAREN                                   (* Sugar: ctor with unit argument.   *)
    { ECtor (c, EUnit) }
  | c=UID LPAREN e=exp COMMA es=exp_comma_list_one RPAREN (* Sugar: ctor with tuple argument.  *)
    { ECtor (c, ETuple (e :: List.rev es)) }
  | c=UID LBRACE es=exp_lexps_list RBRACE                 (* Sugar: ctor with record argument. *)
    { ECtor (c, ERcd (List.rev es)) }
  | MATCH e=exp WITH bs=branches
    { EMatch (e, List.rev bs) }
  | LBRACKET l=exp_semi_list RBRACKET
    { list_of_exps l }
  | LPAREN e=exp COMMA es=exp_comma_list_one RPAREN
    { ETuple (e :: List.rev es) }
  | n=PROJ e=exp
    { EProj (n, e) }
  | LBRACE es=exp_lexps_list RBRACE
    { ERcd (List.rev es) }
  | e=record_proj_exp DOT l=LID
    { ERcdProj (l,e) }
  | LPAREN e=exp RPAREN
    { e }
  | LPAREN RPAREN
    { EUnit }

record_proj_exp:
  | x=LID
    { EVar x }
  | LBRACE es=exp_lexps_list RBRACE
    { ERcd (List.rev es) }
  | LPAREN e=exp RPAREN
    { e }

exp_comma_list_one:    (* NOTE: reversed *)
  | e=exp
    { [e] }
  | es=exp_comma_list_one COMMA e=exp
    { e :: es }

exp_lexps_list:        (* NOTE: reversed *)
  | l=LID EQ e=exp
    { [(l,e)] }
  | lexps=exp_lexps_list SEMI l=LID EQ e=exp
    { (l,e) :: lexps }

exp_semi_list:
  | (* empty *)
    { [] }
  | e=exp
    { [e] }
  | e=exp SEMI es=exp_semi_list_one
    { e :: List.rev es }

exp_semi_list_one:    (* NOTE: reversed *)
  | e=exp
    { [e] }
  | es=exp_semi_list_one SEMI e=exp
    { e :: es }


branches:   (* NOTE: reversed *)
  | (* empty *)
    { [] }
  | bs=branches b=branch
    { b::bs }

branch:
  | PIPE p=pat ARR e=exp
    { (p, e) }

pat:
  | c=UID p=pattern
    { (c, Some p) }
  | c=UID
    { (c, None) }

pattern:
  | UNDERSCORE
    { PWildcard }
  | x=LID
    { PVar x }
  | LPAREN p=pattern COMMA ps=pattern_list_one RPAREN
    { PTuple (p :: List.rev ps) }
  | LBRACE ps=record_patterns RBRACE
    { PRcd (List.rev ps) }

pattern_list_one: (* Reversed *)
  | p=pattern
    { [p] }
  | ps=pattern_list_one COMMA p=pattern
    { p::ps }

record_patterns: (* Reversed *)
  | l=LID EQ p=pattern
    { [(l,p)] }
  | ps=record_patterns SEMI l=LID EQ p=pattern
    { (l,p) :: ps }

evidence:
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
    { v::vs }

(***** }}} *****)
