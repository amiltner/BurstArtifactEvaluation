%{

open Smt2

let mk_typ = function
	| "Int" -> Int
	| x -> Sort x

let mk_sort_declaration id ar =
	DeclareSort (id, int_of_string ar)

let mk_declaration id typ =
	DeclareFun (id, mk_typ typ)

let mk_const typ v =
	match typ with
	| "Int" -> IntConst (int_of_string v)
	| x -> SortConst (x, v)

let mk_definition id typ v =
	DefineFun (id, mk_const typ v)

let mk_forall binding e =
	Forall (binding, e)

%}

%token EOF

%token LP
%token RP

%token <string> NAME

%token SAT
%token UNSAT
%token UNKNOWN
%token MODEL
%token DECLARE_SORT
%token DECLARE_FUN
%token DEFINE_FUN
%token FORALL
%token OR
%token EQ

%start model result
%type <Smt2.model> model
%type <Smt2.result> result

%%

result:
	  UNSAT { Smt2.Unsat }
	| SAT { Smt2.Sat }
	| UNKNOWN { Smt2.Unknown }
;

model:
	LP MODEL commands RP { $3 }
;

binding:
  LP NAME NAME RP { ($2, mk_typ $3) }
;

expr:
	LP expr_body RP { $2 }
;

expr_body:
	  OR exprs { Smt2.Or $2 }
	| EQ value value { Smt2.Eq ($2, $3) }
;

value:
	NAME { Var $1 }
;

exprs:
	  expr exprs { $1 :: $2 }
	| { [] }
;

command:
    DECLARE_SORT NAME NAME { mk_sort_declaration $2 $3 }
  | DECLARE_FUN NAME LP RP NAME { mk_declaration $2 $5 }
	| DEFINE_FUN NAME LP RP NAME NAME { mk_definition $2 $5 $6 }
	| FORALL LP binding RP expr { mk_forall $3 $5 }
;

commands:
	  LP command RP commands { $2::$4 }
	| { [] }
;
