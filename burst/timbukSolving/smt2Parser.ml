type token =
  | EOF
  | LP
  | RP
  | NAME of (string)
  | SAT
  | UNSAT
  | UNKNOWN
  | MODEL
  | DECLARE_SORT
  | DECLARE_FUN
  | DEFINE_FUN
  | FORALL
  | OR
  | EQ

open Parsing;;
let _ = parse_error;;
# 2 "src/smt2Parser.mly"

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

# 45 "src/smt2Parser.ml"
let yytransl_const = [|
    0 (* EOF *);
  257 (* LP *);
  258 (* RP *);
  260 (* SAT *);
  261 (* UNSAT *);
  262 (* UNKNOWN *);
  263 (* MODEL *);
  264 (* DECLARE_SORT *);
  265 (* DECLARE_FUN *);
  266 (* DEFINE_FUN *);
  267 (* FORALL *);
  268 (* OR *);
  269 (* EQ *);
    0|]

let yytransl_block = [|
  259 (* NAME *);
    0|]

let yylhs = "\255\255\
\002\000\002\000\002\000\001\000\004\000\005\000\006\000\006\000\
\008\000\007\000\007\000\009\000\009\000\009\000\009\000\003\000\
\003\000\000\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\004\000\004\000\003\000\002\000\003\000\
\001\000\002\000\000\000\003\000\005\000\006\000\005\000\004\000\
\000\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\018\000\002\000\001\000\003\000\
\019\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\004\000\000\000\000\000\000\000\000\000\000\000\012\000\
\000\000\000\000\000\000\000\000\016\000\000\000\000\000\000\000\
\000\000\013\000\000\000\000\000\000\000\015\000\014\000\005\000\
\000\000\000\000\000\000\000\000\007\000\009\000\000\000\006\000\
\010\000\008\000"

let yydgoto = "\003\000\
\005\000\009\000\012\000\028\000\044\000\043\000\045\000\047\000\
\017\000"

let yysindex = "\006\000\
\010\255\000\255\000\000\005\255\000\000\000\000\000\000\000\000\
\000\000\012\255\248\254\013\255\011\255\014\255\015\255\018\255\
\019\255\000\000\017\255\021\255\022\255\023\255\012\255\000\000\
\024\255\025\255\026\255\028\255\000\000\029\255\030\255\031\255\
\027\255\000\000\032\255\034\255\253\254\000\000\000\000\000\000\
\027\255\035\255\037\255\027\255\000\000\000\000\035\255\000\000\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\038\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\038\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\039\255\000\000\000\000\039\255\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\249\255\000\000\248\255\000\000\243\255\246\255\
\000\000"

let yytablesize = 41
let yytable = "\013\000\
\014\000\015\000\016\000\006\000\007\000\008\000\001\000\002\000\
\041\000\042\000\004\000\010\000\011\000\019\000\018\000\029\000\
\020\000\021\000\022\000\024\000\023\000\025\000\026\000\027\000\
\038\000\030\000\031\000\037\000\032\000\033\000\049\000\034\000\
\035\000\036\000\039\000\040\000\050\000\046\000\048\000\017\000\
\011\000"

let yycheck = "\008\001\
\009\001\010\001\011\001\004\001\005\001\006\001\001\000\002\000\
\012\001\013\001\001\001\007\001\001\001\003\001\002\001\023\000\
\003\001\003\001\001\001\003\001\002\001\001\001\001\001\001\001\
\033\000\002\001\002\001\001\001\003\001\002\001\044\000\003\001\
\003\001\003\001\003\001\002\001\047\000\003\001\002\001\002\001\
\002\001"

let yynames_const = "\
  EOF\000\
  LP\000\
  RP\000\
  SAT\000\
  UNSAT\000\
  UNKNOWN\000\
  MODEL\000\
  DECLARE_SORT\000\
  DECLARE_FUN\000\
  DEFINE_FUN\000\
  FORALL\000\
  OR\000\
  EQ\000\
  "

let yynames_block = "\
  NAME\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    Obj.repr(
# 53 "src/smt2Parser.mly"
         ( Smt2.Unsat )
# 154 "src/smt2Parser.ml"
               : Smt2.result))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "src/smt2Parser.mly"
       ( Smt2.Sat )
# 160 "src/smt2Parser.ml"
               : Smt2.result))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "src/smt2Parser.mly"
           ( Smt2.Unknown )
# 166 "src/smt2Parser.ml"
               : Smt2.result))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'commands) in
    Obj.repr(
# 59 "src/smt2Parser.mly"
                      ( _3 )
# 173 "src/smt2Parser.ml"
               : Smt2.model))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 63 "src/smt2Parser.mly"
                  ( (_2, mk_typ _3) )
# 181 "src/smt2Parser.ml"
               : 'binding))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr_body) in
    Obj.repr(
# 67 "src/smt2Parser.mly"
                 ( _2 )
# 188 "src/smt2Parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 71 "src/smt2Parser.mly"
            ( Smt2.Or _2 )
# 195 "src/smt2Parser.ml"
               : 'expr_body))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'value) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'value) in
    Obj.repr(
# 72 "src/smt2Parser.mly"
                  ( Smt2.Eq (_2, _3) )
# 203 "src/smt2Parser.ml"
               : 'expr_body))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 76 "src/smt2Parser.mly"
      ( Var _1 )
# 210 "src/smt2Parser.ml"
               : 'value))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 80 "src/smt2Parser.mly"
              ( _1 :: _2 )
# 218 "src/smt2Parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    Obj.repr(
# 81 "src/smt2Parser.mly"
   ( [] )
# 224 "src/smt2Parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 85 "src/smt2Parser.mly"
                           ( mk_sort_declaration _2 _3 )
# 232 "src/smt2Parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 86 "src/smt2Parser.mly"
                                ( mk_declaration _2 _5 )
# 240 "src/smt2Parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 87 "src/smt2Parser.mly"
                                   ( mk_definition _2 _5 _6 )
# 249 "src/smt2Parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'binding) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 88 "src/smt2Parser.mly"
                             ( mk_forall _3 _5 )
# 257 "src/smt2Parser.ml"
               : 'command))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'command) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'commands) in
    Obj.repr(
# 92 "src/smt2Parser.mly"
                          ( _2::_4 )
# 265 "src/smt2Parser.ml"
               : 'commands))
; (fun __caml_parser_env ->
    Obj.repr(
# 93 "src/smt2Parser.mly"
   ( [] )
# 271 "src/smt2Parser.ml"
               : 'commands))
(* Entry model *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry result *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let model (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Smt2.model)
let result (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf : Smt2.result)
