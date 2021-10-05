let parse_with_errors
    (type a)
    (parser:(Lexing.lexbuf -> Parser.token) -> Lexing.lexbuf -> a)
    (s:string)
  : a =
  let lexbuf = Lexing.from_string ~with_positions:true s in
  try
    parser
      Lexer.token
      lexbuf
  with _ ->
    failwith ("Unexpected token between positions: ("
              ^ (Int.to_string lexbuf.lex_start_p.pos_lnum)
              ^ "," ^ (Int.to_string (lexbuf.lex_start_p.pos_cnum - lexbuf.lex_start_p.pos_bol))
              ^ ") and ("
              ^ (Int.to_string lexbuf.lex_curr_p.pos_lnum)
              ^ "," ^ (Int.to_string (lexbuf.lex_curr_p.pos_cnum - lexbuf.lex_curr_p.pos_bol))
              ^ ")")

let unprocessed_problem
    (s:String.t)
  : Problem.t_unprocessed =
  parse_with_errors Parser.unprocessed_problem s

let import_decls_start
    (s:String.t)
  : (string list * Declaration.t list) =
  parse_with_errors Parser.imports_decls_start s

let exp
    (s:String.t)
  : Lang.Expr.t =
  parse_with_errors Parser.exp s
