{
	open Smt2Parser

	exception SyntaxError of string
}

let space	= [' ' '\t']
let letter	= ['a'-'z' 'A'-'Z']
let digit	= ['0'-'9']

let ident	= (letter | digit | '_' | '-' | '@' | '!')*
let comline	= ';'([^ '\n'])*

rule token = parse
  | space+			{ token lexbuf } (* skip blanks *)
  | '\n'			{ Lexing.new_line lexbuf; token lexbuf }
	| comline			{ token lexbuf } (* skip comments *)
	| "unsat"				{ UNSAT }
  | "sat"				{ SAT }
	| "unknown"	{ UNKNOWN }
	| "model"		{ MODEL }
	| "declare-sort" { DECLARE_SORT }
	| "declare-fun"	{ DECLARE_FUN }
  | "define-fun"				{ DEFINE_FUN }
	| "forall"	{ FORALL }
	| "or" { OR }
	| "=" { EQ }
  | "("			{ LP }
	| ")"			{ RP }
  | ident as name	{ NAME name }
  | eof				{ EOF }
  | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
