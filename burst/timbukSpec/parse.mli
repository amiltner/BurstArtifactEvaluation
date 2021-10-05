open Codemap

type error =
  | Unexpected of Lexer.token option * Lexer.TokenKind.t list

exception Error of error Span.located

val specification : Lexer.t -> Ast.specification Span.located
(** Create a lexer from an unicode character sequence. *)

val print_error : error -> Format.formatter -> unit
