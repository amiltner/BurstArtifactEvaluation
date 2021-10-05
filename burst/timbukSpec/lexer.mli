open Unicode
open UString
open Codemap

type error =
  | Unexpected of UChar.t option

exception Error of error Span.located

module Delimiter : sig
  type t =
    | Parenthesis

  val begin_char : t -> UChar.t

  val end_char : t -> UChar.t
end

module Keyword : sig
  type t =
    | Ops
    | Vars
    | TRS
    | Automaton
    | States
    | Final
    | Transitions
    | Patterns

  val print : t -> Format.formatter -> unit
end

module TokenKind : sig
  type t =
    | End of Delimiter.t
    | Punct of UChar.t
    | Arrow
    | RegularCast
    | Ident
    | Keyword of Keyword.t
    | Int

  val print : t -> Format.formatter -> unit
end

module Token : sig
  type t =
    | Begin of Delimiter.t
    | End of Delimiter.t
    | Punct of UChar.t
    | Arrow
    | RegularCast
    | Ident of Utf8String.t
    | Keyword of Keyword.t
    | Int of int

  val print : t -> Format.formatter -> unit
  val debug : t -> Format.formatter -> unit
end

type token = Token.t

type t = token Span.located Seq.t
(** A lexer is a sequence of located tokens. *)

val create : UChar.t Seq.t -> token Span.located Seq.t
(** Create a lexer from an unicode character sequence. *)

val print_error : error -> Format.formatter -> unit
