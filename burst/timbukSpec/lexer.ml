open Unicode
open UString
open Codemap

type error =
  | Unexpected of UChar.t option

exception Error of error Span.located

module Delimiter = struct
  type t =
    | Parenthesis

  let begin_char = function
    | Parenthesis -> UChar.of_ascii '('

  let end_char = function
    | Parenthesis -> UChar.of_ascii ')'
end

module Keyword = struct
  type t =
    | Ops
    | Vars
    | TRS
    | Automaton
    | States
    | Final
    | Transitions
    | Patterns

  let print t fmt =
    match t with
    | Ops -> Format.fprintf fmt "Ops"
    | Vars -> Format.fprintf fmt "Vars"
    | TRS -> Format.fprintf fmt "TRS"
    | Automaton -> Format.fprintf fmt "Automaton"
    | States -> Format.fprintf fmt "States"
    | Final -> Format.fprintf fmt "Final"
    | Transitions -> Format.fprintf fmt "Transitions"
    | Patterns -> Format.fprintf fmt "Patterns"
end

module TokenKind = struct
  type t =
    | End of Delimiter.t
    | Punct of UChar.t
    | Arrow
    | RegularCast
    | Ident
    | Keyword of Keyword.t
    | Int

  let print t fmt =
    match t with
    | End d -> Format.fprintf fmt "`%s`" (Utf8String.of_char (Delimiter.end_char d))
    | Punct c -> Format.fprintf fmt "`%s`" (Utf8String.of_char c)
    | Arrow -> Format.fprintf fmt "arrow `->`"
    | RegularCast -> Format.fprintf fmt "regular cast operator `::`"
    | Ident -> Format.fprintf fmt "identifier"
    | Keyword k -> Format.fprintf fmt "`%t`" (Keyword.print k)
    | Int -> Format.fprintf fmt "integer"
end

module Token = struct
  type t =
    | Begin of Delimiter.t
    | End of Delimiter.t
    | Punct of UChar.t
    | Arrow
    | RegularCast
    | Ident of Utf8String.t
    | Keyword of Keyword.t
    | Int of int

  let print t fmt =
    match t with
    | Begin d -> Format.fprintf fmt "%s" (Utf8String.of_char (Delimiter.begin_char d))
    | End d -> Format.fprintf fmt "%s" (Utf8String.of_char (Delimiter.end_char d))
    | Punct c -> Format.fprintf fmt "%s" (Utf8String.of_char c)
    | Arrow -> Format.fprintf fmt "->"
    | RegularCast -> Format.fprintf fmt "::"
    | Ident id -> Format.fprintf fmt "%s" id
    | Keyword k -> Format.fprintf fmt "%t" (Keyword.print k)
    | Int i -> Format.fprintf fmt "%d" i

  let debug t fmt =
    match t with
    | Begin d -> Format.fprintf fmt "opening `%s`" (Utf8String.of_char (Delimiter.begin_char d))
    | End d -> Format.fprintf fmt "closing `%s`" (Utf8String.of_char (Delimiter.end_char d))
    | Punct c -> Format.fprintf fmt "token `%s`" (Utf8String.of_char c)
    | Arrow -> Format.fprintf fmt "arrow `->`"
    | RegularCast -> Format.fprintf fmt "regular cast operator `::`"
    | Ident id -> Format.fprintf fmt "identifier `%s`" id
    | Keyword k -> Format.fprintf fmt "keyword `%t`" (Keyword.print k)
    | Int i -> Format.fprintf fmt "integer `%d`" i
end

type token = Token.t

type t = token Span.located Seq.t
(** A lexer is a sequence of located tokens. *)

let consume span chars =
  begin match chars () with
    | Seq.Nil -> (span, Seq.Nil)
    | Seq.Cons (c, chars) ->
      (* Add [c] to the [span]. *)
      let span = Span.push c span in
      (span, Seq.Cons (c, chars))
  end

let is_punct c =
  begin match UChar.to_int c with
    | 0x2c | 0x3a (* ,: *) -> true
    | _ -> false
  end

let is_delimiter c =
  begin match UChar.to_int c with
    | 0x28 | 0x29 (* () *) -> true
    | _ -> false
  end

let is_separator c =
  begin match UChar.to_int c with
    | 0x28 | 0x29 (* () *) -> true
    | 0x25 (* % *) -> true
    | _ when UChar.is_whitespace c || UChar.is_control c || is_punct c -> true
    | _ -> false
  end

let uint_of_string str =
  Utf8String.fold_left (
    fun i c -> i * 10 + (UChar.to_digit 10 c)
  ) 0 str

let uint_of_string_opt str =
  try Some (uint_of_string str) with
  | Invalid_argument _ -> None

let rec next span chars () =
  let return span chars token =
    Seq.Cons (Span.located span token, next (Span.next span) chars)
  in
  begin match consume span chars with
    | _, Seq.Nil -> Seq.Nil
    | span', Seq.Cons (c, chars') ->
      (* Find the token type. *)
      begin match UChar.to_int c with
        | _ when UChar.is_whitespace c || UChar.is_control c ->
          (* skip spaces and controls. *)
          next (Span.next span') chars' ()
        | 0x25 -> (* % *)
          skip_comment span' chars'
        | 0x28 -> (* ( *)
          return span' chars' (Token.Begin Delimiter.Parenthesis)
        | 0x29 -> (* ) *)
          return span' chars' (Token.End Delimiter.Parenthesis)
        | 0x3a -> (* : *)
          begin match consume span' chars' with
            | span', Seq.Cons (c, chars') when (UChar.to_int c) = 0x3a -> (* :: *)
              return span' chars' Token.RegularCast
            | _ ->
              return span' chars' (Token.Punct c)
          end
        | _ when is_punct c ->
          return span' chars' (Token.Punct c)
        | _ ->
          (* It's a terminal, or a keyword. *)
          lex_ident span chars
      end
  end

and skip_comment span chars =
  begin match consume span chars with
    | _, Seq.Nil -> Seq.Nil
    | span', Seq.Cons (c, chars') ->
      begin match UChar.to_int c with
        | 0x0a -> (* \n *)
          next span' chars' ()
        | _ ->
          skip_comment span' chars'
      end
  end

and lex_ident span chars =
  let return span chars id =
    let token = match id with
      | "Ops" -> Token.Keyword Keyword.Ops
      | "Vars" -> Token.Keyword Keyword.Vars
      | "TRS" -> Token.Keyword Keyword.TRS
      | "Automaton" -> Token.Keyword Keyword.Automaton
      | "States" -> Token.Keyword Keyword.States
      | "Final" -> Token.Keyword Keyword.Final
      | "Transitions" -> Token.Keyword Keyword.Transitions
      | "Patterns" -> Token.Keyword Keyword.Patterns
      | "->" -> Token.Arrow
      | id ->
        begin match uint_of_string_opt id with
          | Some i -> Token.Int i
          | None -> Token.Ident id
        end
    in
    Seq.Cons (Span.located span token, next (Span.next span) chars)
  in
  let rec add_char span chars id =
    begin match consume span chars with
      | _, Seq.Nil -> Seq.Nil
      | span', Seq.Cons (c, chars') ->
        if is_separator c then
          return span chars id
        else
          add_char span' chars' (Utf8String.push c id)
    end
  in
  add_char span chars ""

let create chars =
  next Span.default chars

let print_error e fmt =
  match e with
  | Unexpected (Some c) ->
    Format.fprintf fmt "unexpected char `%s`" (Utf8String.push c "")
  | Unexpected None ->
    Format.fprintf fmt "unexpected end of file"
