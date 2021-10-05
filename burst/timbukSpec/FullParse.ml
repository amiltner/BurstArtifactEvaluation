open Collections
open Codemap
open Timbuk
open Unicode
open UString

module Integer = struct
  type t = int

  let compare a b = a - b

  let print i fmt =
    Format.fprintf fmt "%d" i
end

module Cvc4Conf = struct
  let path () = "cvc4"

  let count = ref 0

  let log () =
    (* let i = !count in
       count := i + 1;
       let filename = "log/cvc4_" ^ (string_of_int i) ^ ".smt2" in
       Some (filename, open_out filename) *)
    None
end

(* Polymorphic typing. *)
(*module PolyTyper = TimbukTyping.Poly.Make (Codemap.Span) (Symbol) (Base) (Aut) (LocPattern) (LocTrs) (PolyTypedTrs)*)

(* Monomorphic typing. *)

  (*| InvalidTargetType of MonoAut.StateSet.t * RegularTyper.RegularTypePartition.t
    | RegularTypeMissmatch of RegularTyper.RegularType.t * RegularTyper.RegularTypedPattern.t * MonoAut.t*)

type error =
  | Parse of Parse.error * Codemap.Span.t
  (*| PolyType of PolyTyper.error * Codemap.Span.t*)
  (*| MonoType of MonoTyper.error * Codemap.Span.t
    | SubType of SubTyper.error * Codemap.Span.t
    | RegularType of RegularTyper.error*)

exception Error of error

let error_kind = function
  | Parse _ -> "syntax error"
  (*| PolyType (e, _) -> "polymorphic type error"*)
  (*| MonoType (e, _) -> "monomorphic type error"
  | SubType (e, _) -> "sub-type error"
    | RegularType _ -> "regular type error"*)

let error_message = function
  | Parse _ -> None
  (*| PolyType (e, _) -> Some (Format.asprintf "%t" (PolyTyper.print_error e))*)
  (*| MonoType (e, _) -> Some (Format.asprintf "%t" (MonoTyper.print_error e))
  | SubType (e, _) -> Some (Format.asprintf "%t" (SubTyper.print_error e))
  | RegularType (RegularTyper.BiTypedTerm (_, q, q', _)) ->
    Some (Format.asprintf "unable to separate types `%t' and `%t'" (RegularTyper.TypeAut.State.print q) (RegularTyper.TypeAut.State.print q'))*)
  (*| Runtime (InvalidTargetType (target_ty, partition)) ->
    let print_partition_elt elt fmt =
      Format.fprintf fmt "{%t}" (MonoAut.StateSet.print MonoType.print ", " elt)
    in
    Some (Format.asprintf "the given target type `%t` is not in the type partition `{%t}'"
            (RegularType.print target_ty)
            (RegularTyper.RegularTypePartition.print print_partition_elt ", " partition))
  | Runtime (RegularTypeMissmatch (expected_ty, (_, (found_ty, _)), _)) ->
    Some (Format.asprintf "expected regular type `%t', found `%t'" (RegularType.print expected_ty) (RegularType.print found_ty))*)

let error_content = function
  | Parse (_, span) -> (None, Some span)
  (*| PolyType (e, span) -> (PolyTyper.error_label e, Some span)*)
  (*| MonoType (e, span) -> (MonoTyper.error_label e, Some span)
  | SubType (e, span) -> (SubTyper.error_label e, Some span)
    | RegularType _ -> (None, None)*)

let format_error_hints fmt = function
  | Parse _ -> ()
  (*| PolyType (e, _) ->
    begin
      match e with
      | TypeMissmatch (expected_ty, Some expected_span, _) ->
        let msg = Format.asprintf "type `%t' is required here" (Aut.State.print expected_ty) in
        Codemap.Formatter.add fmt expected_span (Some msg) Codemap.Formatter.Highlight.Note
      | _ -> ()
    end*)
  (*| MonoType (_e, _) -> ()
  | SubType (_e, _) -> ()
    | RegularType _ -> ()*)

let help ppf f =
  Format.fprintf ppf "\x1b[1;34mnote: \x1b[0m";
  f (Format.fprintf ppf);
  Format.fprintf ppf "@."

let print_error_help ppf = function
  (*| Runtime (RegularTypeMissmatch (expected_ty, found_pattern, aut)) ->
    let sample = instanciate_pattern aut found_pattern in
    help ppf (fun m -> m "here is a term that may not rewrite to %t:\n\n      \x1b[1;1m%t\x1b[0m\n" (RegularType.print expected_ty) (MonoTerm.print sample));*)
  | _ -> ()

let format_error input e ppf =
  let label_opt, span_opt = error_content e in
  let msg_opt = error_message e in
  Format.fprintf ppf "\x1b[1;31m%s\x1b[0m\x1b[1;1m" (error_kind e);
  begin match span_opt with
    | Some span -> Format.fprintf ppf " (%t)" (Codemap.Span.format span)
    | None -> ()
  end;
  begin match msg_opt with
    | Some msg -> Format.fprintf ppf ": %s" msg
    | None -> ()
  end;
  Format.fprintf ppf "\x1b[0m@.";
  begin match span_opt with
    | Some span ->
      let fmt = Formatter.create () in
      let viewport = Span.from_start (Span.aligned ~margin:1 span) in
      Formatter.add fmt span label_opt Formatter.Highlight.Error;
      format_error_hints fmt e;
      Formatter.print fmt input viewport stderr
    | None -> ()
  end;
  print_error_help ppf e

(** Make a sequence of char out of an input channel. *)
let seq_of_channel input =
  let rec next mem () =
    match !mem with
    | Some res -> res
    | None ->
      let res =
        try
          let c = input_char input in
          Seq.Cons (c, next (ref None))
        with
        | End_of_file -> Seq.Nil
      in
      mem := Some res;
      res
  in
  next (ref None)


let process_file filename =
  (* let open Log in *)
  let file = open_in filename in
  let input = seq_of_channel file in
  let utf8_input = Unicode.Encoding.utf8_decode input in
  begin try
      begin try
          let lexer = Lexer.create utf8_input in
          let ast = Parse.specification lexer in
          ast
        with
        | Parse.Error (e, span) -> raise (Error (Parse (e, span)))
        (*| PolyTyper.Error (e, span) -> raise (Error (PolyType (e, span)))*)
        (*| MonoTyper.Error (e, span) -> raise (Error (MonoType (e, span)))
        | SubTyper.Error (e, span) -> raise (Error (SubType (e, span)))
          | RegularTyper.Error e -> raise (Error (RegularType e))*)
        (* | Runtime.Error e -> raise (Error (Runtime (e, span))) *)
      end
    with
    | Error e ->
      format_error utf8_input e Format.err_formatter;
      exit 1
  end

let full_parse_to_ast
    (s:string)
  : Ast.automaton Codemap.Span.located =
  List.hd (fst (process_file s)).spec_automata
