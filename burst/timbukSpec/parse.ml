open Unicode
open Codemap
open Lexer
open Ast
open Collections

type error =
  | Unexpected of Lexer.token option * TokenKind.t list

exception Error of error Span.located

let consume span lexer =
  begin match lexer () with
    | Seq.Nil -> (span, Seq.Nil)
    | Seq.Cons ((token, token_span), lexer') ->
      let span = Span.union span token_span in
      (span, Seq.Cons ((token, token_span), lexer'))
  end

let expect span lexer =
  begin match consume span lexer with
    | _, Seq.Nil -> raise (Error (Unexpected (None, []), Span.next span))
    | span', Seq.Cons (token, lexer') -> (span', token, lexer')
  end

let unexpected (token, span) expected =
  raise (Error (Unexpected (Some token, expected), span))

let rev (l, span) =
  List.rev l, span

module SeqThen = struct
  type ('a, 'b) node =
    | Nil of 'b
    | Cons of 'a * ('a, 'b) t

  and ('a, 'b) t = unit -> ('a, 'b) node

  let rec fold_left f accu t =
    match t () with
    | Nil b -> accu, b
    | Cons (a, t') -> fold_left f (f accu a) t'
end

let ops lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Ident id, id_span), lexer) ->
        begin match expect span lexer with
          | (span, (Token.Punct c, _), lexer) when c = UChar.of_ascii ':' ->
            begin match expect span lexer with
              | (span, (Token.Int arity, arity_span), lexer) ->
                let sym = {
                  sym_name = Span.located id_span id;
                  sym_arity = Span.located arity_span arity
                }
                in
                SeqThen.Cons (Span.located span sym, next lexer)
              | (_, token, _) -> unexpected token [TokenKind.Int]
            end
          | (_, token, _) -> unexpected token [TokenKind.Punct (UChar.of_ascii ':')]
        end
      | _, Seq.Cons (_, _) -> SeqThen.Nil lexer
      | _, Seq.Nil -> SeqThen.Nil lexer
    end
  in
  next lexer

let ops_section lexer =
  begin match expect Span.default lexer with
    | (span, (Token.Keyword Keyword.Ops, _), lexer) ->
      SeqThen.fold_left (
        fun (alphabet, span) (f, f_span) ->
          (f, f_span)::alphabet, (Span.union span f_span)
      ) ([], Span.default) (ops lexer)
    | (_, token, _) -> unexpected token [TokenKind.Keyword Keyword.Ops]
  end

let vars lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Ident id, id_span), lexer) ->
        let var = {
          var_name = Span.located id_span id
        }
        in
        SeqThen.Cons (Span.located span var, next lexer)
      | _, Seq.Cons (_, _) -> SeqThen.Nil lexer
      | _, Seq.Nil -> SeqThen.Nil lexer
    end
  in
  next lexer

let vars_section lexer =
  begin match expect Span.default lexer with
    | (span, (Token.Keyword Keyword.Vars, _), lexer) ->
      SeqThen.fold_left (
        fun (variables, span) (x, x_span) ->
          (x, x_span)::variables, (Span.union span x_span)
      ) ([], Span.default) (vars lexer)
    | (_, token, _) -> unexpected token [TokenKind.Keyword Keyword.Vars]
  end

type section =
  | Automaton of Ast.automaton

let rec term span lexer =
  begin match expect span lexer with
    | (span, (Token.Ident id, id_span), lexer) ->
      let subs, span, lexer = match consume span lexer with
        | span, Seq.Cons ((Token.Begin d, subs_span), lexer) ->
          let (subs, subs_span), lexer = SeqThen.fold_left (
              fun (subs, span) (sub, sub_span) ->
                (sub, sub_span)::subs, (Span.union span sub_span)
            ) ([], subs_span) (sub_terms lexer)
          in
          let subs_span, lexer = match expect subs_span lexer with
            | (subs_span, (Token.End d', _), lexer) when d = d' ->
              subs_span, lexer
            | (_, token, _) -> unexpected token [TokenKind.End d]
          in
          (List.rev subs, subs_span), (Span.union subs_span span), lexer
        | _ -> ([], Span.next id_span), span, lexer
      in
      let ty, span, lexer = match consume span lexer with
        | span, Seq.Cons ((Token.Punct p, _), lexer) when p = UChar.of_ascii ':' ->
          begin match expect span lexer with
            | (span, (Token.Ident ty, ty_span), lexer) ->
              Some (ty, ty_span), span, lexer
            | (_, token, _) -> unexpected token [TokenKind.Punct (UChar.of_ascii ':')]
          end
        | _ -> None, span, lexer
      in
      let term = {
        term_cons = Span.located id_span id;
        term_subs = subs;
        term_type = ty
      }, span
      in
      term, lexer
    | (_, token, _) -> unexpected token [TokenKind.Ident]
  end

and sub_terms lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Ident _, _), _) ->
        let term, lexer = term span lexer in
        SeqThen.Cons (term, next lexer)
      | _, Seq.Cons ((Token.Punct p, _), lexer) when p = UChar.of_ascii ',' ->
        next lexer ()
      | _ -> SeqThen.Nil lexer
    end
  in
  next lexer

let source_patterns lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Ident _, _), _) ->
        let term, lexer = term span lexer in
        let span, target_type, lexer = match consume Span.default lexer with
          | _, Seq.Cons ((Token.RegularCast, _), lexer) ->
            begin match expect Span.default lexer with
              | type_span, (Token.Ident id, _), lexer ->
                let span = Span.union (snd term) type_span in
                span, Some (id, type_span), lexer
              | _, token, _ -> unexpected token [TokenKind.Ident]
            end
          | _ -> (snd term), None, lexer
        in
        let source_pattern = {
          src_pattern = term;
          src_target_type = target_type
        } in
        SeqThen.Cons ((source_pattern, span), next lexer)
      | _, Seq.Cons ((Token.Punct p, _), lexer) when p = UChar.of_ascii ',' ->
        next lexer ()
      | _ -> SeqThen.Nil lexer
    end
  in
  next lexer

let rules lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Ident _, _), _) ->
        let left, lexer = term span lexer in
        begin match expect (Span.next (snd left)) lexer with
          | (_, (Token.Arrow, arr_span), lexer) ->
            let right, lexer = term (Span.next arr_span) lexer in
            let span = Span.union (snd left) (snd right) in
            let rule = { rule_left = left; rule_right = right }, span in
            SeqThen.Cons (rule, next lexer)
          | (_, token, _) -> unexpected token [TokenKind.Arrow]
        end
      | _ -> SeqThen.Nil lexer
    end
  in
  next lexer

let states lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Ident id, id_span), lexer) ->
        let q = {
          state_name = Span.located id_span id
        }
        in
        SeqThen.Cons (Span.located span q, next lexer)
      | _, Seq.Cons (_, _) -> SeqThen.Nil lexer
      | _, Seq.Nil -> SeqThen.Nil lexer
    end
  in
  next lexer

let opt_sections lexer =
  let rec next lexer () =
    begin match consume Span.default lexer with
      | span, Seq.Cons ((Token.Keyword Keyword.Automaton, _), lexer) ->
        begin match expect span lexer with
          | (span, (Token.Ident id, id_span), lexer) ->
            begin match expect span lexer with
              | (span, (Token.Keyword Keyword.States, _), lexer) ->
                let aut_states, lexer = SeqThen.fold_left (
                    fun (states, span) (q, q_span) ->
                      (q, q_span)::states, (Span.union span q_span)
                  ) ([], Span.default) (states lexer)
                in
                let span = Span.union span (snd aut_states) in
                begin match expect span lexer with
                  | (span, (Token.Keyword Keyword.Final, _), lexer) ->
                    begin match expect span lexer with
                      | (span, (Token.Keyword Keyword.States, _), lexer) ->
                        let final_states, lexer = SeqThen.fold_left (
                            fun (states, span) (q, q_span) ->
                              (q, q_span)::states, (Span.union span q_span)
                          ) ([], Span.default) (states lexer)
                        in
                        let span = Span.union span (snd final_states) in
                        begin match expect span lexer with
                          | (span, (Token.Keyword Keyword.Transitions, _), lexer) ->
                            let transitions, lexer = SeqThen.fold_left (
                                fun (rules, span) (rule, rule_span) ->
                                  (rule, rule_span)::rules, (Span.union span rule_span)
                              ) ([], Span.next id_span) (rules lexer)
                            in
                            let span = Span.union span (snd transitions) in
                            let aut = {
                              aut_name = Span.located id_span id;
                              aut_states = rev aut_states;
                              aut_roots = final_states;
                              aut_transitions = transitions
                            }
                            in
                            Seq.Cons ((Automaton aut, span), next lexer)
                          | (_, token, _) -> unexpected token [TokenKind.Keyword Keyword.Transitions]
                        end
                      | (_, token, _) -> unexpected token [TokenKind.Keyword Keyword.States]
                    end
                  | (_, token, _) -> unexpected token [TokenKind.Keyword Keyword.Final]
                end
              | (_, token, _) -> unexpected token [TokenKind.Keyword Keyword.States]
            end
          | (_, token, _) -> unexpected token [TokenKind.Ident]
        end
      | _, Seq.Cons (token, _) -> unexpected token [
          TokenKind.Keyword Keyword.TRS;
          TokenKind.Keyword Keyword.Automaton;
          TokenKind.Keyword Keyword.Patterns
        ]
      | _, Seq.Nil -> Seq.Nil
    end
  in
  next lexer

let specification lexer =
  let alphabet, lexer = ops_section lexer in
  let spec = {
    spec_alphabet = rev alphabet;
    spec_automata = [];
  }
  in
  let span = (snd alphabet) in
  let spec = Seq.fold_left (
      fun (spec, span) (section, section_span) ->
        let spec = match section with
          | Automaton aut -> { spec with spec_automata = (Span.located section_span aut) :: spec.spec_automata }
        in
        spec, Span.union span section_span
    ) (spec, span) (opt_sections lexer)
  in
  spec

let print_error e fmt =
  match e with
  | Unexpected (Some token, []) ->
    Format.fprintf fmt "unexpected %t" (Lexer.Token.debug token)
  | Unexpected (Some token, [k]) ->
    Format.fprintf fmt "unexpected %t, expect %t" (Lexer.Token.debug token) (Lexer.TokenKind.print k)
  | Unexpected (Some token, ks) ->
    Format.fprintf fmt "unexpected %t, expect one of %t" (Lexer.Token.debug token) (List.print (Lexer.TokenKind.print) ", " ks)
  | Unexpected (None, _) ->
    Format.fprintf fmt "unexpected end of file"
