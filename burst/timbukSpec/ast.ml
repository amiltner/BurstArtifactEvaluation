open Codemap

type symbol = {
  sym_name : string Span.located;
  sym_arity : int Span.located
}

type variable = {
  var_name : string Span.located
}

(** A pattern represents a term with variables. *)
type term = {
  term_cons : string Span.located;
  term_subs : (term Span.located) list Span.located;
  term_type : (string Span.located) option
}

type rule = {
  rule_left : term Span.located;
  rule_right : term Span.located
}

type state = {
  state_name : string Span.located
}

type automaton = {
  aut_name : string Span.located;
  aut_states : (state Span.located) list Span.located;
  aut_roots : (state Span.located) list Span.located;
  aut_transitions : rule Span.located list Span.located
}

type trs = {
  trs_name : string Span.located;
  trs_rules : (rule Span.located) list Span.located
}

type source_pattern = {
  src_pattern: term Span.located;
  src_target_type: string Span.located option
}

type pattern_set = {
  pset_name : string Span.located;
  pset_patterns : (source_pattern Span.located) list Span.located;
  pset_type_system : string Span.located option
}

type specification = {
  spec_alphabet : (symbol Span.located) list Span.located;
  spec_automata : (automaton Span.located) list;
}
