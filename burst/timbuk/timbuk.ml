(** Timbuk

    [Timbuk] provides tree terms, patterns, tree automata and term rewriting system.

*)

(** {1 Terms and patterns} *)

module Symbol = Symbol

(** {2 Untyped} *)

module Term = Term

module Pattern = Pattern

(** {2 Typed} *)

module TypedTerm = TypedTerm

module TypedPattern = TypedPattern

(** {2 Substitutions} *)

module Substitution = Substitution

(** {2 Helpers} *)

module StringSymbol = StringSymbol

module Var = Var

(** {1 Tree automata} *)

module Automaton = Automaton

(** {2 Helpers} *)

module IntState = IntState

module StringState = StringState

(** {1 Term rewriting systems} *)

module Relation = Relation

module Pair = Pair

module Equation = Equation

module Rule = Rule
