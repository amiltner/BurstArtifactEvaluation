type position =
  | Root
  | Subterm of int * position

type 'sym term =
  | Term of 'sym * ('sym term) list

val equal_term : ('sym -> 'sym -> bool) -> 'sym term -> 'sym term -> bool
val compare_term : ('sym -> 'sym -> int) -> 'sym term -> 'sym term -> int

val hash_fold_term : 'a Base.Hash.folder -> 'a term Base.Hash.folder

module type S = sig
  module Sym : Symbol.S

  type 'sym abs_term = 'sym term =
    | Term of 'sym * ('sym term) list

  type t = Sym.t term

  exception MalformedTerm
  (** This is raised when the tem is malformed.
      For instance if the subterms count mismatch the constuctor arity. *)

  exception InvalidPosition of position * t

  val create : Sym.t -> t list -> t

  val subterm : position -> t -> t

  val subterm_opt : position -> t -> t option

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int

  val print : t -> Format.formatter -> unit
end

module Make (S: Symbol.S) : S with module Sym = S
