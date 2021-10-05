module type TYPE = sig
  include Pattern.VARIABLE
end

type position = Term.position

type ('sym, 'ty) typed_term = ('sym, 'ty) value * 'ty

and ('sym, 'ty) value =
  | Term of 'sym * (('sym, 'ty) typed_term) list
  | Cast of ('sym, 'ty) typed_term

module type S = sig
  module Sym : Symbol.S
  module Type : TYPE

  type ('sym, 'ty) abs_value = ('sym, 'ty) value =
    | Term of 'sym * (('sym, 'ty) typed_term) list
    | Cast of ('sym, 'ty) typed_term

  type term = Sym.t Term.term
  type t = (Sym.t, Type.t) typed_term

  (** This is raised when the tem is malformed.
      For instance if the subterms count mismatch the constuctor arity. *)
  exception MalformedTerm

  exception InvalidPosition of position * t

  val create : Sym.t -> t list -> Type.t -> t

  val subterm : position -> t -> t

  val subterm_opt : position -> t -> t option

  val size : t -> int

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val product : t -> t -> t option

  val hash : t -> int

  val strip : t -> term

  val print : t -> Format.formatter -> unit
end

module Make (F : Symbol.S) (Type : TYPE) : S with module Sym = F and module Type = Type
