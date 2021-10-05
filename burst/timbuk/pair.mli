module type S = sig
  type elt

  type t = elt * elt

  val symmetry : t -> t

  val compare : t -> t -> int

  val equal : t -> t -> bool

  val hash : t -> int

  val lhs : t -> elt

  val rhs : t -> elt

  val print : t -> Format.formatter -> unit
end
