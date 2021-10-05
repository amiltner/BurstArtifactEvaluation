module type S = sig
  type ord

  include Set.S with type elt = ord * ord

  val of_list : elt list -> t

  (** Get the list of all left sides. *)
  val left_sides : t -> ord list

  (** Get the list of all right sides. *)
  val right_sides : t -> ord list

  (** Get all the right sides of a left side. *)
  val rights_of : ord -> t -> ord list

  (** Get all the left sides of a right side. *)
  val lefts_of : ord -> t -> ord list

  val compare : t -> t -> int

  val print : t -> Format.formatter -> unit
end

module Make (Ord : Symbol.ORDERED_FORMAT_TYPE) (Pair : Pair.S with type elt = Ord.t)
  : S with type ord = Ord.t
