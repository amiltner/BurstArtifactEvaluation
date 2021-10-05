module type ORDERED_FORMAT_TYPE = sig
  include Set.OrderedType

  val equal : t -> t -> bool

  val hash : t -> int

  val hash_fold_t : Base__Hash.state -> t -> Base__Hash.state

  val print : t -> Format.formatter -> unit
end

module type S = sig
  include ORDERED_FORMAT_TYPE

  val arity : t -> int
end
