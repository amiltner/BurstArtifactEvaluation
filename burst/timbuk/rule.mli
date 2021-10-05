module type S = Pair.S

module Make (Ord : Symbol.ORDERED_FORMAT_TYPE) : S with type elt = Ord.t
