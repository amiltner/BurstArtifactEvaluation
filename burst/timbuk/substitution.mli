open Collections

module type S = sig
  include Map.S

  val union : ('a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t

  val union_opt : ('a -> 'a -> 'a option) -> 'a t -> 'a t -> 'a t option
end

module Make (X : Map.OrderedType) : S with type key = X.t
