module type S = sig
  type elt
  type t
  val create : int -> t
  val empty : unit -> t
  val add : elt -> t -> t
  val remove : elt -> t -> t
  val size : t -> int
  val is_empty : t -> bool
  val contains : elt -> t -> bool
  val fold : (elt -> 'b -> 'b) -> t -> 'b -> 'b
  val fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a
  val as_list : t -> elt list
  val iter : (elt -> unit) -> t -> unit
  val union : t -> t -> t
  val pp : (Format.formatter -> elt -> unit) -> Format.formatter -> t -> unit
  val update : (elt option -> unit) -> elt -> t -> t
end

module Make (K: HashTable.HashedType) : S with type elt = K.t
