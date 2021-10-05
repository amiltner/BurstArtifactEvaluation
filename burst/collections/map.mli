module type OrderedType = Stdlib.Map.OrderedType

module type S =
sig
	include Stdlib.Map.S

  val map_bindings : (key -> 'a -> key * 'b) -> ('b -> 'b -> 'b option) -> 'a t -> 'b t

  val fold_pairs: ?reflexive:bool -> (key -> 'a -> key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  (** Fold pairs of bindings. If [reflexive] is true, include pairs of the same binding. By default [reflexive] is false. *)

  val fold2 : (key -> 'a -> key -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c

  val product : (key -> 'a -> key -> 'b -> (key * 'c) option) -> 'a t -> 'b t -> 'c t

  val hash : 'a t -> int

  val fold_combinations : ('b t -> 'c -> 'c) -> 'a t -> (('b -> 'c -> 'c) -> 'a -> 'c -> 'c) -> 'c -> 'c
end

module Make (K : OrderedType) : S with type key = K.t and type +'a t = 'a Stdlib.Map.Make (K).t

module Ext (A : S) (B : S) : sig
  val map : (A.key -> 'a -> B.key * 'b) -> ('b -> 'b -> 'b option) -> 'a A.t -> 'b B.t

  val fold2 : (A.key -> 'a -> B.key -> 'b -> 'c -> 'c) -> 'a A.t -> 'b B.t -> 'c -> 'c
end

module Product (A : S) (B : S) (AB : S) : sig
  val product : (A.key -> 'a -> B.key -> 'b -> (AB.key * 'c) option) -> 'a A.t -> 'b B.t -> 'c AB.t
end
