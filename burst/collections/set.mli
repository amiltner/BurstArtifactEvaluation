module type OrderedType = Stdlib.Set.OrderedType

module type S = sig
  include Stdlib.Set.S

  val fold_pairs: ?reflexive:bool -> (elt -> elt -> 'a -> 'a) -> t -> 'a -> 'a

  val fold_pairs2: ?reflexive:bool -> (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a

  val fold_words : int -> (elt list -> 'a -> 'a) -> t -> 'a -> 'a
  (** [fold_words n f x t] fold all words of size [n] where [t] is the alphabet.
      Complexity: |t|^n.*)

  val fold_inline_combinations : (elt list -> 'a -> 'a) -> t list -> 'a -> 'a

  val fold_random: (elt -> 'a -> 'a) -> t -> 'a -> 'a

  val update : (elt option -> unit) -> elt -> t -> t
  (** Add an element to the set.
      update f x t.
      Calls f with Some e if equal e x = 0 and mem e, or with None. *)

  val search : (elt -> bool) -> t -> elt

  val search_opt : (elt -> bool) -> t -> elt option

  val fold2 : (elt -> elt -> 'a -> 'a) -> t -> t -> 'a -> 'a

  val iter2 : (elt -> elt -> unit) -> t -> t -> unit

  val product : (elt -> elt -> elt option) -> t -> t -> t

  val hash : t -> int

  val print : (elt -> Format.formatter -> unit) -> string -> t -> Format.formatter -> unit
end

module Make (E : OrderedType) : S with type elt = E.t and type t = Stdlib.Set.Make (E).t

module Ext (A : S) (B : S) : sig
  val map : (A.elt -> B.elt) -> A.t -> B.t

  val fold2 : (A.elt -> B.elt -> 'a -> 'a) -> A.t -> B.t -> 'a -> 'a

  val iter2 : (A.elt -> B.elt -> unit) -> A.t -> B.t -> unit
end

module Product (A : S) (B : S) (AB : S) : sig
  val product : (A.elt -> B.elt -> AB.elt option) -> A.t -> B.t -> AB.t
end
