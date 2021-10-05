include module type of Stdlib.List

val compare : ('a -> 'a -> int) -> 'a t -> 'a t -> int
(* Lexicographic order over lists. *)

val equal : ('a -> 'a -> bool) -> 'a t -> 'a t -> bool
(* Check equality with the given element equality operator.
   Alias of [for_all2].*)

val map_opt : ('a -> 'b option) -> 'a t -> 'b t option

val map2_opt : ('a -> 'b -> 'c option) -> 'a t -> 'b t -> 'c t option

val transpose : ('a t -> 'b) -> 'a t t -> 'b t
(** Transposition of a list of list.
    [transpose l] compute the transposition
    [[f [a11, ..., an1], ..., f [a1m, ..., anm]]] of the list [l] where it is
    equal to [[[a11, ..., a1m], ..., [an1, ... anm]]]. *)

val inner_fold2 : ('d t -> 'c -> 'c) -> (('d -> 'c -> 'c) -> 'a -> 'b -> 'c -> 'c) -> 'a t -> 'b t -> 'c -> 'c


val fold_inline_combinations : ('a t -> 'b -> 'b) -> ('a t) t -> 'b -> 'b
(** [List.fold_inline_combinations f l c] fold all the combinations of the form
    [e1, ..., en] where each element [ei] is choosed from the list
    [List.nth l i]. *)

val fold_bool_combinations : (bool t -> 'a -> 'a) -> int -> 'a -> 'a
(** [fold_bool_combinations f n] fold all the combinations of [n] booleans. *)

val print : ('a -> Format.formatter -> unit) -> string -> 'a list -> Format.formatter -> unit
