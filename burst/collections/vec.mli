type 'a t

val create : int -> 'a t
(** Create a vector with the given capacity *)

val of_list : 'a list -> 'a t

val length : 'a t -> int

val is_empty : 'a t -> bool

val push : 'a -> 'a t -> 'a t

val pop_opt : 'a t -> ('a t * 'a) option

val pop : 'a t -> ('a t * 'a)

val get_opt : int -> 'a t -> 'a option

val get : int -> 'a t -> 'a

val set_opt : int -> 'a -> 'a t -> ('a t) option

val set : int -> 'a -> 'a t -> 'a t

val swap_opt : int -> int -> 'a t -> ('a t) option

val swap : int -> int -> 'a t -> 'a t

val find_first_opt : ('a -> bool) -> 'a t -> ('a * int) option

val find_first : ('a -> bool) -> 'a t -> 'a * int

(** Starts the search from the end *)
val find_last_opt : ('a -> bool) -> 'a t -> ('a * int) option

val find_last : ('a -> bool) -> 'a t -> 'a * int
