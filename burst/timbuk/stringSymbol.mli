type t

module Id : sig
	type t = string

	val compare : t -> t -> int
end

(** Create a symbol from its name and arity. *)
val create : string -> int -> t

(** Get the id (name) of the symbol *)
val id : t -> Id.t

val arity : t -> int

(** Get the name of the symbol. *)
val name : t -> string

val compare : t -> t -> int

val equal : t -> t -> bool

val hash : t -> int

val print : t -> Format.formatter -> unit
