include Automaton.STATE

val create : unit -> t

val of_int : int -> t

val int_opt : t -> int option

val equal: t -> t -> bool

val hash: t -> int
