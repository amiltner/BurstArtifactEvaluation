include Automaton.STATE

val of_string : string -> t

val string_opt : t -> string option

val equal: t -> t -> bool

val hash: t -> int
