open Timbuk

include Automaton.STATE

val create : unit -> t

val of_string : string -> t

val string_opt : t -> string option

val equal: t -> t -> bool

val hash: t -> int
val hash_fold_t: t Base.Hash.folder
