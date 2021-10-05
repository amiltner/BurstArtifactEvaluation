include Pattern.VARIABLE

val create : unit -> t

val of_int : int -> t

val fresh_of_int : int -> t
(* debug purpose only. *)

type namespace

val namespace : unit -> namespace

val spawn : namespace -> t

val spawn_int : namespace -> int
