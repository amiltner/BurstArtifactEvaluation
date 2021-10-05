open Unicode

type t

val of_seq : UChar.t Seq.t -> t
(** Create a buffer from an input char sequence. *)

val get : t -> int -> UChar.t
(** Get the char at the given position, or raise End_of_file. *)

val to_seq : t -> UChar.t Seq.t
(** Make a sequence out of a buffer. *)

val to_seq_from : t -> int -> UChar.t Seq.t
(** Make a sequence out of a buffer, starting from the given index. *)

val to_seq_from_position : t -> Position.t -> UChar.t Seq.t
(** Make a sequence out of a buffer, starting from the given cursor position. *)
