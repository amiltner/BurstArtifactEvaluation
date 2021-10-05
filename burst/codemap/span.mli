type t

val default : t

val first : t -> Position.t
(** [first span] get the position of the first character in the span. *)

val last : t -> Position.t
(** [last span] get the position of the last character in the span. *)

val next_position : t -> Position.t
(** [next_position span] return the position of the character directly following
    the span. It is not included in the span. *)

val push : Unicode.UChar.t -> t -> t

val next : t -> t

val union : t -> t -> t

val includes : t -> Position.t -> bool

val includes_line : t -> int -> bool

val is_included : t -> t -> bool
(** [is_included a b] checks if [b] is included in [a]. *)

val is_multi_line : t -> bool
(** [is_muli_line s] checks if [s] includes multiple lines. *)

val aligned : ?margin:int -> t -> t

val from_start : t -> t
(** Extends the span so it starts from the position 0. *)

val compare : t -> t -> int
(** [compare a b] compare two spans. *)

val print : t -> out_channel -> unit
(** [print span] format the span [span]. *)

val format : t -> Format.formatter -> unit
(** [format span] format the span [span]. *)

type 'a located = 'a * t
(** Type of located values. *)

val located : t -> 'a -> 'a located

val get : 'a located -> t
