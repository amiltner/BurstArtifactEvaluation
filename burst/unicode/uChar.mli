type t = Uchar.t
(** Unicode character scalar value.
    It is the same has the standard library [UChar.t]. *)

val is_valid : int -> bool

val of_int : int -> t
(** [of_int i] create a character from the given scalar value. *)

val to_int : t -> int
(** [to_int c] return the integer scalar value of [c]. *)

val of_ascii : char -> t
(** [of_ascii] create a character from the given ascii char. *)

val is_ascii : t -> bool
(** [is_ascii c] return [true] is [c] is an ASCII character, and [false] if not. *)

val is_alphabetic : t -> bool
(** [is_alphabetic c] return [true] if [c] is an alphabetic code point, and [false] if not. *)

val is_numeric : t -> bool

val is_alphanumeric : t -> bool

val is_control : t -> bool
(** [is_control c] return [true] if [c] is a control code point, and [false] if not. *)

val is_digit : int -> t -> bool
(** [is_digit radix c] checks if [c] is a digit in the given [radix]. *)

val is_whitespace : t -> bool
(** [is_space c] checks if [c] is a whitespace character. *)

val tab_length : ?tab_stop:int -> int -> int
(** Get the tab length at the given position. *)

val width : ?tab_stop:int -> int -> t -> int
(** [width ?tab_stop col c] return the number of columns needed to draw [c] when
    it occurs at the column [col].
    Control characters are of width 0.
    The width of the tabulation character dependes on [col] and [tab_stop]:
    it can be from 1 to [tab_stop].
    This function raise an [Invalid_argument] if [tab_stop] is not strictly
    positive. *)

val to_ascii : t -> char
(** [to_ascii c] try to convert the given character [c] into an ASCII [char]. *)

val to_ascii_opt : t -> char option
(** [to_ascii c] try to convert the given character [c] into an ASCII [char]. *)

val to_digit : int -> t -> int
(** [to_digit radix c] try to convert the given character [c] into a digit in the given [radix]. *)

val to_digit_opt : int -> t -> int option
(** [to_digit radix c] try to convert the given character [c] into a digit in the given [radix]. *)
