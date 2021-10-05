module type S = sig
  module Encoding : Encoding.S

  type t = string

  val of_char : UChar.t -> t
  (** Create a string out of a char. *)

  val length : t -> int
  (** [length str] return the length of the string [str]. *)

  val compare : t -> t -> int
  (** [compare a b] compare the two strings [a] and [b]. *)

  val push : UChar.t -> t -> t
  (** [push c str] create a new string where [c] is added to the end of [str]. *)

  val fold_left : ('a -> UChar.t -> 'a) -> 'a -> t -> 'a
  (** [fold_left f accu str] folds the string [str] from the left. *)

  val iter : (UChar.t -> unit) -> t -> unit
  (** [iter f str] iterate the characters string [str] from the left. *)

  val to_seq : t -> UChar.t Seq.t
  (** [to_seq str] return [str] as a sequence of unicode characters. *)
end

module Encoded (E: Encoding.S) : S with module Encoding = E

module Utf8String : S with module Encoding = Encoding.UTF8
