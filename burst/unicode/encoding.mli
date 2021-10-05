module type S = sig
  val name : string

  val encode : UChar.t -> char list

  val decode : char Seq.t -> UChar.t * char Seq.t
end

val decode : (module S) -> char Seq.t -> UChar.t Seq.t

val encode : (module S) -> UChar.t Seq.t -> char Seq.t

exception InvalidEncoding of string

module UTF8 : S

val utf8_decode : char Seq.t -> UChar.t Seq.t

val utf8_encode : UChar.t Seq.t -> char Seq.t
