module type S = sig
  module Encoding : Encoding.S

  type t = string

  val of_char : UChar.t -> t
  val length : t -> int
  val compare : t -> t -> int
  val push : UChar.t -> t -> t
  val fold_left : ('a -> UChar.t -> 'a) -> 'a -> t -> 'a
  val iter : (UChar.t -> unit) -> t -> unit
  val to_seq : t -> UChar.t Seq.t
end

module EncodingBase = Encoding

module Encoded (E: Encoding.S) = struct
  module Encoding = E

  type t = string

  let of_char c =
    let bytes = Encoding.encode c in
    let len = List.length bytes in
    let buffer = Bytes.create len in
    List.iteri (fun i byte -> Bytes.set buffer i byte) bytes;
    Bytes.to_string buffer

  let length = String.length

  let compare = String.compare

  let push c str =
    let bytes = Encoding.encode c in
    let len = List.length bytes in
    let offset = length str in
    let buffer = Bytes.create ((length str) + len) in
    List.iteri (fun i byte -> Bytes.set buffer (offset + i) byte) bytes;
    Bytes.blit_string str 0 buffer 0 (length str);
    Bytes.to_string buffer

  let to_seq str =
    EncodingBase.decode (module Encoding) (String.to_seq str)

  let fold_left f accu str =
    Seq.fold_left f accu (to_seq str)

  let iter f str =
    fold_left (fun () c -> f c) () str
end

module Utf8String = Encoded (Encoding.UTF8)
