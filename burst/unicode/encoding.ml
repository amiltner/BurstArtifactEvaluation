module type S = sig
  val name : string
  val encode : UChar.t -> char list
  val decode : char Seq.t -> UChar.t * char Seq.t
end

let encode (encoding : (module S)) input =
  let module Encoding = (val encoding) in
  let rec next input () =
    match input () with
    | Seq.Nil -> Seq.Nil
    | Seq.Cons (c, input') ->
      let rec next_byte bytes () =
        match bytes with
        | [] -> next input' ()
        | b::bytes' ->
          Seq.Cons (b, next_byte bytes')
      in
      let bytes = Encoding.encode c in
      next_byte bytes ()
  in
  next input

let decode (encoding : (module S)) input =
  let module Encoding = (val encoding) in
  let rec next input () =
    try
      let c, input' = Encoding.decode input in
      Seq.Cons (c, next input')
    with
    | End_of_file -> Seq.Nil
  in
  next input

exception InvalidEncoding of string

module UTF8 = struct
  let name = "UTF-8"

  let encode c =
    match UChar.to_int c with
    | i when i < 0x80 ->
      [Char.chr i]
    | _ -> failwith "UTF-8: encoding is yet TODO."

  let decode (input : char Seq.t) =
    let next_byte input =
      match input () with
      | Seq.Nil -> raise (InvalidEncoding "unexpected end of UTF-8 sequence.")
      | Seq.Cons (byte, input') ->
        Char.code byte, input'
    in
    begin match input () with
      | Seq.Nil -> raise End_of_file
      | Seq.Cons (byte, input') ->
        begin match Char.code byte with
          | a when (a land 0x80) = 0x00 ->
            UChar.of_int a, input'
          | a when (a land 0xe0) = 0xc0 ->
            let b, input' = next_byte input' in
            UChar.of_int (((a land 0x1f) lsl 6) lor b), input'
          | a when (a land 0xf0) = 0xe0 ->
            let b, input' = next_byte input' in
            let c, input' = next_byte input' in
            UChar.of_int (((a land 0x0f) lsl 12) lor (b lsl 6) lor c), input'
          | a when (a land 0xf8) = 0xf0 ->
            let b, input' = next_byte input' in
            let c, input' = next_byte input' in
            let d, input' = next_byte input' in
            UChar.of_int (((a land 0x07) lsl 18) lor (b lsl 12) lor (c lsl 6) lor d), input'
          | _ ->
            raise (InvalidEncoding "invalid UTF-8 sequence.")
        end
    end
end

let utf8_decode = decode (module UTF8)

let utf8_encode = encode (module UTF8)
