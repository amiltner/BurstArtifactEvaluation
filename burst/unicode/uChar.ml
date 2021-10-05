type t = Uchar.t
(** Unicode character scalar value.
    It is the same has the standard library [Uchar.t]. *)

let is_between c min max =
  c >= min && c <= max

let is_valid = Uchar.is_valid

let of_int = Uchar.of_int

let to_int = Uchar.to_int

let of_ascii = Uchar.of_char

let is_ascii t =
  let c = Uchar.to_int t in
  is_between c 0x00 0xff

let is_alphabetic t =
  let c = Uchar.to_int t in
  (is_between c 0x41 0x5a) || (is_between c 0x61 0x7a) || (c > 0x7f && failwith "not implemented for non-ASCII chars.")

let is_numeric t =
  let c = Uchar.to_int t in
  (is_between c 0x30 0x39) || (c > 0x7f && failwith "not implemented for non-ASCII chars.")

let is_alphanumeric t =
  is_alphabetic t || is_numeric t

let is_control t =
  let c = Uchar.to_int t in
  (is_between c 0x00 0x1f) || (c = 0x7f) || (c > 0x7f && failwith "not implemented for non-ASCII chars.")

let is_whitespace t =
  let c = Uchar.to_int t in
  (c = 0x20) || (is_between c 0x09 0x0d) || (c > 0x7f && failwith "not implemented for non-ASCII chars.")

let tab_length ?(tab_stop=8) col =
  if tab_stop <= 0 then raise (Invalid_argument "tab stop length must be strictly positive");
  if col < 0 then -col else
    tab_stop - (col mod tab_stop)

let width ?(tab_stop=8) col t =
  let i = to_int t in
  begin match i with
    | 0x09 (* \t *) ->
      col + (tab_length ~tab_stop col)
    | _ when is_control t -> 0
    | _ -> 1 (* TODO multi column chars are not handled yet. *)
  end

let to_ascii t =
  Uchar.to_char t

let to_ascii_opt t =
  begin try Some (to_ascii t) with
    | Invalid_argument _ -> None
  end

let to_digit radix t =
  let c = Uchar.to_int t in
  let value =
    if radix <= 10
    then
      begin
        if is_between c 0x30 0x39
        then c - 0x30
        else raise (Invalid_argument "Not a digit")
      end
    else
      begin if is_between c 0x30 0x39
        then c - 0x30
        else begin if is_between c 0x41 0x5a
          then c - 0x41 + 10
          else begin if is_between c 0x61 0x7a
            then c - 0x61 + 10
            else raise (Invalid_argument "Not a digit")
          end
        end
      end
  in
  if value < radix
  then value
  else raise (Invalid_argument "Not a digit")

let to_digit_opt radix t =
  begin try Some (to_digit radix t) with
    | Invalid_argument _ -> None
  end

let is_digit radix t =
  match to_digit_opt radix t with
  | Some _ -> true
  | None -> false
