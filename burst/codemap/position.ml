open Unicode

type t = {
  line: int;
  column: int
}

let default =
  {
    line = 0;
    column = 0
  }

let create line column =
  {
    line = line;
    column = column
  }

let last =
  {
    line = max_int;
    column = max_int
  }

let next_column p =
  { p with column = p.column + 1 }

let reset_column p =
  { p with column = 0 }

let next_line p =
  {
    line = p.line + 1;
    column = 0
  }

let tab_length p =
  UChar.tab_length p.column

let next c p =
  let i = UChar.to_int c in
  begin match i with
    | 0x0a (* \n *) -> next_line p
    | 0x0d (* \r *) -> reset_column p
    | _ -> { p with column = p.column + (UChar.width p.column c) }
  end

let compare a b =
  let c = compare a.line b.line in
  if c = 0 then
    compare a.column b.column
  else c

let min a b =
  if compare a b > 0 then b else a

let max a b =
  if compare a b > 0 then a else b

let print_tab p fmt =
  let rec print = function
    | 0 -> ()
    | n ->
      output_char fmt ' ';
      print (n - 1)
  in
  print (tab_length p)

let print p fmt =
  Printf.fprintf fmt "line %d column %d" (p.line+1) (p.column+1)

let print_short p fmt =
  Printf.fprintf fmt "%d:%d" (p.line+1) (p.column+1)

let format p fmt =
  Format.fprintf fmt "line %d column %d" (p.line+1) (p.column+1)

let format_short p fmt =
  Format.fprintf fmt "%d:%d" (p.line+1) (p.column+1)
