type t = {
  first: Position.t;
  last: Position.t;
  next: Position.t
}

let default =
  {
    first = Position.default;
    last = Position.default;
    next = Position.default
  }

let first t = t.first

let last t = t.last

let next_position t = t.next

let push c t =
  {
    t with
    last = t.next;
    next = Position.next c t.next
  }

let next t =
  {
    first = t.next;
    last = t.next;
    next = t.next
  }

let is_empty t =
  t.first == t.next

let union a b =
  if is_empty a then b else
  if is_empty b then a else
  if (Position.compare b.last a.last > 0) && (Position.compare b.next a.next > 0) then
    {
      first = Position.min a.first b.first;
      last = b.last;
      next = b.next
    }
  else
    {
      first = Position.min a.first b.first;
      last = a.last;
      next = a.next
    }

let includes_line t l =
  t.first.line <= l && t.last.line >= l

let includes t pos =
  includes_line t pos.Position.line &&
  (t.first.line != pos.line || pos.column >= t.first.column) &&
  (t.last.line != pos.line || pos.column <= t.last.column)

let is_multi_line s =
  s.first.line != s.last.line

let is_included a b =
  Position.compare a.first b.first <= 0 && Position.compare a.next b.last > 0

let aligned ?(margin=0) t =
  {
    first = {
      line = (max 0 (t.first.line - margin));
      column = 0
    };
    last = {
      line = t.next.line + margin;
      column = max_int - 1
    };
    next = {
      line = t.next.line + margin;
      column = max_int
    }
  }

let from_start t =
  { t with first = Position.default }

let compare a b =
  let c = Position.compare a.first b.first in
  if c = 0 then Position.compare b.last a.last (* the inversion is intended. *)
  else c

let print t fmt =
  if t.first = t.last then
    Position.print t.first fmt
  else if t.first.line = t.last.line then
    Printf.fprintf fmt "line %d columns %d to %d" (t.first.line + 1) (t.first.column + 1) (t.last.column + 1)
  else
    Printf.fprintf fmt "%t to %t" (Position.print t.first) (Position.print t.last)

let format t fmt =
  if t.first = t.last then
    Position.format t.first fmt
  else if t.first.line = t.last.line then
    Format.fprintf fmt "line %d columns %d to %d" (t.first.line + 1) (t.first.column + 1) (t.last.column + 1)
  else
    Format.fprintf fmt "%t to %t" (Position.format t.first) (Position.format t.last)

type 'a located = 'a * t

let located span x = x, span

let get (_, span) = span
