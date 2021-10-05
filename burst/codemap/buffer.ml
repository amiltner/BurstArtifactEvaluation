open Unicode

type t = {
  mutable input: UChar.t Seq.t;
  (** Input stream. *)

  mutable data: UChar.t Array.t;
  (** The actual buffer. *)

  mutable length: int;
  (** The length of the buffer. *)

  mutable indexes: int Array.t;
  (** Stores the index of the first character of each line. *)

  mutable pos: Position.t
  (** The position of the end of the buffer. *)
}

let of_seq input =
  {
    input = input;
    data = Array.make 128 (UChar.of_int 0);
    length = 0;
    indexes = Array.make 8 0;
    pos = Position.default
  }

(** Bufferize the next in the input stream. *)
let grow t =
  match t.input () with
  | Seq.Cons (c, input') ->
    t.input <- input';
    let i = t.length in
    t.length <- t.length + 1;
    let capacity = Array.length t.data in
    if t.length > capacity then begin
      (* Double the capacity. *)
      let data' = Array.make (capacity * 2) (UChar.of_int 0) in
      Array.blit t.data 0 data' 0 capacity;
      t.data <- data'
    end;
    Array.set t.data i c;
    let pos' = Position.next c t.pos in
    if pos'.line > t.pos.line then begin
      let capacity = Array.length t.indexes in
      if capacity <= pos'.line then begin
        (* Double the capacity. *)
        let indexes' = Array.make (capacity * 2) 0 in
        Array.blit t.indexes 0 indexes' 0 capacity;
        t.indexes <- indexes'
      end;
      Array.set t.indexes pos'.line (i+1)
    end;
    t.pos <- pos'
  | Seq.Nil ->
    raise End_of_file

let get t i =
  while t.length <= i do
    grow t
  done;
  Array.get t.data i

let get_opt t i =
  try Some (get t i) with
  | End_of_file -> None

let to_seq_from t i =
  let rec next i () =
    match get_opt t i with
    | Some c ->
      Seq.Cons (c, next (i + 1))
    | None ->
      Seq.Nil
  in
  next i

let to_seq t =
  to_seq_from t 0

let index_of_line t l =
  while t.pos.line < l do
    grow t
  done;
  Array.get t.indexes l

let index_of_position t pos =
  let i = index_of_line t pos.Position.line in
  let rec index_of_column i current_pos =
    if current_pos.Position.line > pos.line then raise Not_found;
    if current_pos.column >= pos.column then
      i
    else
      let c = get t i in
      index_of_column (i + 1) (Position.next c current_pos)
  in
  index_of_column i (Position.create pos.line 0)

let to_seq_from_position t pos =
  let i = index_of_position t pos in
  to_seq_from t i
