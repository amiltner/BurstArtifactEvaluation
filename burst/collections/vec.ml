type 'a data = {
  mutable buffer: ('a option) array;
  mutable len: int;
}

type 'a undo =
  | Push
  | Pop of 'a
  | Set of int * 'a

type 'a vec =
  | Old of 'a t * 'a undo * int
  | Owned of 'a data

and 'a t = ('a vec) ref

let create capacity =
  let vec = Owned
      {
        buffer = Array.make capacity None;
        len = 0
      }
  in
  ref vec

let of_list l =
  let buffer = Array.of_list (List.map (function x -> Some x) l) in
  let vec = Owned
      {
        buffer = buffer;
        len = Array.length buffer
      }
  in
  ref vec

let length t =
  begin match !t with
    | Old (_, _, len) -> len
    | Owned data -> data.len
  end

let is_empty t = (length t) = 0

let expect opt msg =
  begin match opt with
    | Some x -> x
    | None -> raise (Invalid_argument msg)
  end

let unwrap = function
  | Some x -> x
  | None -> failwith "Malformed Vec"

let rec revert t =
  begin match !t with
    | Owned data -> {
        data with
        buffer = Array.copy data.buffer
      }
    | Old (t, _, _) ->
      let data = revert t in
      data.len <- data.len - 1;
      data
  end


let own t =
  begin match !t with
    | Owned data -> data
    | _ -> revert t
  end

let adjust data target_len =
  let new_capacity = ref (Array.length data.buffer) in
  while !new_capacity < target_len do
    new_capacity := !new_capacity * 2
  done;
  let new_buffer = Array.make !new_capacity None in
  Array.blit data.buffer 0 new_buffer 0 data.len;
  data.buffer <- new_buffer

let push x t =
  let data = own t in
  adjust data (data.len + 1);
  Array.set data.buffer data.len (Some x);
  data.len <- data.len + 1;
  let new_t = ref (Owned data) in
  t := Old (new_t, Push, data.len - 1);
  new_t

let pop_opt t =
  if is_empty t then
    None
  else begin
    let data = own t in
    data.len <- data.len - 1;
    let x = unwrap (Array.get data.buffer data.len) in
    Array.set data.buffer data.len None;
    let new_t = ref (Owned data) in
    t := Old (new_t, Pop x, data.len + 1);
    Some (new_t, x)
  end

let pop t = expect (pop_opt t) "Vec is empty"

let set_opt i x t =
  if length t <= i then
    None
  else begin
    let data = own t in
    let old_x = unwrap (Array.get data.buffer i) in
    Array.set data.buffer i (Some x);
    let new_t = ref (Owned data) in
    t := Old (new_t, Set (i, old_x), data.len);
    Some new_t
  end

let set i x t = expect (set_opt i x t) "Index out of bounds"

let rec get_opt i t =
  begin match !t with
    | Old (t, undo, len) ->
      if i < len then begin
        begin match undo with
          | Pop x when i = len - 1 -> Some x
          | Set (j, x) when i = j -> Some x
          | _ -> get_opt i t
        end
      end else None
    | Owned data ->
      if i < data.len then
        Array.get data.buffer i
      else
        None
  end

let get i t = expect (get_opt i t) "Index out of bounds"

let swap_opt i j t =
  begin match get_opt i t with
    | Some x ->
      begin match get_opt j t with
        | Some y -> Some (set i y (set j x t))
        | None -> None
      end
    | None -> None
  end

let swap i j t = expect (swap_opt i j t) "Index out of bounds"

let find_first_opt f t =
  let len = length t in
  let rec find i =
    if i >= len then None else
      let x = get i t in
      if f x then Some (x, i) else find (i + 1)
  in
  find 0

let find_first f t =
  begin match find_first_opt f t with
    | Some res -> res
    | None -> raise Not_found
  end

let find_last_opt f t =
  let len = length t in
  let rec find i =
    if i < 0 then None else
      let x = get i t in
      if f x then Some (x, i) else find (i - 1)
  in
  find (len - 1)

let find_last f t =
  begin match find_last_opt f t with
    | Some res -> res
    | None -> raise Not_found
  end
