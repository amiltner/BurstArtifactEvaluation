open MyStdLib

type 'a g = int -> 'a option

let _ = Random.init 0

let rec choice (gs : 'a g list) : 'a g =
  let len = List.length gs in
  if len = 0 then
    (fun _ -> None)
  else
    let i = Random.int len in
    let base_g = List.nth_exn gs i in
    let g (s:int) : 'a option =
      let a_o = base_g s in
      if Option.is_some a_o then
        a_o
      else
        let gs = remove_at_exn gs i
         in (choice gs) s
     in g

let subtract_size (type a) (g : a g) (m : int) : a g =
  let subtracted_gen (s:int) : a option =
    let new_size = s - m
     in if new_size < 1 then None
                        else g (s-m)
   in subtracted_gen

let product (type a) (gs : a g list) : a list g =
  let len = List.length gs in
  let list_gen (s : int) : a list option =
    let s = if len = 0 then 0 else s - 1 in
    distribute_option (List.map gs ~f:(fun g -> g s))
   in list_gen

let map (type a) (type b) ~(f:a -> b) (g:a g) : b g =
  (Option.map ~f) % g

let size_seq : int Sequence.t ref =
  ref (Sequence.map ~f:(( * ) 5)
         (Quickcheck.random_sequence ~seed:Quickcheck.default_seed Quickcheck.Generator.small_positive_int))

let next_size () : int =
  let (s,ss) = Option.value_exn (Sequence.next !size_seq)
   in size_seq := ss
    ; s

let of_list (type a) (l : a list) : a g =
  fun _ -> let i = Random.int (List.length l)
            in Some (List.nth_exn l i)

let g_to_seq (g : 'a g) : 'a Sequence.t =
  Sequence.unfold_step ~init:()
    ~f:(fun () -> let size = next_size () in
         begin match g size with
           | None -> Skip ()
           | Some v -> Yield (v,())
         end)
