open MyStdLib

type t_node =
  | Named of Id.t
  | Arrow of t * t
  | Tuple of t list
  | Mu of Id.t * t
  | Variant of (Id.t * t) list
and t = t_node hash_consed
[@@deriving eq, hash, ord, show, sexp]

let table = HashConsTable.create 1000

let create
    (node:t_node)
  : t =
  HashConsTable.hashcons
    hash_t_node
    compare_t_node
    table
    node

let node
    (v:t)
  : t_node =
  v.node

let mk_named (i : Id.t) : t =
  create (Named i)

let mk_arrow (t1:t) (t2:t) : t =
  create (Arrow (t1,t2))

let mk_mu (i:Id.t) (t:t) : t =
  if equal t (mk_named i) then
    failwith "cannot do infinite loop";
  create (Mu (i,t))

let fold (type a)
         ~(name_f : Id.t -> a)
         ~(arr_f : a -> a -> a)
         ~(tuple_f : a list -> a)
         ~(mu_f : Id.t -> a -> a)
         ~(variant_f : (Id.t * a) list -> a)
         (e : t)
         : a =
  let rec fold_internal (e : t) : a =
    match node e with
      | Named v -> name_f v
      | Arrow (e1,e2) -> arr_f (fold_internal e1) (fold_internal e2)
      | Tuple es -> tuple_f (List.map ~f:fold_internal es)
      | Mu (i,e) -> mu_f i (fold_internal e)
      | Variant variants ->
        variant_f (List.map ~f:(fun (i,t) -> (i,fold_internal t)) variants)
  in fold_internal e

let arr_apply (type a) ~(f : t -> t -> a) (ty : t) : a option =
  match node ty with
    | Arrow (ty1,ty2) -> Some (f ty1 ty2)
    | _ -> None

let destruct_arr : t -> (t * t) option =
  arr_apply ~f:(fun ty1 ty2 -> (ty1,ty2))

let destruct_arr_exn (t : t) : t * t =
  Option.value_exn (destruct_arr t)

let id_apply (type a) ~(f:Id.t -> a) (ty:t) : a option =
  match node ty with
    | Named v -> Some (f v)
    | _ -> None

let destruct_id : t -> Id.t option =
  id_apply ~f:ident

let destruct_id_exn (x:t) : Id.t =
  Option.value_exn (destruct_id x)

let mk_variant (vs:(Id.t * t) list) : t =
  create (Variant vs)

let variant_apply (type a) ~(f:(Id.t * t) list -> a) (ty:t) : a option =
  match node ty with
    | Variant its -> Some (f its)
    | _ -> None

let destruct_variant : t -> (Id.t * t) list option =
  variant_apply ~f:ident

let destruct_variant_exn (t:t) : (Id.t * t) list =
  Option.value_exn (destruct_variant t)

let mk_tuple (ts:t list) : t =
  begin match ts with
    | [t] -> t
    | _ -> create (Tuple ts)
  end

let tuple_apply (type a) ~(f:t list -> a) (ty:t) : a option =
  match node ty with
    | Tuple ts -> Some (f ts)
    | _ -> None

let destruct_tuple : t -> (t list) option =
  tuple_apply ~f:ident

let destruct_tuple_exn (t:t) : t list =
  Option.value_exn (destruct_tuple t)

let mu_apply (type a) ~(f:Id.t -> t -> a) (ty:t) : a option =
  match node ty with
    | Mu (i,t)-> Some (f i t)
    | _ -> None

let destruct_mu : t -> (Id.t * t) option =
  mu_apply ~f:(fun i t -> (i,t))

let destruct_mu_exn (t:t) : Id.t * t =
  Option.value_exn (destruct_mu t)

let _unit : t = mk_tuple []

let _t = mk_named (Id.create "t")

let _bool = mk_named (Id.create "bool")

let _nat = mk_named (Id.create "nat")

let size : t -> int =
  fold ~name_f:(fun _ -> 1)
       ~arr_f:(fun x y -> x+y+1)
       ~tuple_f:(fun ss -> List.fold_left ~f:(+) ~init:1 ss)
       ~mu_f:(fun _ s -> s+1)
       ~variant_f:(List.fold_left ~init:1 ~f:(fun acc (_,i) -> i+acc))

let is_functionless
  : t -> bool =
  fold
    ~name_f:(fun _ -> true)
    ~arr_f:(fun _ _ -> false)
    ~tuple_f:(fun ss -> List.for_all ~f:ident ss)
    ~mu_f:(fun _ _ -> true)
    ~variant_f:(List.fold ~f:(fun acc (_,b) -> acc && b) ~init:true)

let rec split_to_arg_list_result
    (x:t)
  : t list * t =
  begin match node x with
    | Arrow (t1,t2) ->
      let (args,res) = split_to_arg_list_result t2 in
      (t1::args,res)
    | _ -> ([],x)
  end

let rec replace
    (t:t)
    (i:Id.t)
    (rep:t)
  : t =
  let replace t = replace t i rep in
  begin match node t with
    | Named i' ->
      if Id.equal i i' then
        rep
      else
        t
    | Arrow (t1,t2) ->
      mk_arrow (replace t1) (replace t2)
    | Tuple ts ->
      mk_tuple (List.map ~f:replace ts)
    | Mu (i',t) ->
      mk_mu i' (replace t)
    | Variant branches ->
      mk_variant (List.map ~f:(fun (i,t) -> (i,replace t)) branches)
  end

let pp f t =
  let fpf = Format.fprintf in
  let prec_of_typ (t:t) =
    match node t with
    | Named _  -> 125
    | Tuple _ -> 75
    | Arrow   _ -> 50
    | Mu   _ -> 20
    | Variant _ -> 10
  in
  let rec pp_internal f ((lvl, t): int * t) =
    let this_lvl = prec_of_typ t in
    (if this_lvl < lvl then fpf f "(");
    begin match node t with
      | Named x       -> fpf f "%a" Id.pp x
      | Arrow (t1, t2) ->
        fpf f "@[<2>%a ->@ %a@]" pp_internal (this_lvl+1, t1) pp_internal (this_lvl, t2)
      | Tuple ts -> fpf_tuple_typ_list f (lvl, ts)
      | Mu (i,t) ->
        fpf f "@[<2>mu@ %a .@ %a@]" Id.pp i pp_internal (this_lvl, t)
      | Variant branches ->
        fpf_branches f (lvl, branches)
    end;
    (if this_lvl < lvl then fpf f ")")
  and fpf_tuple_typ_list ppf (lvl, ts) =
    match ts with
    | []    -> ()
    | [t]   -> fpf ppf "%a" pp_internal (76, t)  (* Hack to ensure that nested tuples get parens *)
    | t::ts -> fpf ppf "%a * %a" pp_internal (76, t) fpf_tuple_typ_list (lvl, ts)
  and fpf_branches ppf (lvl, branches) =
    match branches with
    | []    -> ()
    | [(i,t)]   ->
      fpf
        ppf
        "|@ %a@ %a"
        Id.pp i
        pp_internal (11, t)  (* Hack to ensure that nested tuples get parens *)
    | (i,t)::branches ->
      fpf ppf "|@ %a@ %a@ %a" Id.pp i pp_internal (11, t) fpf_branches (lvl, branches)
  in
  pp_internal f (0,t)

let show = show_of_pp pp
