open MyStdLib

module Pattern =
struct
  type t =
    | Tuple of t list
    | Ctor of Id.t * t
    | Var of Id.t
    | Wildcard
  [@@deriving eq, hash, ord, show]

  let rec contains_id
      (i:Id.t)
      (p:t)
    : bool =
    begin match p with
      | Tuple ps -> List.exists ~f:(contains_id i) ps
      | Ctor (_,p) -> contains_id i p
      | Var i' -> Id.equal i i'
      | Wildcard -> false
    end

  let rec pp
      (ppf:Format.formatter)
      (p:t)
    : unit =
    begin match p with
      | Ctor (i,p) ->
        Format.fprintf
          ppf
          "@[<2>%a %a@]"
          Id.pp i
          pp p
      | Wildcard -> Format.fprintf ppf "_"
      | Tuple ps ->
        Format.fprintf
          ppf
          "@[<2>(%a)@]"
          pp_many ps
      | Var i ->
        Id.pp ppf i
    end
  and pp_many
      (ppf:Format.formatter)
      (ps:t list)
    : unit =
    begin match ps with
      | [] -> ()
      | [p]   -> Format.fprintf ppf "%a" pp p
      | p::ps -> Format.fprintf ppf "%a,@ %a" pp p pp_many ps
    end


  let show = show_of_pp pp
end

type 'a e_node_maker =
  | Var of Id.t
  | Wildcard
  | App of 'a e_maker * 'a e_maker
  | Func of Param.t * 'a e_maker
  | Ctor of Id.t * 'a e_maker
  | Unctor of Id.t * 'a e_maker
  | Eq of bool * 'a e_maker * 'a e_maker
  | Match of 'a e_maker * (Pattern.t * 'a e_maker) list
  | Fix  of Id.t * Type.t * 'a e_maker
  | Tuple of 'a e_maker list
  | Proj of int * 'a e_maker
and 'a e_l_maker =
  {
    e_node : 'a e_node_maker ;
    mutable eval : 'a option [@compare.ignore] [@ignore] ;
  }
and 'a e_maker = ('a e_l_maker) hash_consed
[@@deriving eq, hash, ord, show]

type v_node =
  | Func of Param.t * expr
  | Ctor of Id.t * value
  | Tuple of value list
  | Wildcard
and v_l =
  {
    v_node : v_node ;
  }
and value = v_l hash_consed
and e_node = value e_node_maker
and e_l = value e_l_maker
and expr = value e_maker
[@@deriving eq, hash, ord, show]

module Expr = struct
  type t = expr
  [@@deriving eq, hash, ord, show]
  type t_node = e_node
  [@@deriving eq, hash, ord, show]

  let table = HashConsTable.create 1000

  let create
      (node:e_node)
    : t =
    let l =
      {
        e_node = node ;
        eval = None   ;
      }
    in
    HashConsTable.hashcons
      (fun e -> hash_e_node e.e_node)
      (fun e1 e2 -> compare_e_node e1.e_node e2.e_node)
      table
      l

  let node
      (v:t)
    : e_node =
    v.node.e_node

  let mk_var (i:Id.t) : t =
    create (Var i)

  let mk_wildcard : t = create Wildcard

  let fold (type a)
      ~(var_f:Id.t -> a)
      ~(app_f:a -> a -> a)
      ~(func_f:Param.t -> a -> a)
      ~(ctor_f:Id.t -> a -> a)
      ~(eq_f:bool -> a -> a -> a)
      ~(unctor_f:Id.t -> a -> a)
      ~(match_f:a -> (Pattern.t * a) list -> a)
      ~(fix_f:Id.t -> Type.t -> a -> a)
      ~(tuple_f:a list -> a)
      ~(proj_f:int -> a -> a)
      ~(wildcard_f:a)
      (e:t)
    : a =
    let rec fold_internal (e:t) : a =
      match node e with
      | Var v -> var_f v
      | App (e1,e2) -> app_f (fold_internal e1) (fold_internal e2)
      | Func (a,e) -> func_f a (fold_internal e)
      | Eq (b,e1,e2) -> eq_f b (fold_internal e1) (fold_internal e2)
      | Ctor (v,e) -> ctor_f v (fold_internal e)
      | Match (e,branches)
        -> match_f (fold_internal e)
             (List.map ~f:(fun (p,e') -> (p,fold_internal e')) branches)
      | Fix (i,t,e)
        -> fix_f i t (fold_internal e)
      | Tuple es
        -> tuple_f (List.map ~f:fold_internal es)
      | Proj (i,e)
        -> proj_f i (fold_internal e)
      | Unctor (i,e)
        -> unctor_f i (fold_internal e)
      | Wildcard -> wildcard_f
    in fold_internal e

  let mk_app (e1:t) (e2:t) : t =
    create (App (e1,e2))

  let mk_eq (b:bool) (e1:t) (e2:t) : t =
    create (Eq (b,e1,e2))

  let mk_equal (e1:t) (e2:t) : t =
    mk_eq true e1 e2

  let mk_not_equal (e1:t) (e2:t) : t =
    mk_eq false e1 e2

  let apply_app
      (type a)
      ~(f:t -> t -> a)
      (e:t)
    : a option =
    begin match node e with
      | App (e1,e2) -> Some (f e1 e2)
      | _ -> None
    end

  let destruct_app
    : t -> (t * t) option =
    apply_app ~f:(fun e1 e2 -> (e1,e2))

  let destruct_app_exn
      (e:t)
    : t * t =
    Option.value_exn (destruct_app e)

  let mk_func
      (a:Param.t)
      (e:t)
    : t =
    create (Func (a,e))

  let apply_func
      (type a)
      ~(f:Param.t -> t -> a)
      (e:t)
    : a option =
    begin match node e with
      | Func (a,e2) -> Some (f a e2)
      | _ -> None
    end

  let destruct_func
    : t -> (Param.t * t) option =
    apply_func ~f:(fun a e2 -> (a,e2))

  let destruct_func_exn
      (e:t)
    : Param.t * t =
    Option.value_exn (destruct_func e)

  let mk_ctor
      (i:Id.t)
      (e:t)
    : t =
    create (Ctor (i,e))

  let apply_ctor
      (type a)
      ~(f:Id.t -> t -> a)
      (e:t)
    : a option =
    begin match node e with
      | Ctor (i,e2) -> Some (f i e2)
      | _ -> None
    end

  let destruct_ctor
    : t -> (Id.t * t) option =
    apply_ctor ~f:(fun a e2 -> (a,e2))

  let destruct_ctor_exn
      (e:t)
    : Id.t * t =
    Option.value_exn (destruct_ctor e)

  let mk_unctor
      (i:Id.t)
      (e:t)
    : t =
    create (Unctor (i,e))

  let apply_unctor
      (type a)
      ~(f:Id.t -> t -> a)
      (e:t)
    : a option =
    begin match node e with
      | Unctor (i,e2) -> Some (f i e2)
      | _ -> None
    end

  let destruct_unctor
    : t -> (Id.t * t) option =
    apply_unctor ~f:(fun a e2 -> (a,e2))

  let destruct_unctor_exn
      (e:t)
    : Id.t * t =
    Option.value_exn (destruct_unctor e)

  let mk_tuple
      (es:t list)
    : t =
    create (Tuple es)

  let apply_tuple
      (type a)
      ~(f:t list -> a)
      (e:t)
    : a option =
    begin match node e with
      | Tuple es -> Some (f es)
      | _ -> None
    end

  let destruct_tuple
    : t -> t list option =
    apply_tuple ~f:ident

  let destruct_tuple_exn
      (e:t)
    : t list =
    Option.value_exn (destruct_tuple e)

  let mk_proj
      (i:int)
      (e:t)
    : t =
    create (Proj (i,e))

  let apply_proj
      (type a)
      ~(f:int -> t -> a)
      (e:t)
    : a option =
    begin match node e with
      | Proj (i,e2) -> Some (f i e2)
      | _ -> None
    end

  let destruct_proj
    : t -> (int * t) option =
    apply_proj ~f:(fun a e2 -> (a,e2))

  let destruct_proj_exn
      (e:t)
    : int * t =
    Option.value_exn (destruct_proj e)

  let mk_match
      (e:t)
      (branches:(Pattern.t * t) list)
    : t =
    create (Match (e,branches))

  let apply_match
      (type a)
      ~(f:t -> (Pattern.t * t) list -> a)
      (e:t)
    : a option =
    begin match node e with
      | Match (e,branches) -> Some (f e branches)
      | _ -> None
    end

  let destruct_match
    : t -> (t * (Pattern.t * t) list) option =
    apply_match ~f:(fun e branches -> (e,branches))

  let destruct_match_exn
      (e:t)
    : t * (Pattern.t * t) list =
    Option.value_exn (destruct_match e)

  let mk_fix
      (i:Id.t)
      (t:Type.t)
      (e:t)
    : t =
    create (Fix (i,t,e))

  let apply_fix
      (type a)
      ~(f:Id.t -> Type.t -> t -> a)
      (e:t)
    : a option =
    begin match node e with
      | Fix (i,t,e) -> Some (f i t e)
      | _ -> None
    end

  let destruct_fix
    : t -> (Id.t * Type.t * t) option =
    apply_fix ~f:(fun i t e -> (i,t,e))

  let destruct_fix_exn
      (e:t)
    : Id.t * Type.t * t =
    Option.value_exn (destruct_fix e)

  let rec replace
      (i:Id.t)
      (e_with:t)
      (e:t)
    : t =
    let replace_simple = replace i e_with in
    begin match node e with
      | Wildcard -> e
      | Eq (b,e1,e2) ->
        mk_eq b (replace_simple e1) (replace_simple e2)
      | Var i' ->
        if Id.equal i i' then
          e_with
        else
          e
      | App (e1,e2) ->
        mk_app (replace_simple e1) (replace_simple e2)
      | Func ((i',t),e') ->
        if Id.equal i i' then
          e
        else
          mk_func (i',t) (replace_simple e')
      | Ctor (i,e) ->
        mk_ctor i (replace_simple e)
      | Unctor (i,e) ->
        mk_unctor i (replace_simple e)
      | Match (e,branches) ->
        let branches =
          List.map
            ~f:(fun (p,e) ->
                if Pattern.contains_id i p then
                  (p,e)
                else
                  (p,replace_simple e))
            branches
        in
        mk_match (replace_simple e) branches
      | Fix (i',t,e') ->
        if Id.equal i i' then
          e
        else
          mk_fix i' t (replace_simple e')
      | Tuple es ->
        mk_tuple
          (List.map ~f:replace_simple es)
      | Proj (i,e) ->
        mk_proj i (replace_simple e)
    end

  let replace_holes
      ~(i_e:(Id.t * t) list)
      (e:t)
    : t =
    List.fold_left
      ~f:(fun acc (i,e) -> replace i e acc)
      ~init:e
      i_e

  let mk_unit : t = mk_tuple []
  let unit_ : t = mk_unit

  let mk_true_exp
    : t =
    mk_ctor (Id.create "True") (mk_tuple [])

  let mk_false_exp
    : t =
    mk_ctor (Id.create "False") (mk_tuple [])

  let mk_constant_func
      (t:Type.t)
      (e:t)
    : t =
    mk_func ((Id.create "x"),t) e

  let mk_constant_true_func
      (t:Type.t)
    : t =
    mk_constant_func t mk_true_exp

  let mk_constant_false_func
      (t:Type.t)
    : t =
    mk_constant_func t mk_false_exp

  let mk_identity_func
      (t:Type.t)
    : t =
    mk_func ((Id.create "x"),t) (mk_var (Id.create "x"))

  let mk_and_func : t = mk_var (Id.create "and")

  let rec contains_var
      (v:Id.t)
      (e:t)
    : bool =
    let contains_var_simple = contains_var v in
    begin match node e with
      | Wildcard -> false
      | Var i -> Id.equal i v
      | App (e1,e2) -> contains_var_simple e1 || contains_var_simple e2
      | Func ((i,_),e) ->
        if Id.equal i v then
          false
        else
          contains_var_simple e
      | Ctor (_,e) -> contains_var_simple e
      | Eq (_,e1,e2) -> contains_var_simple e1 || contains_var_simple e2
      | Unctor (_,e) -> contains_var_simple e
      | Match (e,branches) ->
        contains_var_simple e ||
        (List.exists
           ~f:(fun (p,e) ->
               not (Pattern.contains_id v p) && contains_var_simple e)
           branches)
      | Fix (i,_,e) ->
        if Id.equal i v then
          false
        else
          contains_var_simple e
      | Tuple es -> List.exists ~f:contains_var_simple es
      | Proj (_,e) -> contains_var_simple e
    end

  let rec simplify
      (e:t)
    : t =
    begin match node e with
      | Wildcard -> e
      | Var _ -> e
      | App (e1,e2) ->
        mk_app (simplify e1) (simplify e2)
      | Eq (b,e1,e2) ->
        mk_eq b (simplify e1) (simplify e2)
      | Func (a,e) ->
        mk_func a (simplify e)
      | Match (e,branches) ->
        mk_match
          (simplify e)
          (List.map ~f:(fun (p,e) -> (p,simplify e)) branches)
      | Fix (i,t,e) ->
        let e = simplify e in
        if not (contains_var i e) then
          e
        else
          mk_fix i t e
      | Ctor (i,e) ->
        mk_ctor i (simplify e)
      | Unctor (i,e) ->
        mk_unctor i (simplify e)
      | Tuple es -> mk_tuple (List.map ~f:simplify es)
      | Proj (i,e) -> mk_proj i (simplify e)
    end

  let and_exps
      (e1:t)
      (e2:t)
    : t =
    mk_app (mk_app mk_and_func e1) e2

  let is_func
      ~(func_internals:t)
      (e:t)
    : bool =
    begin match node e with
      | Func (_,e) -> equal e func_internals
      | _ -> false
    end

  let and_predicates (e1:t) (e2:t) : t =
    let is_true_func = is_func ~func_internals:mk_true_exp in
    let is_false_func = is_func ~func_internals:mk_false_exp in
    if is_true_func e1 then
      e2
    else if is_true_func e2 then
      e1
    else if is_false_func e1 || is_false_func e2 then
      mk_constant_false_func (Type._t)
    else
      let var = (Id.create "x") in
      let var_exp = mk_var var in
      let apped_e1 = mk_app e1 var_exp in
      let apped_e2 = mk_app e2 var_exp in
      mk_func
        (var,Type._t)
        (and_exps apped_e1 apped_e2)

  let mk_let_in (i:Id.t) (t:Type.t) (e1:t) (e2:t) : t =
    mk_app (mk_func (i,t) e2) e1

  let size : t -> int =
    fold ~var_f:(fun _ -> 1)
      ~app_f:(fun x y -> x+y+1)
      ~eq_f:(fun _ x y -> x+y+1)
      ~func_f:(fun (_,t) i -> 1 + (Type.size t) + i)
      ~ctor_f:(fun _ s -> s+1)
      ~unctor_f:(fun _ s -> s+1)
      ~match_f:(fun s bs -> List.fold_left bs ~init:(s+1)
                   ~f:(fun acc (_,s) -> s+acc))
      ~fix_f:(fun _ t s -> 1 + (Type.size t) + s)
      ~tuple_f:(List.fold_left ~f:(+) ~init:1)
      ~proj_f:(fun _ i -> i+2)
      ~wildcard_f:1

  let pp f e =
    (*This code heavily taken from Myth*)
    let fpf = Format.fprintf in
    let rec is_nat_literal (e:t) : bool =
      match node e with
      | Ctor (i, e) ->
        (Id.equal i (Id.create "O") && equal e unit_)
        || Id.equal i (Id.create "S") && is_nat_literal e
      | _           -> false
    in
    let fpf_nat_literal ppf e =
      let rec count n e =
        match node e with
        | Ctor (i, e) ->
          if Id.equal i (Id.create "O") then
            fpf ppf "%d" n
          else
            count (n+1) e
        | _ -> failwith "non-nat literal encountered"
      in
      count 0 e
    in
    let prec_of_exp (e:t) : int =
      match node e with
      | App _  -> 500
      | Eq _ -> 400
      | Proj _ -> 500
      | Func _ | Fix _ -> 100
      | Ctor  (_, e) -> (if equal e unit_ then 1000 else 600)
      | Unctor  (_, e) -> 600
      | Tuple _       -> 700
      | Match  _      -> 200
      | Var _         -> 1000
      | Wildcard         -> 1000
    in
    let rec fpf_branch ppf ((lvl, (p,e)):int * (Pattern.t * t)) =
      fpf ppf "@[<2>| %a -> %a@]" Pattern.pp p pp_internal (lvl, e)
    and pp_branches
        (ppf:Format.formatter)
        ((lvl,bs):int * ((Pattern.t * t) list))
      : unit =
      match bs with
      | [] -> ()
      | [b] -> fpf ppf "%a" fpf_branch (lvl, b)
      | b::bs -> fpf ppf "%a@\n%a" fpf_branch (lvl, b) pp_branches (lvl, bs)
    and fpf_exp_list ppf (es:t list) =
      match es with
      | []    -> ()
      | [e]   -> fpf ppf "%a" pp_internal (0, e)
      | e::es -> fpf ppf "%a,@ %a" pp_internal (0, e) fpf_exp_list es
    and pp_internal
        (ppf:Format.formatter)
        ((lvl,e):(int*t))
      : unit =
      if is_nat_literal e then
        fpf_nat_literal ppf e
      else
        let this_lvl = prec_of_exp e in
        (if this_lvl < lvl then fpf ppf "(");
        begin match node e with
          | Var x -> fpf ppf "%a" Id.pp x
          | Eq (true,e1,e2) ->
            fpf ppf "%a == %a" pp_internal (this_lvl + 1,e1) pp_internal (this_lvl + 1,e2)
          | Eq (false,e1,e2) ->
            fpf ppf "%a != %a" pp_internal (this_lvl + 1,e1) pp_internal (this_lvl + 1,e2)
          | App (e1, e2) ->
            fpf ppf "@[<2>%a@ %a@]"
              pp_internal (this_lvl, e1) pp_internal (this_lvl + 1, e2)
          | Proj (n, e) ->
            fpf ppf "@[<2>%a@ .@ %d@]" pp_internal (this_lvl + 1, e) n
          | Func (x, e) ->
            fpf ppf "@[<2>fun %a ->@ %a@]" Param.pp x pp_internal (this_lvl, e)
          | Ctor (c, e)  ->
            if equal e unit_ then
              fpf ppf "@[<2>%a@]" Id.pp c
            else
              fpf ppf "@[<2>%a %a@]" Id.pp c pp_internal (this_lvl + 1, e)
          | Unctor (c, e)  ->
            let unc = Id.create ("Un_" ^ (Id.to_string c)) in
            fpf ppf "@[<2>%a %a@]" Id.pp unc pp_internal (this_lvl + 1, e)
          | Match (e, bs) ->
            fpf ppf "@[<2>match %a with@\n%a@]"
              pp_internal (0, e)
              pp_branches (this_lvl+1, bs)
          | Fix (i, t, e) ->
            fpf ppf "@[<2>fix (%a : %a) =@ %a@]"
              Id.pp i
              Type.pp t
              pp_internal (this_lvl, e)
          | Tuple es -> fpf ppf "@[<2>(%a)@]" fpf_exp_list es
          | Wildcard -> fpf ppf "@[_@]"
        end;
        (if this_lvl < lvl then fpf ppf ")")
    in
    pp_internal f (0,e)

  let show = show_of_pp pp

  let rec from_int n =
    if n = 0 then
      create (Ctor (Id.create "O",unit_))
    else
      create (Ctor (Id.create "S",from_int (n-1)))

  let rec of_type
      (t:Type.t)
    : t option =
    begin match Type.node t with
      | Named i -> None
      | Arrow (t1,t2) ->
        Option.map
          ~f:(fun e2 ->
              (mk_func
                 (Id.create "var",t1)
                 e2))
          (of_type t2)
      | Tuple ts ->
        let eso = List.map ~f:of_type ts in
        begin match distribute_option eso with
          | None -> None
          | Some es -> Some (mk_tuple es)
        end
      | Mu (_,t) ->
        of_type t
      | Variant branches ->
        List.fold
          ~f:(fun acco (i,t) ->
              begin match acco with
                | None ->
                  let eo = of_type t in
                  Option.map ~f:(fun e -> mk_ctor i e) eo
                | Some e -> Some e
              end)
          ~init:None
          branches
    end

  let rec extract_unbranched_switches
      (e:t)
    : (t * Id.t) list =
    begin match node e with
      | Var _ -> []
      | App (e1,e2) -> (extract_unbranched_switches e1)@(extract_unbranched_switches e2)
      | Eq (_,e1,e2) -> (extract_unbranched_switches e1)@(extract_unbranched_switches e2)
      | Func (_,e) -> extract_unbranched_switches e
      | Ctor (_,e) -> extract_unbranched_switches e
      | Unctor (i,e) ->
        let l = extract_unbranched_switches e in
        (e,i)::l
      | Match (e,branches) ->
        let matched_e = e in
        let l1 = extract_unbranched_switches e in
        l1@
        (List.concat_map
           ~f:(fun (_,e) ->
               let l = extract_unbranched_switches e in
               List.filter ~f:(fun (e,_) -> not (equal e matched_e)) l)
           branches)
      | Wildcard -> []
      | Fix _ -> failwith "not doing"
      | Tuple es -> List.concat_map ~f:extract_unbranched_switches es
      | Proj (i,e) -> extract_unbranched_switches e
    end

  let ensure_switches
      (e:t)
    : t =
    failwith "ah"
end

module Value = struct
  type t = value
  [@@deriving eq, hash, ord, show]
  type t_node = v_node
  [@@deriving eq, hash, ord, show]

  let table = HashConsTable.create 1000

  let create
      (node:v_node)
    : t =
    let l =
      {
        v_node = node ;
      }
    in
    HashConsTable.hashcons
      (fun v -> hash_v_node v.v_node)
      (fun v1 v2 -> compare_v_node v1.v_node v2.v_node)
      table
      l

  let node
      (v:t)
    : v_node =
    v.node.v_node

  let mk_func (a:Param.t) (e:Expr.t) : t =
    create (Func (a,e))

  let apply_func (type a) ~(f:Param.t -> Expr.t -> a) (v:t) : a option =
    begin match (node v) with
      | Func (a,e2) -> Some (f a e2)
      | _ -> None
    end

  let destruct_func : t -> (Param.t * Expr.t) option =
    apply_func ~f:(fun a e2 -> (a,e2))

  let destruct_func_exn (v:t) : Param.t * Expr.t =
    Option.value_exn (destruct_func v)

  let mk_ctor (i:Id.t) (v:t) : t =
    create (Ctor (i,v))

  let apply_ctor (type a) ~(f:Id.t -> t -> a) (v:t) : a option =
    match node v with
    | Ctor (i,v) -> Some (f i v)
    | _ -> None

  let destruct_ctor : t -> (Id.t * t) option =
    apply_ctor ~f:(fun i v -> (i,v))

  let destruct_ctor_exn (v:t) : Id.t * t =
    begin match (destruct_ctor v) with
      | Some v -> v
      | None -> failwith (show v)
    end

  let mk_tuple (vs:t list) : t =
    begin match vs with
      | [v] -> v
      | _ -> create (Tuple vs)
    end

  let apply_tuple (type a) ~(f:t list -> a) (v:t) : a option =
    begin match node v with
      | Tuple vs -> Some (f vs)
      | _ -> None
    end

  let destruct_tuple : t -> t list option =
    apply_tuple ~f:ident

  let destruct_tuple_exn (v:t) : t list =
    Option.value_exn (destruct_tuple v)

  let mk_true : t = mk_ctor (Id.create "True") (mk_tuple [])

  let mk_false : t = mk_ctor (Id.create "False") (mk_tuple [])

  let from_bool (b:bool) : t = if b then mk_true else mk_false

  let mk_wildcard : t = create Wildcard

  let rec fold
      ~(func_f:Param.t -> Expr.t -> 'a)
      ~(ctor_f:Id.t -> 'a -> 'a)
      ~(tuple_f:'a list -> 'a)
      ~(wildcard_f:'a)
      (v:t)
    : 'a =
    let fold_simple = fold ~func_f ~ctor_f ~tuple_f ~wildcard_f
    in match node v with
    | Func (a,e) -> func_f a e
    | Ctor (i,v) -> ctor_f i (fold_simple v)
    | Tuple vs -> tuple_f (List.map ~f:fold_simple vs)
    | Wildcard -> wildcard_f

  let to_exp
      (v:t)
    : Expr.t =
    fold
      ~func_f:Expr.mk_func
      ~ctor_f:Expr.mk_ctor
      ~tuple_f:Expr.mk_tuple
      ~wildcard_f:Expr.mk_wildcard
      v

  let rec from_exp (e:Expr.t) : t option =
    match Expr.node e with
    | Func (a,e)
      -> Some (mk_func a e)
    | Ctor (i,e)
      -> Option.map ~f:(mk_ctor i) (from_exp e)
    | Tuple es
      -> Option.map ~f:mk_tuple (Some (List.filter_map es ~f:from_exp))
    | Wildcard -> Some mk_wildcard
    | Var _
    | App _
    | Proj _
    | Match _
    | Fix _
    | Unctor _
    | Eq _
      -> None

  let from_exp_exn (e:Expr.t) : t =
    Option.value_exn (from_exp e)

  let rec subvalues (v:t) : t list =
    v :: begin match node v with
      | Func _ -> []
      | Ctor (_,v) -> subvalues v
      | Tuple vs -> List.concat_map ~f:subvalues vs
      | Wildcard -> []
    end

  let strict_subvalues (e:t) : t list =
    List.tl_exn (subvalues e)

  let strict_subvalue (e1:t) (e2:t) : bool =
    List.mem ~equal (strict_subvalues e2) e1

  let rec functional_subvalues
      ~(break:t -> bool)
      (v:t)
    : t list =
    if break v then
      subvalues v
    else
      begin match node v with
        | Func _ -> [v]
        | Ctor (_,v') -> v::(functional_subvalues ~break v')
        | Tuple vs ->
          let vssubs = List.map ~f:(functional_subvalues ~break) vs in
          let all_subs = List.concat vssubs in
          let combos = List.map ~f:mk_tuple (combinations vssubs) in
          all_subs@combos
        | Wildcard -> [v]
      end

  let strict_functional_subvalues
      ~(break:t -> bool)
      (v:t)
    : t list =
    List.filter
      ~f:(fun v' -> not (equal v v'))
      (functional_subvalues ~break v)

  let strict_functional_subvalue ~(break:t -> bool) (e1:t) (e2:t) : bool =
    List.mem ~equal (strict_functional_subvalues ~break e2) e1

  let size : t -> int =
    fold
      ~func_f:(fun (_,t) e -> 1 + (Type.size t) + (Expr.size e))
      ~ctor_f:(fun _ i -> i+1)
      ~tuple_f:(fun is -> List.fold ~f:(+) ~init:1 is)
      ~wildcard_f:1

  let size_min_expr : t -> int =
    fold
      ~func_f:(fun _ _ -> 1)
      ~ctor_f:(fun _ i -> i+1)
      ~tuple_f:(fun is -> List.fold ~f:(+) ~init:1 is)
      ~wildcard_f:1

  let unit_ = create (Tuple [])
  let true_ = create (Ctor (Id.create "True",unit_))
  let false_ = create (Ctor (Id.create "False",unit_))

  let rec from_int n =
    if n = 0 then
      create (Ctor (Id.create "O",unit_))
    else
      create (Ctor (Id.create "S",from_int (n-1)))

  let pp f v = Expr.pp f (to_exp v)
  let show = show_of_pp pp

  let rec of_type
      (t:Type.t)
    : t option =
    Option.map ~f:from_exp_exn (Expr.of_type t)

  let rec matches_pattern_and_extractions
      (p:Pattern.t)
      (v:t)
    : (Id.t * t) list option =
    begin match (p,node v) with
      | (Tuple ps, Tuple vs) ->
        let merge_os =
          List.map2_exn
            ~f:matches_pattern_and_extractions
            ps
            vs
        in
        Option.map
          ~f:(fun ivs -> List.concat ivs)
          (distribute_option merge_os)
      | (Ctor (i,p),Ctor (i',v)) ->
        if Id.equal i i' then
          matches_pattern_and_extractions p v
        else
          None
      | (Var i,_) -> Some [(i,v)]
      | (Wildcard,_) -> Some []
      | _ -> failwith ("bad typechecking: pattern: " ^ Pattern.show p ^ "value: " ^ show v)
    end
end
