open MyStdLib
open Lang

exception ExpectedException

type expr =
  | Var of Id.t
  | Wildcard
  | App of expr * expr
  | Func of Param.t * expr
  | Ctor of Id.t * expr
  | Unctor of Id.t * expr
  | Match of expr * (Pattern.t * expr) list
  | Fix  of Id.t * Type.t * expr
  | Tuple of expr list
  | Proj of int * expr
  | UpdateChecks of (value -> value -> bool) * expr * expr
  | Check of expr

and value =
  | VFunc of Param.t * expr
  | VCtor of Id.t * value
  | VTuple of value list
  | VWildcard
[@@deriving show]

let rec matches_pattern_and_extractions
    (p:Pattern.t)
    (v:value)
  : (Id.t * value) list option =
  begin match (p,v) with
    | (Tuple ps, VTuple vs) ->
      let merge_os =
        List.map2_exn
          ~f:matches_pattern_and_extractions
          ps
          vs
      in
      Option.map
        ~f:(fun ivs -> List.concat ivs)
        (distribute_option merge_os)
    | (Ctor (i,p),VCtor (i',v)) ->
      if Id.equal i i' then
        matches_pattern_and_extractions p v
      else
        None
    | (Var i,_) -> Some [(i,v)]
    | (Wildcard,_) -> Some []
    | _ -> failwith "bad typechecking"
  end

let from_exp =
  Expr.fold
    ~var_f:(fun i -> Var i)
    ~app_f:(fun e1 e2 -> App (e1,e2))
    ~func_f:(fun p e -> Func(p,e))
    ~ctor_f:(fun i e -> Ctor(i,e))
    ~unctor_f:(fun i e -> Unctor (i,e))
    ~match_f:(fun e bs -> Match(e,bs))
    ~fix_f:(fun i t e -> Fix(i,t,e))
    ~tuple_f:(fun es -> Tuple es)
    ~proj_f:(fun i e -> Proj(i,e))
    ~eq_f:(fun _ _ -> failwith "invalid")
    ~wildcard_f:(Wildcard)

let from_value : Value.t -> value =
  Value.fold
    ~func_f:(fun p e -> VFunc(p,from_exp e))
    ~ctor_f:(fun i e -> VCtor(i,e))
    ~tuple_f:(fun es -> VTuple es)
    ~wildcard_f:(VWildcard)

let rec to_exp
    (e:expr)
  : Expr.t =
  begin match e with
    | Var i -> Expr.mk_var i
    | Wildcard -> Expr.mk_wildcard
    | App (e1,e2) -> Expr.mk_app (to_exp e1) (to_exp e2)
    | Func (p,e) -> Expr.mk_func p (to_exp e)
    | Ctor (i,e) -> Expr.mk_ctor i (to_exp e)
    | Unctor (i,e) -> Expr.mk_unctor i (to_exp e)
    | Match (e,branches) ->
      Expr.mk_match
        (to_exp e)
        (List.map ~f:(fun (p,e) -> (p,to_exp e)) branches)
    | Fix (i,t,e) -> Expr.mk_fix i t (to_exp e)
    | Tuple es -> Expr.mk_tuple (List.map ~f:to_exp es)
    | Proj (i,e) -> Expr.mk_proj i (to_exp e)
    | UpdateChecks _ -> failwith "cannot do"
    | Check _ -> failwith "cannot do"
  end

let rec to_value
    (v:value)
  : Value.t =
  begin match v with
    | VFunc (p,e) -> Value.mk_func p (to_exp e)
    | VCtor (i,v) -> Value.mk_ctor i (to_value v)
    | VTuple vs -> Value.mk_tuple (List.map ~f:to_value vs)
    | VWildcard -> Value.mk_wildcard
  end

let rec value_to_exp
    (v:value)
  : expr =
  begin match v with
    | VFunc (p,e) -> Func (p,e)
    | VCtor (i,v) -> Ctor (i,value_to_exp v)
    | VTuple vs -> Tuple (List.map ~f:value_to_exp vs)
    | VWildcard -> Wildcard
  end


let rec replace
    (i:Id.t)
    (e_with:expr)
    (e:expr)
  : expr =
  let replace_simple = replace i e_with in
  begin match e with
    | UpdateChecks (f,earg,e) -> UpdateChecks (f,replace_simple earg,replace_simple e)
    | Check e -> Check (replace_simple e)
    | Wildcard -> e
    | Var i' ->
      if Id.equal i i' then
        e_with
      else
        e
    | App (e1,e2) ->
      App (replace_simple e1,replace_simple e2)
    | Func ((i',t),e') ->
      if Id.equal i i' then
        e
      else
        Func ((i',t),(replace_simple e'))
    | Ctor (i,e) ->
      Ctor (i,(replace_simple e))
    | Unctor (i,e) ->
      Unctor (i,(replace_simple e))
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
      Match ((replace_simple e),branches)
    | Fix (i',t,e') ->
      if Id.equal i i' then
        e
      else
        Fix (i',t,(replace_simple e'))
    | Tuple es ->
      Tuple
        (List.map ~f:replace_simple es)
    | Proj (i,e) ->
      Proj (i,(replace_simple e))
  end

let replace_holes
    ~(i_e:(Id.t * expr) list)
    (e:expr)
  : expr =
  List.fold_left
    ~f:(fun acc (i,e) -> replace i e acc)
    ~init:e
    i_e

let rec evaluate
    (current_check : value -> bool)
    (e : expr)
  : value =
  begin match e with
    | UpdateChecks (f,earg,e) ->
      let varg = evaluate current_check earg in
      evaluate (f varg) e
    | Check e ->
      let v = evaluate current_check e in
      if current_check v then
        v
      else
        raise ExpectedException
    | Wildcard -> VWildcard
    | Var i -> failwith ("unbound variable " ^ (Id.show i))
    | App (e1,e2) ->
      let (v1) = evaluate current_check e1 in
      let e1 = (value_to_exp v1) in
      begin match e1 with
        | Func ((i,_),e1) ->
          let (v2) = evaluate current_check e2 in
          let e2 = (value_to_exp v2) in
          evaluate current_check (replace i e2 e1)
        | _ -> failwith "nonfunc applied"
      end
    | Func (a,e) ->
      VFunc (a,e)
    | Ctor (i,e) ->
      let v = evaluate current_check e in
      VCtor (i,v)
    | Match (e,branches) as match_expr ->
      let v = evaluate current_check e in
      let branch_o =
        List.find_map
          ~f:(fun (p,e) ->
              Option.map
                ~f:(fun ms -> (ms,e))
                (matches_pattern_and_extractions p v))
          branches
      in
      let (replacements,e) =
        begin match branch_o with
          | None ->
            failwith
              ((show_value v)
               ^ " not matched: \n "
               ^ (show_expr match_expr))
          | Some b -> b
        end
      in
      let replacements =
        List.map ~f:(fun (i,v) -> (i,value_to_exp v)) replacements
      in
      let v = evaluate current_check (replace_holes replacements e) in
      v
    | Fix (i,_,e') ->
      evaluate current_check (replace i e e')
    | Tuple es ->
      let vs =
        List.map ~f:(evaluate current_check) es
      in
      VTuple vs
    | Proj (i,e) ->
      let v = evaluate current_check e in
      begin match v with
        | VWildcard -> VWildcard
        | VTuple vs ->
          begin match List.nth vs i with
            | None -> raise ExpectedException
            | Some v -> v
          end
        | _ -> raise ExpectedException
      end
    | Unctor (i,e) ->
      let v = evaluate current_check e in
      begin match v with
        | VCtor (i',e) ->
          if Id.equal i i' then
            e
          else
            raise ExpectedException
        | _ -> raise ExpectedException
      end
  end

let evaluate
    (e : expr)
  : value option =
  try Some (evaluate (fun _ -> true)  e) with ExpectedException -> None

let evaluate_with_holes
    ~(eval_context:(Id.t * Expr.t) list)
    (e:expr)
  : value option =
  let i_e = List.map ~f:(fun (i,e) -> (i,from_exp e)) eval_context in
  let e = replace_holes ~i_e e in
  evaluate e
