open MyStdLib
open Lang

type expr =
  | Var of Id.t
  | App of expr * expr
  | Func of Param.t * expr
  | Ctor of Id.t * expr
  | Unctor of Id.t * expr
  | Match of expr * (Pattern.t * expr) list
  | Fix of Id.t * Type.t * expr
  | Tuple of expr list
  | Proj of int * expr
  | AngelicF of expr
  | Wildcard

and value =
  | Func of Param.t * expr
  | Ctor of Id.t * value
  | Tuple of value list
  | Wildcard
[@@deriving eq, show]

let rec matches_pattern_and_extractions
    (p:Pattern.t)
    (v:value)
  : (Id.t * value) list option =
  begin match (p,v) with
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
    | _ -> failwith "bad typechecking"
  end

let mk_value_ctor (i:Id.t) (v:value) : value = Ctor (i,v)

let from_exp =
  Expr.fold
    ~var_f:(fun i -> Var i)
    ~app_f:(fun e1 e2 -> App (e1,e2))
    ~eq_f:(fun _ _ _ -> failwith "no eq in angelic evals")
    ~func_f:(fun p e -> Func(p,e))
    ~ctor_f:(fun i e -> Ctor(i,e))
    ~unctor_f:(fun i e -> Unctor (i,e))
    ~match_f:(fun e bs -> Match(e,bs))
    ~tuple_f:(fun es -> Tuple es)
    ~proj_f:(fun i e -> Proj(i,e))
    ~fix_f:(fun i t e -> Fix (i,t,e))
    ~wildcard_f:(Wildcard)

let from_value : Value.t -> value =
  Value.fold
    ~func_f:(fun p e -> (Func (p,from_exp e) : value))
    ~ctor_f:(fun i e -> Ctor(i,e))
    ~tuple_f:(fun es -> Tuple es)
    ~wildcard_f:(Tuple [])

let rec to_exp
    (e:expr)
  : Expr.t =
  begin match e with
    | Wildcard -> Expr.mk_wildcard
    | Var i -> Expr.mk_var i
    | App (e1,e2) -> Expr.mk_app (to_exp e1) (to_exp e2)
    | Func (p,e) ->
      Expr.mk_func
        p
        (to_exp e)
    | Ctor (i,e) -> Expr.mk_ctor i (to_exp e)
    | Unctor (i,e) -> Expr.mk_unctor i (to_exp e)
    | Match (e,bs) ->
      Expr.mk_match
        (to_exp e)
        (List.map ~f:(fun (p,e) -> (p,to_exp e)) bs)
    | Tuple es -> Expr.mk_tuple (List.map ~f:to_exp es)
    | Proj (i,e) -> Expr.mk_proj i (to_exp e)
    | AngelicF e -> failwith "no"
    | Fix (i,t,e) -> Expr.mk_fix i t (to_exp e)
  end

let rec to_value
    (v:value)
  : Value.t =
  begin match v with
    | Func (p,e) ->
      Value.mk_func
        p
        (to_exp e)
    | Ctor (i,e) -> Value.mk_ctor i (to_value e)
    | Tuple es -> Value.mk_tuple (List.map ~f:to_value es)
    | Wildcard -> Value.mk_wildcard
  end


let rec value_to_exp
    (v:value)
  : expr =
  begin match v with
    | Func (p,e) -> Func (p,e)
    | Ctor (i,v) -> Ctor (i,value_to_exp v)
    | Tuple vs -> Tuple (List.map ~f:value_to_exp vs)
    | Wildcard -> Wildcard
  end


let rec replace
    (i:Id.t)
    (e_with:expr)
    (e:expr)
  : expr =
  let replace_simple = replace i e_with in
  begin match e with
    | AngelicF e -> AngelicF (replace_simple e)
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
    | Tuple es ->
      Tuple
        (List.map ~f:replace_simple es)
    | Proj (i,e) ->
      Proj (i,(replace_simple e))
    | Fix (i',t,e') ->
      if Id.equal i i' then
        e
      else
        Fix (i',t,replace_simple e')
    | Wildcard -> Wildcard
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
    (angelics : (value * value list) list)
    (e : expr)
  : ((value * value) list * value) list =
  let evaluate = evaluate angelics in
  begin match e with
    | AngelicF e ->
      let vs_invs = evaluate e in
      List.concat_map
        ~f:(fun (vs,inv) ->
            let outvs =
              Option.value
                ~default:[]
                (List.Assoc.find ~equal:equal_value angelics inv)
            in
            List.map
              ~f:(fun outv ->
                  ((inv , outv)::vs,outv))
              outvs)
        vs_invs
    | Var i -> failwith ("unbound variable " ^ (Id.show i))
    | App (e1,e2) ->
      let vins1v1s = evaluate e1 in
      let vins2v2s = evaluate e2 in
      cartesian_concat_map
        ~f:(fun (vins1,v1) (vins2,v2) ->
            let vins = vins1@vins2 in
            let e1 = value_to_exp v1 in
            let e2 = value_to_exp v2 in
            begin match e1 with
              | Func ((i,_),e1) ->
                let fulle = replace i e2 e1 in
                let vinscallress = evaluate fulle in
                List.map
                  ~f:(fun (vinscall,res) ->
                      (vinscall@vins,res))
                  vinscallress
              | _ -> failwith ("nonfunc applied: " ^ (show_expr e1))
            end)
        vins1v1s
        vins2v2s
    | Func (a,e) ->
      [([],Func (a,e))]
    | Ctor (i,e) ->
      let vcallsvs = evaluate e in
      List.map
        ~f:(fun (vcalls,v) ->
            (vcalls,(Ctor (i,v) : value)))
        vcallsvs
    | Fix (i,_,e') ->
      evaluate (replace i e e')
    | Match (e,branches) as match_expr ->
      let vcallsvs = evaluate e in
      List.concat_map
        ~f:(fun (vcalls,v) ->
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
            let vcalls'vs = evaluate (replace_holes replacements e) in
            List.map
              ~f:(fun (vcalls',v) ->
                  (vcalls@vcalls',v))
              vcalls'vs)
        vcallsvs
    | Tuple es ->
      let allcalls_allvs = List.map ~f:evaluate es in
      let all_merges = combinations allcalls_allvs in
      List.map
        ~f:(fun calls_vs ->
            let (vcalls,vs) =
              List.unzip calls_vs
            in
            let allcalls = List.concat vcalls in
            (allcalls,(Tuple vs : value)))
        all_merges
    | Proj (i,e) ->
      let vcallsvs = evaluate e in
      List.map
        ~f:(fun (vcalls,v) ->
            begin match v with
              | Tuple vs -> (vcalls,List.nth_exn vs i)
              | Wildcard -> (vcalls,Wildcard)
              | _ -> failwith "bad"
            end)
        vcallsvs
    | Unctor (i,e) ->
      let vcallsvs = evaluate e in
      List.map
        ~f:(fun (vcalls,v) ->
            begin match v with
            | Ctor (i',e) ->
              assert (Id.equal i  i');
              (vcalls,e)
            | Wildcard -> (vcalls,Wildcard)
            | _ -> failwith "ah"
          end)
        vcallsvs
    | Wildcard -> [[],Wildcard]
  end

let replace_holes
    ~(i_e:(Id.t * expr) list)
    (e:expr)
  : expr =
  List.fold_left
    ~f:(fun acc (i,e) -> replace i e acc)
    ~init:e
    i_e

let evaluate_with_holes
    ~eval_context:(i_e:(Id.t * expr) list)
    (ios:(value * value list) list)
    (e:expr)
  : ((value * value) list * value) list =
  let e = replace_holes ~i_e e in
  evaluate ios e
