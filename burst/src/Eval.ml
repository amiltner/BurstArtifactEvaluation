open MyStdLib
open Lang

let rec evaluate
    (e : Expr.t)
  : Value.t =
  let l = e.node in
  begin match l.eval with
    | None ->
      let ans =
        match Expr.node e with
        | Wildcard -> Value.mk_wildcard
        | Var i -> failwith ("unbound variable " ^ (Id.show i))
        | App (e1,e2) ->
          let (v1) = evaluate e1 in
          let e1 = Value.to_exp v1 in
          begin match Expr.node e1 with
            | Func ((i,_),e1) ->
              let (v2) = evaluate e2 in
              let e2 = Value.to_exp v2 in
              evaluate (Expr.replace i e2 e1)
            | Wildcard ->
              Value.mk_wildcard
            | _ -> failwith "nonfunc applied"
          end
        | Eq (b,e1,e2) ->
          let v1 = evaluate e1 in
          let v2 = evaluate e2 in
          let eq = Value.equal v1 v2 in
          let res = if b then eq else not eq in
          Value.from_bool res
        | Func (a,e) ->
          Value.mk_func a e
        | Ctor (i,e) ->
          let v = evaluate e in
          Value.mk_ctor i v
        | Match (e,branches) as match_expr ->
          let v = evaluate e in
          let branch_o =
            List.find_map
              ~f:(fun (p,e) ->
                  Option.map
                    ~f:(fun ms -> (ms,e))
                    (Value.matches_pattern_and_extractions p v))
              branches
          in
          let (replacements,e) =
            begin match branch_o with
              | None ->
                failwith
                  ((Value.show v)
                   ^ " not matched: \n "
                   ^ (Expr.show_t_node match_expr))
              | Some b -> b
            end
          in
          let replacements =
            List.map ~f:(fun (i,v) -> (i,Value.to_exp v)) replacements
          in
          let v = evaluate (Expr.replace_holes replacements e) in
          v
        | Fix (i,_,e') ->
          evaluate (Expr.replace i e e')
        | Tuple es ->
          let vs =
            List.map ~f:evaluate es
          in
          Value.mk_tuple vs
        | Proj (i,e) ->
          let v = evaluate e in
          begin match Value.node v with
            | Wildcard -> Value.mk_wildcard
            | Tuple vs -> List.nth_exn vs i
            | _ -> failwith "bad"
          end
        | Unctor (i,e) ->
          let v = evaluate e in
          let (i',e) = Value.destruct_ctor_exn v in
          assert (Id.equal i  i');
          e
      in
      l.eval <- Some ans;
      ans
    | Some ans ->
      ans
  end

let evaluate_with_holes
    ~eval_context:(i_e:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t =
  let e = Expr.replace_holes ~i_e e in
  evaluate e

let rec safe_evaluate
    (e:Expr.t)
  : Value.t option =
  try
    Some (evaluate e)
  with _ ->
    None

let rec safe_evaluate_with_holes
    ~(eval_context:(Id.t * Expr.t) list)
    (e:Expr.t)
  : Value.t option =
  try
    Some (evaluate_with_holes ~eval_context e)
  with _ ->
    None
