open Core
open Lang

let rec fix_to_let (e:exp) : exp =
  let trans : exp -> exp = fix_to_let in
  match e with
  | EVar _ -> e
  | EApp (e1, e2) -> EApp (trans e1, trans e2)
  | EFun (x, e) -> EFun (x, trans e)
  | ELet (f, is_rec, xs, t, e1, e2) ->
      ELet (f, is_rec, xs, t, trans e1, trans e2)
  | ECtor (c, e) -> ECtor (c, trans e)
  | ETuple es -> ETuple (List.map ~f:trans es)
  | EProj (n, e) -> EProj (n, trans e)
  | ERcd les -> ERcd (List.map ~f:(fun (l,e) -> (l,trans e)) les)
  | ERcdProj (l, e) -> ERcdProj (l, trans e)
  | EMatch (e, bs) ->
      EMatch (trans e, List.map ~f:(fun (p, e) -> (p, trans e)) bs)
  | EPFun ios ->
      EPFun (List.map ~f:(fun (e1, e2) -> (trans e1, trans e2)) ios)
  | EFix (f, (x, t1), t2, e) ->
      if List.mem ~equal:String.equal (free_vars e) f then
        ELet (f, true, [(x, t1)], t2, trans e, EVar f)
      else
        EFun ((x, t1), trans e)
  | EUnit -> EUnit

let wrap_in_dlet (x:id) (t:typ) (e:exp) : decl = DLet (x, false, [], t, e)

let to_top_level (x:id) (t:typ) (e:exp) : decl =
  fix_to_let e |> wrap_in_dlet x t
