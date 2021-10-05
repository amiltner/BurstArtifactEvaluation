open MyStdLib
open Burst
open Lang

module SMythLang = Smyth.Lang

let rec convert_type : SMythLang.typ -> Type.t =
  function [@warning "-8"]
  | TData (id,_)          -> Type.mk_named (Id.create id)
  | TArr (typ1, typ2) -> Type.mk_arrow (convert_type typ1) (convert_type typ2)
  | TTuple (typlist)  -> Type.mk_tuple (List.map ~f:convert_type typlist)

let rec pat_to_pat
    (p:SMythLang.pat)
  : Pattern.t =
  begin match p with
    | PVar s -> Pattern.Var (Id.create s)
    | PTuple ps -> Pattern.Tuple (List.map ~f:pat_to_pat ps)
    | PWildcard -> Pattern.Wildcard
  end

let  rec convert_expr (counter:int) (e : SMythLang.exp) : Expr.t * int =
  begin match e with
    | SMythLang.ETypeAnnotation (e,_) -> convert_expr counter e
  | SMythLang.EVar id
    -> (Expr.mk_var (Id.create id),counter)
  | SMythLang.EApp (_, exp1, exp2)
    ->
    begin match exp2 with
      | EAExp exp2 ->
        let (e1,counter) = (convert_expr counter exp1) in
        let (e2,counter) = (convert_expr counter exp2) in
        (Expr.mk_app e1 e2,counter)
      | _ -> failwith "invalid"
    end
  | SMythLang.ECtor (id, _, exp)
    ->
    let (e,counter) = (convert_expr counter exp) in
    (Expr.mk_ctor (Id.create id) e,counter)
  | SMythLang.ETuple explist
    ->
    let (es,counter) =
      List.fold_right
        ~f:(fun e (es,counter) ->
            let (e,counter) = convert_expr counter e in
            (e::es,counter))
        ~init:([],counter)
        explist
    in
    (Expr.mk_tuple es,counter)
  | SMythLang.EProj (_, int, exp)
    ->
    let (e,counter) = (convert_expr counter exp) in
    (Expr.mk_proj (int-1) e,counter)
  | SMythLang.EFix (fido, argi, body)
    ->
    begin match argi with
      | PatParam (PVar argi) ->
        begin match fido with
          | None ->
            let (e,counter) = (convert_expr counter body) in
            (Expr.mk_func (Id.create argi,Type._unit) e,counter)
          | Some fid ->
            let (e,counter) = (convert_expr counter body) in
            (Expr.mk_fix (Id.create fid) Type._unit
               (Expr.mk_func (Id.create argi,Type._unit) e)
            ,counter)
        end
      | _ -> failwith "invalid"
    end
  | SMythLang.ECase (exp, branchlist)
    ->
    let (e,counter) = convert_expr counter exp in
    let branches =
      List.map
        ~f:(fun (sbr,(svar,e)) ->
            let (e,counter) = convert_expr counter e in
            (Pattern.Ctor (Id.create sbr, pat_to_pat svar),e))
        branchlist
    in
    (Expr.mk_match e branches,counter)
  | EHole _ -> (Expr.mk_unit,counter)
  | EAssert _ -> failwith "assert"
  end

let convert_expr (e : SMythLang.exp) : Expr.t =
  fst (convert_expr 0 e)
