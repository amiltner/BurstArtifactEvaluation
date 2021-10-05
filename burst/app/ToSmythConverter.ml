open MyStdLib
open Burst
open Lang

module IdSet = Set.Make(Id)
module SmythLang = Smyth.Lang

module TypeMap = Map.Make(Type)
type type_to_type = SmythLang.typ TypeMap.t

let merge_tts tt1 tt2 =
  Map.merge_skewed tt1 tt2
    ~combine:(fun ~key:_ v1 v2
               -> if SmythLang.equal_typ v1 v2 then
                   v1
                 else
                   failwith "conflict")

let rec to_smyth_type
    (real_vars:IdSet.t)
    (adjoining_var:Id.t option)
    (tt:type_to_type)
    (t:Type.t)
  : (string * (string list * (string * SmythLang.typ) list)) list * SmythLang.typ * type_to_type =
  let to_smyth_type_simple = to_smyth_type real_vars adjoining_var tt in
  begin match TypeMap.find tt t with
    | Some mt -> ([],mt,tt)
    | None ->
      begin match Type.node t with
        | Named v ->
          (*if IdSet.mem real_vars v then*)
            ([],SmythLang.TData (Id.to_string v,[]),tt)
          (*else
            failwith ("non-real var: " ^ Id.show v)*)
        | Arrow (t1,t2) ->
          let (ds1,mt1,tt1) = to_smyth_type_simple t1 in
          let (ds2,mt2,tt2) = to_smyth_type_simple t2 in
          ((ds1@ds2), SmythLang.TArr (mt1, mt2), merge_tts tt1 tt2)
        | Tuple ts ->
          let (ds,mts,tts) = List.unzip3 (List.map ~f:to_smyth_type_simple ts) in
          let tt = List.fold_left tts ~init:TypeMap.empty ~f:merge_tts in
          (List.concat ds, SmythLang.TTuple mts, tt)
        | Mu (i,t) ->
          (*let fresh = IdSet.fresh_id used_ids i in*)
          assert
            (Option.is_some (Type.destruct_variant t)
              && (Option.equal Id.equal (Some i) adjoining_var));
          let real_vars = IdSet.add real_vars i in
          to_smyth_type real_vars adjoining_var tt t
        | Variant branches ->
          let i = Option.value_exn adjoining_var in
          let (unflattened_bs,its,tts) =
            List.unzip3 (
              List.map
                ~f:(fun (i,t) ->
                      let (b,mt,tt) =
                        to_smyth_type real_vars adjoining_var tt t
                       in (b,(Id.to_string i,mt),tt))
                branches)
          in
          let tt = List.fold_left tts ~init:tt ~f:merge_tts in
          let bs = List.concat unflattened_bs in
          let tt = TypeMap.set tt ~key:(Type.mk_variant branches) ~data:(SmythLang.TData (Id.to_string i,[])) in
          ((Id.to_string i,([],its))::bs, SmythLang.TData (Id.to_string i,[]),tt)
      end
  end

let to_smyth_type_basic
    (tt:type_to_type)
    (t:Type.t)
  : SmythLang.typ =
  snd3 (to_smyth_type IdSet.empty None tt t)

let rec to_pat
    (p:Pattern.t)
  : SmythLang.pat =
  begin match p with
    | Tuple ps -> PTuple (List.map ~f:to_pat ps)
    | Ctor _ -> failwith (Pattern.show p)
    | Var i -> PVar (Id.to_string i)
    | Wildcard -> PWildcard
  end

let rec to_smyth_exp_with_replacement
    (e:Expr.t)
    (ireps:(Id.t * SmythLang.exp) list)
    (tt:type_to_type)
  : SmythLang.exp =
  let to_smyth_exp e = to_smyth_exp_with_replacement e ireps tt in
  (begin match Expr.node e with
     | Var i ->
       begin match List.Assoc.find ~equal:Id.equal ireps i with
         | Some e -> e
         | None -> SmythLang.EVar (Id.to_string i)
       end
     | App (e1,e2) -> SmythLang.EApp (false, to_smyth_exp e1, EAExp (to_smyth_exp e2))
    | Func ((i,_),e) ->
      SmythLang.EFix (None,SmythLang.PatParam (PVar (Id.to_string i)), to_smyth_exp e)
    | Ctor (i,e) ->
      ECtor (Id.to_string i,[],to_smyth_exp e)
    | Match (e,branches) ->
      let me = to_smyth_exp e in
      let mbranches =
        List.map
          ~f:(fun (p,e) ->
              begin match p with
                | Ctor (i,p') ->
                  (Id.to_string i,(to_pat p',to_smyth_exp e))
                | _ -> failwith "invalid"
              end)
          branches
      in
      SmythLang.ECase (me,mbranches)
    | Fix (i,t,e) ->
      let ((i',_),e) = Expr.destruct_func_exn e in
      let me = to_smyth_exp e in

      let e = SmythLang.EFix (Some (Id.to_string i), PatParam (PVar (Id.to_string i')), me) in
      SmythLang.ETypeAnnotation (e,to_smyth_type_basic tt t)
    | Tuple es ->
      if List.length es = 0 then
        SmythLang.ETuple []
      else
        SmythLang.ETuple (List.map ~f:to_smyth_exp es)
    | Proj (i,e) ->
      SmythLang.EProj (100000, i+1, to_smyth_exp e)
    | _ -> failwith "invalid"
   end)

let to_smyth_exp
    (e:Expr.t)
    (tt:type_to_type)
  : SmythLang.exp =
  to_smyth_exp_with_replacement e [] tt

let convert_decl_list_to_smyth
    (ds:Declaration.t list)
  : SmythLang.datatype_ctx * (string * SmythLang.exp) list * type_to_type =
  let (tt,sigma,ies) =
    List.fold_left
      ~f:(fun (tt,sigma,iesrev) d ->
          Declaration.fold
            ~type_f:(fun i t ->
                let (ctors,st,tt) = to_smyth_type IdSet.empty (Some i) tt t in
                let sigma = sigma@ctors in
                let tt = TypeMap.set tt ~key:(Type.mk_named i) ~data:st in
                (tt,sigma,iesrev))
            ~expr_f:(fun i e ->
                let e = to_smyth_exp e tt in
                (tt,sigma,(Id.to_string i,e)::iesrev))
            d)
      ~init:(TypeMap.empty,[],[])
      ds
  in
  (sigma, List.rev ies,tt)

let convert_problem_examples_type_to_smyth
    (p:Problem.t)
    (examples:((Expr.t list) * Expr.t) list)
    (tins:Type.t list)
    (tout:Type.t)
  : SmythLang.datatype_ctx * (string * (SmythLang.typ * SmythLang.exp)) list
    * ((SmythLang.exp list) * SmythLang.exp) list
    * SmythLang.typ * (SmythLang.typ list) * SmythLang.typ =
  let (_,ds,t,_,_) = p.unprocessed in
  let (ds,ies,tt) = convert_decl_list_to_smyth ds in
  let iets =
    List.map
      ~f:(fun (i,e) ->
          let t = Context.find_exn p.ec (Id.create i) in
          let t = to_smyth_type_basic tt t in
          (i,(t,e)))
      ies
  in
  let examples =
    List.map
      ~f:(fun (e1,e2) -> (List.map ~f:(fun e -> to_smyth_exp e tt) e1, to_smyth_exp e2 tt))
      examples
  in
  let t = to_smyth_type_basic tt t in
  let tins = List.map ~f:(to_smyth_type_basic tt) tins in
  let tout = to_smyth_type_basic tt tout in
  (ds,iets,examples,t,tins,tout)

