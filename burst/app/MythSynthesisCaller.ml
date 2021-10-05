open MyStdLib
open Burst
open Lang

module DSToMyth = struct
  module IdSet = Set.Make(Id)
  module MythLang = Myth.Lang

  module TypeMap = Map.Make(Type)
  type type_to_type = MythLang.MType.t TypeMap.t

  let merge_tts tt1 tt2 =
    Map.merge_skewed tt1 tt2
      ~combine:(fun ~key:_ v1 v2
                 -> if MythLang.MType.equal v1 v2 then
                     v1
                   else
                     failwith "conflict")

  let rec to_myth_type
      (real_vars:IdSet.t)
      (adjoining_var:Id.t option)
      (tt:type_to_type)
      (t:Type.t)
    : (MythLang.id * MythLang.ctor list) list * MythLang.typ * type_to_type =
    let to_myth_type_simple = to_myth_type real_vars adjoining_var tt in
    begin match TypeMap.find tt t with
      | Some mt -> ([],mt,tt)
      | None ->
        begin match Type.node t with
          | Named v ->
            ([],MythLang.TBase (Id.to_string v),tt)
          | Arrow (t1,t2) ->
            let (ds1,mt1,tt1) = to_myth_type_simple t1 in
            let (ds2,mt2,tt2) = to_myth_type_simple t2 in
            ((ds1@ds2), MythLang.TArr (mt1, mt2), merge_tts tt1 tt2)
          | Tuple ts ->
            if List.length ts = 0 then
              ([],MythLang.TUnit,tt)
            else
              let (ds,mts,tts) = List.unzip3 (List.map ~f:to_myth_type_simple ts) in
              let tt = List.fold_left tts ~init:TypeMap.empty ~f:merge_tts in
              (List.concat ds, MythLang.TTuple mts, tt)
          | Mu (i,t) ->
            (*let fresh = IdSet.fresh_id used_ids i in*)
            assert
              (Option.is_some (Type.destruct_variant t)
               && (Option.equal Id.equal (Some i) adjoining_var));
            let real_vars = IdSet.add real_vars i in
            to_myth_type real_vars adjoining_var tt t
          | Variant branches ->
            let i = Option.value_exn adjoining_var in
            let (unflattened_bs,its,tts) =
              List.unzip3 (
                List.map
                  ~f:(fun (i,t) ->
                      let (b,mt,tt) =
                        to_myth_type real_vars adjoining_var tt t
                      in (b,(Id.to_string i,mt),tt))
                  branches)
            in
            let tt = List.fold_left tts ~init:tt ~f:merge_tts in
            let bs = List.concat unflattened_bs in
            let tt = TypeMap.set tt ~key:(Type.mk_variant branches) ~data:(MythLang.TBase (Id.to_string i)) in
            ((Id.to_string i,its)::bs, MythLang.TBase (Id.to_string i),tt)
        end
    end

  let to_myth_type_basic
      (tt:type_to_type)
      (t:Type.t)
    : MythLang.typ =
    snd3 (to_myth_type IdSet.empty None tt t)

  let rec pattern_to_myth
      (p:Pattern.t)
    : MythLang.pattern =
    begin match p with
      | Tuple ps -> PTuple (List.map ~f:pattern_to_myth ps)
      | Ctor _ -> failwith "invalid"
      | Var i -> PVar (Id.to_string i)
      | Wildcard -> PWildcard
    end

  let rec to_myth_exp
      (tt:type_to_type)
      (e:Expr.t)
    : MythLang.exp =
    let to_myth_exp = to_myth_exp tt in
    (begin match Expr.node e with
       | Wildcard -> failwith "no conversion"
       | Eq _ -> failwith "no conversion"
       | Var i -> MythLang.EVar (Id.to_string i)
       | Unctor _ -> failwith "no conversion"
       | App (e1,e2) -> MythLang.EApp (to_myth_exp e1, to_myth_exp e2)
       | Func ((i,t),e) ->
         let mt = to_myth_type_basic tt t in
         MythLang.EFun ((Id.to_string i,mt), to_myth_exp e)
       | Ctor (i,e) ->
         ECtor (Id.to_string i,to_myth_exp e)
       | Match (e,branches) ->
         let me = to_myth_exp e in
         let mbranches =
           List.map
             ~f:(fun (b,e) ->
                 begin match b with
                   | Pattern.Ctor (b,p) -> ((Id.to_string b,Some (pattern_to_myth p)), to_myth_exp e)
                   | _ -> failwith "ah"
                 end)
             branches
         in
         MythLang.EMatch (me,mbranches)
       | Fix (i,t,e) ->
         let (t1,t2) = Type.destruct_arr_exn t in
         let ((i',t'),e) = Expr.destruct_func_exn e in
         assert (Type.equal t1 t');
         let mt1 = to_myth_type_basic tt t1 in
         let mt2 = to_myth_type_basic tt t2 in
         let me = to_myth_exp e in
         MythLang.EFix (Id.to_string i, (Id.to_string i',mt1), mt2, me)
       | Tuple es ->
         if List.length es = 0 then
           MythLang.EUnit
         else
           MythLang.ETuple (List.map ~f:to_myth_exp es)
       | Proj (i,e) ->
         MythLang.EProj (i+1, to_myth_exp e)
     end)

  let convert_decl_list_to_myth
      (ec:Context.Exprs.t)
      (ds:Declaration.t list)
    : MythLang.decl list * type_to_type =
    let (tt,ds) =
      List.fold_left
        ~f:(fun (tt,dsrev) d ->
            Declaration.fold
              ~type_f:(fun i t ->
                  let (ctors,mt,tt) = to_myth_type IdSet.empty (Some i) tt t in
                  let new_ds =
                    List.map
                      ~f:(fun (i,cs) -> MythLang.DData (i,cs))
                      ctors
                  in
                  let tt = TypeMap.set tt ~key:(Type.mk_named i) ~data:mt in
                  (tt,new_ds@dsrev))
              ~expr_f:(fun i e ->
                  let new_d =
                    MythLang.DLet
                      (Id.to_string i
                      ,false
                      ,[]
                      ,to_myth_type_basic tt (Context.find_exn ec i)
                      ,to_myth_exp tt e)
                  in
                  (tt,new_d::dsrev))
              d)
        ~init:(TypeMap.empty,[])
        ds
    in
    (List.rev ds, tt)

  let to_myth_exp_with_problem ~(problem:Problem.t) (e:Expr.t) : MythLang.exp =
    let (_,decls,_,_,_) = problem.unprocessed in
    let (_,tt) = convert_decl_list_to_myth problem.ec decls in
    to_myth_exp tt e

  let to_pretty_myth_string ~(problem:Problem.t) (e:Expr.t) : string =
    let me = to_myth_exp_with_problem ~problem e
    in Myth.Pp.pp_exp me

  let rec convert_ioes_to_pfuns
      (ioes:(MythLang.exp list * MythLang.exp) list)
    : MythLang.exp =
    if (List.is_empty (fst (List.hd_exn ioes))) then
      let deduped =
        List.dedup_and_sort
          ~compare:(pair_compare (compare_list ~cmp:MythLang.compare_exp) MythLang.compare_exp)
          ioes
      in
      begin match deduped with
        | [[],e] -> e
        | _ -> failwith "bad examples"
      end
    else
      let kvps =
        List.map
          ~f:(fun (ins,out) ->
              begin match ins with
                | h::t -> (h,(t,out))
                | _ -> failwith "ill formed"
              end)
          ioes
      in
      let grouped_by_keys =
        group_by_keys
          ~is_eq:(fun e1 e2 -> is_equal (MythLang.compare_exp e1 e2))
          kvps
      in
      let pfun_ios =
        List.map
          ~f:(fun (i,ioes) -> (i,convert_ioes_to_pfuns ioes))
          grouped_by_keys
      in
      MythLang.EPFun pfun_ios

  let convert_problem_examples_type_to_myth
      (p:Problem.t)
      (examples:((Expr.t list) * Expr.t) list)
    : MythLang.decl list
      * MythLang.exp
      * MythLang.typ =
    let (_,decls,desired_t,_,_) = p.unprocessed in
    let (ds,tt) = convert_decl_list_to_myth p.ec decls in
    let ioes =
      List.map
        ~f:(fun (es,e) -> (List.map ~f:(to_myth_exp tt) es,to_myth_exp tt e))
        examples
      in
    let pfun = convert_ioes_to_pfuns ioes in
    (*let pfuns =
      List.map
        ~f:(fun (es,e) ->
            List.fold_right
              ~f:(fun e acc ->
                  let e = to_myth_exp tt e in
                  MythLang.EPFun [e,acc])
              ~init:(to_myth_exp tt e)
              es)
        examples
      in*)
    let t = to_myth_type_basic tt desired_t in
    (ds,pfun,t)
end

module MythToDS = struct
  let rec explode (binder: Expr.t) : Myth.Lang.pattern list -> (Expr.t * Id.t) list =
    let rec helper i acc =
      function
      | [] -> acc
      | (Myth.Lang.PVar id) :: plist
        -> helper (i + 1) (((Expr.mk_proj i binder), Id.create id) :: acc) plist
      | (Myth.Lang.PTuple _plist) :: plist
        -> helper (i + 1) ((explode (Expr.mk_proj i binder) _plist) @ acc) plist
      | _ :: plist
        -> helper (i + 1) acc plist
    in helper 0 []

  let rec pattern_from_myth
      (p:Myth.Lang.pattern)
    : Pattern.t =
    begin match p with
      | PVar id -> Pattern.Var (Id.create id)
      | PTuple ps -> Pattern.Tuple (List.map ~f:pattern_from_myth ps)
      | PWildcard -> Pattern.Wildcard
      | _ -> failwith "invalid"
    end

  let rec convert_type : Myth.Lang.typ -> Type.t =
    function [@warning "-8"]
    | TBase id          -> Type.mk_named (Id.create id)
    | TArr (typ1, typ2) -> Type.mk_arrow (convert_type typ1) (convert_type typ2)
    | TTuple (typlist)  -> Type.mk_tuple (List.map ~f:convert_type typlist)
    | TUnit             -> Type._unit

  let convert_arg ((id, typ) : Myth.Lang.arg) : Param.t =
    (Id.create id, convert_type typ)

  let create_fresh_var (counter:int) : Id.t*int =
    (Id.create ("N_fresh_var_" ^ (string_of_int counter)),counter+1)

  let  [@warning "-8"] rec convert_expr (counter:int) (e : Myth.Lang.exp) : Expr.t * int =
    begin match e with
      | Myth.Lang.EUnit
        -> (Expr.mk_unit,counter)
      | Myth.Lang.EVar id
        -> (Expr.mk_var (Id.create id),counter)
      | Myth.Lang.EApp (exp1, exp2)
        ->
        let (e1,counter) = (convert_expr counter exp1) in
        let (e2,counter) = (convert_expr counter exp2) in
        ((Expr.mk_app e1 e2),counter)
      | Myth.Lang.ECtor (id, exp)
        ->
        let (e,counter) = (convert_expr counter exp) in
        (Expr.mk_ctor (Id.create id) e,counter)
      | Myth.Lang.ETuple explist
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
      | Myth.Lang.EProj (int, exp)
        ->
        let (e,counter) = (convert_expr counter exp) in
        (Expr.mk_proj (int-1) e,counter)
      | Myth.Lang.EFix (id, ((_, arg_typ) as arg), typ, body)
        ->
        let (e,counter) = (convert_expr counter body) in
        (Expr.mk_fix (Id.create id) (convert_type (Myth.Lang.TArr (arg_typ, typ)))
                   (Expr.mk_func (convert_arg arg) e)
        ,counter)
      | Myth.Lang.EFun (arg, body)
        ->
        let (e,counter) = (convert_expr counter body) in
        (Expr.mk_func (convert_arg arg) e,counter)
      | Myth.Lang.ELet (id, _, arglist, typ, exp, body)
        ->
        let (e,counter) = (convert_expr counter exp) in
        let (body,counter) = (convert_expr counter body) in
        let arglist = (List.map ~f:convert_arg arglist)
        in (Expr.mk_app (Expr.mk_fix (Id.create id)
                                 (List.fold
                                    arglist
                                    ~init:(convert_type typ)
                                    ~f:(fun etyp (_, t) -> Type.mk_arrow t etyp))
                                 (List.fold
                                    arglist
                                    ~init:(e)
                                    ~f:(fun eacc arg -> Expr.mk_func arg eacc)))
                      (body),counter)
      | Myth.Lang.EMatch (exp, branchlist)
        ->
        let (e,counter) = convert_expr counter exp in
        let (branches,counter) =
          List.fold_right
            ~f:(fun b (bs,counter) ->
                let (b,counter) = (convert_branch counter b) in
                (b::bs,counter))
            ~init:([],counter)
            branchlist
        in
        (Expr.mk_match e
           branches,counter)
    end

  and convert_branch (counter:int) : Myth.Lang.branch -> ((Pattern.t * Expr.t) * int) =
    function [@warning "-8"]
    | ((id, None), exp) ->
      let (e,counter) = convert_expr counter exp in
      ((Pattern.Ctor (Id.create id,Pattern.Tuple []), e),counter)
    | ((id, Some p), exp)
      -> let (e,counter) = (convert_expr counter exp) in
      ((Pattern.Ctor (Id.create id, pattern_from_myth p),e),counter)

  let convert_expr (e : Myth.Lang.exp) : Expr.t =
    fst (convert_expr 0 e)
end

type t = Problem.t * Context.t * Type.t * Type.t

let init
    ~(problem:Problem.t)
    ~(context:Context.t)
    ~(tin:Type.t)
    ~(tout:Type.t)
  : t =
  (problem,context,tin,tout)

let problem (p,_,_,_) = p
let context (_,c,_,_) = c
let tin (_,_,t,_) = t
let tout (_,_,_,t) = t

let rec term_of_type
    (c:Context.t)
    (t:Type.t)
  : Expr.t =
  begin match Type.node t with
    | Named i -> term_of_type c (Context.find_exn c.tc i)
    | Arrow (t1,t2) ->
      Expr.mk_func
        (Id.create "x",t1)
        (term_of_type c t2)
    | Tuple ts ->
      Expr.mk_tuple (List.map ~f:(term_of_type c) ts)
    | Mu _ -> failwith "TODO"
    | Variant bs ->
      let (i,t) = List.hd_exn bs in
      Expr.mk_ctor i (term_of_type c t)
  end

let synth
    (a:t)
    (ios:(Value.t * Value.t) list)
  : Expr.t =
  if (List.length ios = 0) then
    term_of_type (context a) (Type.mk_arrow (tin a) (tout a))
  else
    let ios = List.map ~f:(fun (v1,v2) -> (Value.to_exp v1,Value.to_exp v2)) ios in
    let ios =
      List.map
        ~f:(fun (vin,vout) ->
            begin match Expr.destruct_tuple vin with
              | Some vins -> (vins,vout)
              | None -> ([vin],vout)
            end)
        ios
    in
    print_endline
      (string_of_list
         (string_of_pair (string_of_list Expr.show) Expr.show)
         ios);
    let (decls,examples,t) = DSToMyth.convert_problem_examples_type_to_myth (problem a) ios in
    let (sigma,gamma) =
      Myth.Typecheck.Typecheck.check_decls
        Myth.Sigma.Sigma.empty
        Myth.Gamma.Gamma.empty
        decls
    in
    print_endline (Myth.Pp.pp_exp examples);
    let env = Myth.Eval.gen_init_env decls in
    let w = Myth.Eval.gen_init_world env [examples] in
    let myth_exp =
      (Myth.Synth.synthesize
         sigma
         env
         (Myth.Rtree.create_rtree
            sigma
            gamma
            env
            t w 0))
    in
    let e =
      MythToDS.convert_expr
        (List.hd_exn myth_exp)
    in
    begin match Type.destruct_tuple (tin a) with
      | None -> e
      | Some tins ->
        let argv = Id.create "x" in
        let arge = Expr.mk_var argv in
        Expr.mk_func
          (argv,(tin a))
          (fst (List.fold_left
                  ~f:(fun (acce,i) tin ->
                      (Expr.mk_app
                         acce
                         (Expr.mk_proj i arge),
                       i+1))
                  ~init:(e,0)
                  tins))
    end

let synth
    (a:t)
    (ios:(Value.t * Value.t) list)
  : t * Expr.t =
  (a,synth a ios)
