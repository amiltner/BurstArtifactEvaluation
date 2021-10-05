open MyStdLib
open Lang

open Typecheck

type unprocessed_spec =
  | UIOEs of (Expr.t list * Expr.t) list
  | UPost of Expr.t
  | UEquiv of Expr.t
[@@deriving eq, hash, ord, show]

type spec =
  | IOEs of (Value.t * Value.t) list
  | Post of (Value.t -> Value.t -> bool)
  | Equiv of (Value.t -> Value.t)
[@@deriving show]

type t_unprocessed = string list
                     * Declaration.t list
                     * Type.t
                     * Declaration.t list
                     * unprocessed_spec
[@@deriving show]

let update_import_base
    (ss:string list)
    (fname:string)
  : string list =
  let dir = Filename.dirname fname in
  List.map ~f:((^) (dir ^ "/")) ss

let update_all_import_bases
    ((ss,ds,t,dss,ios):t_unprocessed)
    (fname:string)
  : t_unprocessed =
  let ss = update_import_base ss fname in
  (ss,ds,t,dss,ios)

let extract_file
    ((ss,ds,t,dss,ios):t_unprocessed)
  : (string * t_unprocessed) option =
  begin match split_by_last ss with
    | None -> None
    | Some (ss,h) -> Some (h,(ss,ds,t,dss,ios))
  end

let merge_unprocessed
    ((ss,ds,t,dss,ios):t_unprocessed)
    ((imports,decls):string list * Declaration.t list)
  : t_unprocessed =
  (imports@ss,decls@ds,t,dss,ios)

type t = {
  synth_type   : Type.t * Type.t          ;
  ec           : Context.Exprs.t          ;
  tc           : Context.Types.t          ;
  vc           : Context.Variants.t       ;
  spec     : spec ;
  i     : (Value.t * Value.t) list ;
  eval_context : (Id.t * Expr.t) list     ;
  unprocessed  : t_unprocessed            ;
  full_ec           : Context.Exprs.t          ;
  full_tc           : Context.Types.t          ;
  full_vc           : Context.Variants.t       ;
  full_eval_context : (Id.t * Expr.t) list     ;
}
[@@deriving make]


let extract_variants
    (t:Type.t)
    : (Context.Variants.key * Context.Variants.value) list =
  fst (Type.fold
         ~name_f:(fun i -> ([],Type.mk_named i))
         ~arr_f:(fun (vs1,t1) (vs2,t2) -> (vs1@vs2,Type.mk_arrow t1 t2))
         ~tuple_f:(fun vss_ts ->
                     let (vss,ts) = List.unzip vss_ts in
                     (List.concat vss, Type.mk_tuple ts))
        ~mu_f:(fun _ vs -> vs)
        ~variant_f:(fun ids_vss_ts ->
                      let (ids,vss_ts) = List.unzip ids_vss_ts in
                      let (vss,ts) = List.unzip vss_ts in
                      let ids_ts = List.zip_exn ids ts in
                      let ids_map = List.map ~f:(fun id -> (id,ids_ts)) ids in
                      (ids_map@(List.concat vss), Type.mk_variant ids_ts))
        t)

let process_decl_list
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (i_e:(Id.t * Expr.t) list)
    (ds:Declaration.t list)
  : (Context.Exprs.t * Context.Types.t * Context.Variants.t * (Id.t * Expr.t) list)
    * (Context.Exprs.t * Context.Types.t * Context.Variants.t * (Id.t * Expr.t) list) =
    (List.fold_left
       ~f:(fun ((new_ec,new_tc,new_vc,new_i_e),(ec,tc,vc,i_e)) decl ->
           Declaration.fold
             ~type_f:(fun i t ->
                 let all_variants = extract_variants t in
                 ((new_ec
                  ,Context.set new_tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Context.set vc ~key:k ~data:v)
                      ~init:new_vc
                      all_variants
                  ,new_i_e)
                 ,(ec
                  ,Context.set tc ~key:i ~data:t
                  ,List.fold_left
                      ~f:(fun vc (k,v) -> Context.set vc ~key:k ~data:v)
                      ~init:vc
                      all_variants
                  ,i_e))
               )
             ~expr_f:(fun i e ->
                 let t = typecheck_exp ec tc vc e in
                 ((Context.set new_ec ~key:i ~data:t
                  ,new_tc
                  ,new_vc
                  ,(i,e)::new_i_e)
                 ,(Context.set ec ~key:i ~data:t
                  ,tc
                  ,vc
                  ,(i,e)::i_e))
               )
             decl)
       ~init:(((Context.empty,Context.empty,Context.empty,[])
              ,(ec,tc,vc,i_e)))
       ds)

let st_to_pair
    (synth_type:Type.t)
  : Type.t * Type.t =
  fold_until_completion
    ~f:(fun (acc,t) ->
        begin match Type.node t with
          | Type.Arrow (t1,t2) -> Left (t1::acc,t2)
          | _ -> Right (Type.mk_tuple (List.rev acc),t)
        end)
    ([],synth_type)

let process_spec
    (ec:Context.Exprs.t)
    (tc:Context.Types.t)
    (vc:Context.Variants.t)
    (i_e:(Id.t * Expr.t) list)
    (synth_type:Type.t)
    (us:unprocessed_spec) : spec =
  begin match us with
    | UIOEs us ->
      List.iter
        ~f:(fun (es,e) ->
            let typecheck = Typecheck.typecheck_exp ec tc vc in
            let es_ts =
              List.map
                ~f:typecheck
                es
            in
            let e_t = typecheck e in
            let ex_t =
              List.fold_right
                ~f:Type.mk_arrow
                ~init:e_t
                es_ts
            in
            if Typecheck.type_equiv tc synth_type ex_t then
              ()
            else
              failwith "example doesn't satisfy the expected type")
        us;
      let examples =
        List.map
          ~f:(fun (es,e) ->
              let vs =
                List.map
                  ~f:(Eval.evaluate_with_holes ~eval_context:i_e)
                  es
              in
              let v =
                Eval.evaluate_with_holes
                  ~eval_context:i_e
                  e
              in
              (Value.mk_tuple vs,v))
          us
      in
      IOEs examples
    | UEquiv e ->
      let t = Typecheck.typecheck_exp ec tc vc e in
      assert (Typecheck.type_equiv tc t synth_type);
      let runner =
        fun v1 ->
          let real_e =
            begin match Value.destruct_tuple v1 with
              | None -> Expr.mk_app e (Value.to_exp v1)
              | Some vs ->
                List.fold
                  ~f:(fun acc v -> Expr.mk_app acc (Value.to_exp v))
                  ~init:e
                  vs
            end
          in
          Eval.evaluate_with_holes ~eval_context:i_e real_e
      in
      Equiv runner
    | UPost e ->
      let (tin,tout) = st_to_pair synth_type in
      let t = Typecheck.typecheck_exp ec tc vc e in
      assert
        (Typecheck.type_equiv
           tc
           t
           (Type.mk_arrow tin (Type.mk_arrow tout Type._bool)));
      Post
        (fun v1 v2 ->
           let e1 = Value.to_exp v1 in
           let e2 = Value.to_exp v2 in
           let full_exp = Expr.mk_app (Expr.mk_app e e1) e2 in
           let vout = Eval.safe_evaluate_with_holes ~eval_context:i_e full_exp in
           begin match vout with
             | None -> false
             | Some vout -> Value.equal vout Value.true_
           end)
  end

let rec process (unprocessed : t_unprocessed) : t =
  let (_,decs,synth_type,dss,uspec) = unprocessed in
  let (ec,tc,vc,eval_context) =
    fst
      (process_decl_list
         Context.empty
         Context.empty
         Context.empty
         []
         decs)
  in
  let st = synth_type in
  let synth_type = st_to_pair synth_type in
  let (full_ec,full_tc,full_vc,full_eval_context) =
    snd
      (process_decl_list
         ec
         tc
         vc
         eval_context
         dss)
  in
  let spec = process_spec full_ec full_tc full_vc full_eval_context st uspec in
  make
    ~ec
    ~tc
    ~vc
    ~eval_context
    ~unprocessed
    ~synth_type
    ~spec
    ~full_ec
    ~full_tc
    ~full_vc
    ~full_eval_context
    ()

let extract_context
    (p:t)
  : Context.t =
  {
    ec = p.ec ;
    tc = p.tc ;
    vc = p.vc ;
    full_ec = p.full_ec ;
    full_tc = p.full_tc ;
    full_vc = p.full_vc ;
    evals = p.eval_context ;
    full_evals = p.full_eval_context ;
  }
