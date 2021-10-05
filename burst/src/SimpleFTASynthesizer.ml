open MyStdLib
open Lang

module Create(B : Automata.AutomatonBuilder) (*: Synthesizers.PredicateSynth.S *)= struct
  module A = B(FTAConstructor.Transition)(FTAConstructor.State)
  module C = FTAConstructor.Make(A)

  let __INITIAL_SIZE__ = 2
  let __INITIAL_MVM__ = 3.0

  module ValToC = DictOf(Value)(C)
  module ValueSet = SetOf(Value)
  module IndividualSettings = struct
    type t =
      {
        max_value_multiplier : Float.t ;
      }
    [@@deriving eq, hash, ord, show]

    let initial =
      {
        max_value_multiplier = __INITIAL_MVM__ ;
      }

    let increase_mvm is =
      {
        max_value_multiplier = is.max_value_multiplier +. 1.0 ;
      }
  end

  module GlobalState = struct
    module D = DictOf(Value)(IndividualSettings)
    type t =
      {
        d : D.t ;
        size : int ;
      }
    [@@deriving eq, hash, ord, show]

    let empty : t =
      {
        d = D.empty ;
        size = __INITIAL_SIZE__ ;
      }

    let lookup
        (gs:t)
        (v:Value.t)
      : IndividualSettings.t =
      begin match D.lookup gs.d v with
        | None -> IndividualSettings.initial
        | Some is -> is
      end

    let upgrade_from_failed_isect
        (gs:t)
      : t =
      { gs with size = gs.size+1; }

    let increase_max_multiplier
        (gs:t)
        (v:Value.t)
      : t =
      let is = lookup gs v in
      let is = IndividualSettings.increase_mvm is in
      { gs with
        d = D.insert gs.d v is
      }

    let get_num_applications
        (gs:t)
      : int =
      gs.size

    let get_max_value_multiplier
        (s:t)
        (v:Value.t)
      : Float.t =
      let is = lookup s v in
      is.max_value_multiplier
  end

  let strict_functional_subvalue
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      (v1:Value.t)
      (v2:Value.t)
    : bool =
    let break = fun v ->
      let t =
        Typecheck.typecheck_value
          context.ec
          context.tc
          context.vc
          v
      in
      C.TypeDS.is_recursive_type
        ds
        t
    in
    Value.strict_functional_subvalue ~break v1 v2

  let subvalues_full_of_same_type
      ~(context:Context.t)
      ~(ds:C.TypeDS.t)
      (v:Value.t)
    : Value.t list =
    let break = fun v ->
      let t =
        Typecheck.typecheck_value
          context.ec
          context.tc
          context.vc
          v
      in
      C.TypeDS.is_recursive_type
        ds
        t
    in
    let t = Typecheck.typecheck_value context.ec context.tc context.vc v in
    let subvalues_full = Value.functional_subvalues ~break v in
    List.filter
      ~f:(fun v ->
          Typecheck.type_equiv
            context.tc
            (Typecheck.typecheck_value context.ec context.tc context.vc v)
            t)
      subvalues_full

  type single_fta_response =
    | Generated of C.t
    | IncreaseMaxResponse

  let rec construct_single_fta
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(gs:GlobalState.t)
      (sub_calls:Value.t -> Value.t list)
      (input:Value.t)
      (valid_ios:Value.t -> Value.t -> bool)
    : C.t * GlobalState.t =
    let mvm = GlobalState.get_max_value_multiplier gs input in
    let ans_o =
      Consts.time
        Consts.initial_creation_times
        (fun _ ->
           let c =
             C.initialize_context
               ~context
               ~value_filter:((fun v' -> Value.size_min_expr v' <= Float.to_int (Float.of_int (Value.size_min_expr input)+.mvm)))
               ([tin;tout]
                @(List.map ~f:Type.mk_named (Context.keys context.tc))
                @(Context.data context.ec)
                @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) (Value.subvalues input)))
               [input]
               (tin,tout)
               valid_ios
           in
           let rec get_all_partial_apps
               (ins:Type.t list)
               (base:Expr.t)
               (extractor:Type.t -> Expr.t list)
             : ((Type.t list * Expr.t) list) =
             let basic = (ins,base) in
             let advanced =
               begin match ins with
                 | [] -> []
                 | h::t ->
                   if Option.is_some (Type.destruct_arr h) then
                     let apps = extractor h in
                     List.concat_map
                       ~f:(fun app ->
                           let base = Expr.mk_app base app in
                           get_all_partial_apps t base extractor)
                       apps
                   else
                     []
               end
             in
             basic::advanced
           in
           let context_conversions =
             List.concat_map
               ~f:(fun (i,e) ->
                   let t = Context.find_exn context.ec i in
                   let (ins,out) = Type.split_to_arg_list_result t in
                   let possible_partials =
                     get_all_partial_apps
                       ins
                       (Expr.mk_var i)
                       (fun t ->
                          List.filter_map
                            ~f:(fun (i,_) ->
                                let t' = Context.find_exn context.ec i in
                                if Typecheck.type_equiv context.tc t t' then
                                  (Some (Expr.mk_var i))
                                else
                                  None)
                            context.evals)
                   in
                   List.concat_map
                     ~f:(fun (ins,e) ->
                         let ins =
                           List.map
                             ~f:(fun int -> (int,TermClassification.Introduction))
                             ins
                         in
                         let e_func = Expr.replace_holes ~i_e:context.evals e in
                         let e_func = Value.to_exp (Eval.evaluate e_func) in
                         let evaluation vs =
                           let es = List.map ~f:Value.to_exp vs in
                           [Eval.evaluate
                              (List.fold
                                 ~f:Expr.mk_app
                                 ~init:e_func
                                 es)]
                         in
                         [(FTAConstructor.Transition.FunctionApp e,evaluation,ins,(out,TermClassification.Elimination))
                         ;(FTAConstructor.Transition.FunctionApp e,evaluation,ins,(out,TermClassification.Introduction))])
                     possible_partials)
               context.evals
           in
           let eval_conversion =
             List.concat_map
               ~f:(fun t ->
                   match Type.node t with
                   | Type.Arrow (t1,t2) ->
                     let evaluate vs =
                       begin match vs with
                         | [f;e] ->
                           let f = Value.to_exp f in
                           let e = Value.to_exp e in
                           [Eval.evaluate (Expr.mk_app f e)]
                         | _ -> failwith "bad"
                       end
                     in
                     [(FTAConstructor.Transition.Apply
                      ,evaluate
                      ,[(t,TermClassification.Elimination)
                       ;(t1,TermClassification.Introduction)]
                      ,(t2,TermClassification.Elimination))
                     ;(FTAConstructor.Transition.Apply
                      ,evaluate
                      ,[(t,TermClassification.Elimination)
                       ;(t1,TermClassification.Introduction)]
                      ,(t2,TermClassification.Introduction))]
                   | _ -> [])
               (C.get_all_types c)
           in
           let variant_construct_conversions =
             List.concat_map
               ~f:(fun t ->
                   match Type.node t with
                   | Type.Variant l ->
                     List.map
                       ~f:(fun (i,t') ->
                           (FTAConstructor.Transition.VariantConstruct i
                           ,(fun vs -> [Value.mk_ctor i (List.hd_exn vs)])
                           ,[(t',TermClassification.Introduction)]
                           ,(t,TermClassification.Introduction)))
                       l
                   | _ -> [])
               (C.get_all_types c)
           in
           let variant_unsafe_destruct_conversions =
             List.concat_map
               ~f:(fun t ->
                   match Type.node t with
                   | Type.Variant l ->
                     List.concat_map
                       ~f:(fun (i,t') ->
                           [(FTAConstructor.Transition.UnsafeVariantDestruct i,
                             (fun vs ->
                                match Value.destruct_ctor (List.hd_exn vs) with
                                | Some (i',v) ->
                                  if Id.equal i i' then [v] else []
                                | _ -> [])
                            ,[(t,TermClassification.Elimination)]
                            ,(t',TermClassification.Elimination))
                           ;(FTAConstructor.Transition.UnsafeVariantDestruct i,
                             (fun vs ->
                                match Value.destruct_ctor (List.hd_exn vs) with
                                | Some (i',v) ->
                                  if Id.equal i i' then [v] else []
                                | _ -> [])
                            ,[(t,TermClassification.Elimination)]
                            ,(t',TermClassification.Introduction))])
                       l
                   | _ -> [])
               (C.get_all_types c)
           in
           let tuple_constructors =
             List.filter_map
               ~f:(fun t ->
                   match Type.node t with
                   | Type.Tuple ts ->
                     let ts =
                       List.map
                         ~f:(fun t -> (t,TermClassification.Introduction))
                         ts
                     in
                     Some (FTAConstructor.Transition.TupleConstruct (List.length ts)
                          ,(fun vs -> [Value.mk_tuple vs])
                          ,ts
                          ,(t,TermClassification.Introduction))
                   | _ -> None)
               (C.get_all_types c)
           in
           let tuple_destructors =
             List.concat_map
               ~f:(fun t ->
                   begin match Type.node t with
                     | Type.Tuple ts ->
                       List.concat_mapi
                         ~f:(fun i tout ->
                             [(FTAConstructor.Transition.TupleDestruct (i)
                              ,(fun vs ->
                                 [begin match Value.node (List.hd_exn vs) with
                                    | Tuple vs ->
                                      List.nth_exn vs i
                                    | Wildcard ->
                                      Value.mk_wildcard
                                    | _ -> failwith "invalid"
                                  end])
                              ,[(t,TermClassification.Elimination)]
                              ,(tout,TermClassification.Elimination))
                             ;(FTAConstructor.Transition.TupleDestruct i
                              ,(fun vs ->
                                 [begin match Value.node (List.hd_exn vs) with
                                    | Tuple vs ->
                                      List.nth_exn vs i
                                    | Wildcard ->
                                      Value.mk_wildcard
                                    | _ -> failwith "invalid"
                                  end])
                              ,[(t,TermClassification.Elimination)]
                              ,(tout,TermClassification.Introduction))])
                         ts
                     | _ -> []
                   end)
               (C.get_all_types c)
           in
           let rec_call_conversions =
             let evaluation vs =
               begin match vs with
                 | [v1] ->
                   let break = fun v ->
                     let t =
                       Typecheck.typecheck_value
                         context.ec
                         context.tc
                         context.vc
                         v
                     in
                     C.is_recursive_type
                       c
                       t
                   in
                   if Predicate.implied_by_strict_functional_subvalue ~break v1 input then
                     begin
                       sub_calls v1
                     end
                   else
                     []
                 | _ -> failwith "invalid"
               end
             in
             [(FTAConstructor.Transition.Rec
              ,evaluation
              ,[(tin,TermClassification.Introduction)]
              ,(tout,TermClassification.Elimination))
             ;(FTAConstructor.Transition.Rec
              ,evaluation
              ,[(tin,TermClassification.Introduction)]
              ,(tout,TermClassification.Introduction))]
           in
           let conversions =
             variant_construct_conversions
             @ tuple_constructors
             @ eval_conversion
             @ tuple_destructors
             @ variant_unsafe_destruct_conversions
           in
           let all_conversions =
             context_conversions
             @ rec_call_conversions
             @ conversions
           in
           (*let destruct_conversions =
             tuple_destructors
             @ variant_unsafe_destruct_conversions
             in
             let construct_conversions =
             tuple_constructors
             @ variant_construct_conversions
             in*)
           (*let subvalues =
             subvalues_full_of_same_type
               ~context
               ~break:(fun v ->
                   let t =
                     Typecheck.typecheck_value
                       context.ec
                       context.tc
                       context.vc
                       v
                   in
                   C.is_recursive_type
                     c
                     t)
               input
             in
             let subcall_sites =
             List.filter_map
               ~f:(fun i' ->
                   if Value.strict_subvalue i' input then
                     Some ([(input,i')],tin)
                   else
                     None)
               subvalues
             in
             let c = C.add_states c subcall_sites in*)
           let no_news =
             List.fold
               ~f:(fun last_adds i ->
                   begin match last_adds with
                     | None -> None
                     | Some (old_added,old_pruned) ->
                       let (d1,e1) = C.update_from_conversions c variant_unsafe_destruct_conversions in
                       let (d2,e2) = C.update_from_conversions c tuple_destructors in
                       let (d3,e3) =
                         C.update_from_conversions c conversions
                       in
                       let (d4,e4) =
                         C.update_from_conversions c all_conversions
                       in
                       let new_added = (List.length d1) + (List.length d2) + (List.length d3) + (List.length d4) in
                       let new_pruned = (List.length e1) + (List.length e2) + (List.length e3) + (List.length d4) in
                       if new_pruned > 0 &&
                          (new_added = 0 ||
                           (Float.to_int (Float.of_int new_added *. 5.0) < old_added && new_pruned > (Float.to_int (Float.of_int old_pruned *. 5.0)))) then
                         None
                       else
                         Some (new_added, new_pruned)
                   end)
               ~init:(Some (0,0))
               (range 0 (GlobalState.get_num_applications gs))
           in
           if Option.is_none no_news then
             begin
               IncreaseMaxResponse
             end
           else
             begin
               (*C.update_from_conversions c (destruct_conversions) ~ensure_state:false;*)
               C.add_destructors c;
               let c = C.minimize c in
               Generated c
             end)
    in
    begin match ans_o with
      | IncreaseMaxResponse ->
        let gs = GlobalState.increase_max_multiplier gs input in
        Consts.log
          (fun () ->
             "MVM increased on " ^
             (Value.show input) ^
             " to " ^
             (Float.to_string (GlobalState.get_max_value_multiplier gs input)));
        construct_single_fta
          ~context
          ~tin
          ~tout
          ~gs
          sub_calls
          input
          valid_ios
      | Generated ans ->
        (ans,gs)
    end

  let construct_full
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
      ~(checker:Value.t -> Value.t -> bool)
      ~(gs:GlobalState.t)
      (all_ins:Value.t list)
      (required_vs:ValueSet.t)
    : (C.t list * ValToC.t * GlobalState.t) =
    let (inmap,gs) =
      List.fold
        ~f:(fun (inmap,gs) v ->
            let (res,gs) =
              construct_single_fta
                ~context
                ~tin
                ~tout
                ~gs
                (fun v ->
                   let vc = ValToC.as_kvp_list inmap in
                   let all_valids = List.filter ~f:(fun (v',_) -> Predicate.(=>) v' v) vc in
                   List.concat_map ~f:(fun (v,c) -> C.get_final_values c v) all_valids)
                v
                checker
            in
            (ValToC.insert
               inmap
               v
               res,gs))
        ~init:(ValToC.empty,gs)
        all_ins
    in
    let cs =
      List.map
        ~f:(ValToC.lookup_exn inmap)
        (ValueSet.as_list required_vs)
    in
    (cs,inmap,gs)

  let get_all_sorted_inputs_of_same_type
      (context:Context.t)
      (ds:C.TypeDS.t)
      (inputs:Value.t list)
    =
    let all_inputs =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map
           ~f:(subvalues_full_of_same_type
                 ~context
                 ~ds)
           inputs)
    in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
      then v1 comes before v2 in terms of generating their FTAs. This is
      necessrary for ensuring that recursion is appropriately added *)
    let sorted_inputs =
      safe_sort
        ~compare:(fun v1 v2 ->
            if strict_functional_subvalue ~context ~ds v1 v2 then
              Some (-1)
            else if strict_functional_subvalue ~context ~ds v2 v1 then
              Some 1
            else
              None)
        all_inputs
    in
    sorted_inputs

  let get_all_subvalues_of_same_type
      ~(problem:Problem.t)
      (args_t:Type.t)
      (v:Value.t)
    : Value.t list =
    let vtc = ValueTCIntegration.tc_val (problem.tc) v args_t in
    let sub_vs =
      List.dedup_and_sort
        ~compare:ValueTCIntegration.Derivation.compare
        (ValueTCIntegration.Derivation.sub_derivations vtc)
    in
    let vs_ts =
      List.map
        ~f:(fun d ->
            (ValueTCIntegration.Derivation.get_value d
            ,ValueTCIntegration.Derivation.get_type d))
        sub_vs
    in
    let relevant_ins =
      List.filter_map
        ~f:(fun (v,t) ->
            let is_relevant =
              Typecheck.type_equiv
                problem.tc
                t
                args_t
            in
            if is_relevant then
              Some v
            else
              None)
        vs_ts
    in
    relevant_ins

  module TermSet = SetOf(A.Term)
  let procd = ref TermSet.empty
  let subprocd = ref TermSet.empty

  let rec add_all_subterms
      (Term (_,ts) as fullt:A.Term.t)
    : unit =
    if TermSet.member !subprocd fullt then
      begin
        ()
      end
    else
      begin
        subprocd := TermSet.insert fullt !subprocd;
        List.iter
          ~f:add_all_subterms
          ts
      end

    let full_satisfies
        ~(context:Context.t)
        ~(rep:A.TermState.t)
        ~(input:Type.t)
        ~(output:Type.t)
        ~(pred:Value.t -> Value.t -> bool)
        ~(inputs:Value.t list)
        ~(ds:C.TypeDS.t)
      : bool =
      let term = A.TermState.to_term rep in
      let fune = C.term_to_safe_eval input output term (fun v1 v2 -> strict_functional_subvalue ~context ~ds v2 v1) in
      List.for_all
        ~f:(fun vin ->
            let v = SafeEval.from_value vin in
            let e = SafeEval.value_to_exp v in
            let fulle = SafeEval.App (fune,e) in
            let vo = SafeEval.evaluate_with_holes ~eval_context:context.evals fulle in
            begin match vo with
              | None -> false
              | Some v ->
                let vout = SafeEval.to_value v in
                pred vin vout
            end)
        inputs

  type synth_res =
    | IncreaseSize
    | FoundResult of A.Term.t

  type t =
    {
      context : Context.t ;
      tin : Type.t ;
      tout : Type.t ;
      gs : GlobalState.t ;
      last_processed : Value.t list ;
    }

  let context
      (a:t)
    : Context.t =
    a.context

  let tin
      (a:t)
    : Type.t =
    a.tin

  let tout
      (a:t)
    : Type.t =
    a.tout

  let upgrade_from_failed_isect
      (a:t)
    : t =
    { a with
      gs = GlobalState.upgrade_from_failed_isect a.gs ;
    }

  let synthesize
      ~(inputs:Value.t list)
      ~(ds:C.TypeDS.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(a:t)
    : (synth_res * t) =
    let orig_inputs = inputs in
    let context = a.context in
    if (List.length orig_inputs = 0) then
      (*Expr.of_type
         (Type.mk_arrow
            (Typecheck.concretify context.tc tin)
            (Typecheck.concretify context.tc tout))*)
      (FoundResult (C.term_of_type_exn ds a.tout),a)
    else
      let all_inputs =
        List.dedup_and_sort
          ~compare:Value.compare
          (List.concat_map
             ~f:(subvalues_full_of_same_type
                   ~context
                   ~ds)
             orig_inputs)
      in
      let sorted_inputs =
        safe_sort
          ~compare:(fun v1 v2 ->
              if strict_functional_subvalue
                  ~context ~ds v1 v2 then
                Some (-1)
              else if strict_functional_subvalue ~context ~ds v2 v1 then
                Some 1
              else
                None)
          all_inputs
      in
      let (cs,_,gs) =
        construct_full
        ~context
        ~tin:a.tin
        ~tout:a.tout
        ~checker:pred
        ~gs:a.gs
        sorted_inputs
        (ValueSet.from_list inputs)
      in
      let c =
        fold_on_head_exn
          ~f:(fun c1 c2 -> C.minimize (C.intersect c1 c2))
          cs
      in
      let rec find_in_c c =
        C.invalidate_computations c;
        let rep_o = C.min_term_state_silly c (fun t -> TermSet.member !subprocd t) (fun t -> TermSet.member !procd t) in
        begin match rep_o with
          | Some rep ->
            let term = (A.TermState.to_term rep) in
            if full_satisfies ~context ~rep ~input:a.tin ~output:a.tout ~pred ~inputs ~ds then
              (FoundResult term,{ a with gs})
            else
              begin
                Consts.log (fun () -> "failed correctness");
                Consts.log (fun () -> "candidate value was: " ^ Expr.show (C.term_to_exp_internals term));
                procd := TermSet.insert term !procd;
                add_all_subterms term;
                find_in_c c
              end
          | None -> (IncreaseSize,{ a with gs })
        end
      in
      find_in_c c
      (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
        then v1 comes before v2 in terms of generating their FTAs. This is
        necessrary for ensuring that recursion is appropriately added *)

  let rec synthesize_caller
      (a:t)
      ~(ds:C.TypeDS.t)
      ~(pred:Value.t -> Value.t -> bool)
      ~(inputs:Value.t list)
    : t * Expr.t =
    Consts.log (fun _ -> "Synthesis started with size " ^ (string_of_int (GlobalState.get_num_applications a.gs)));
    let (synth_res,a) =
      synthesize
        ~pred
        ~inputs
        ~ds
        ~a
    in
    begin match synth_res with
      | IncreaseSize ->
        let a = upgrade_from_failed_isect a in
        synthesize_caller
          a
          ~ds
          ~pred
          ~inputs
      | FoundResult t ->
        (*let t = C.ensure_switches ds context t tout in*)
        (a,C.term_to_exp a.tin a.tout t)
    end

  let init
      ~(problem:Problem.t)
      ~(context:Context.t)
      ~(tin:Type.t)
      ~(tout:Type.t)
    : t =
    {
      context ;
      tin ;
      tout ;
      gs = GlobalState.empty ;
      last_processed = [] ;
    }

  let synth
      (a:t)
      (inputs:Value.t list)
      (pred:Value.t -> Value.t -> bool)
    : t * Expr.t =
    let context = (context a) in
    let tin = tin a in
    let tout = tout a in
    let all_values =
      List.dedup_and_sort
        ~compare:Value.compare
        (List.concat_map ~f:Value.subvalues inputs) (*TODO*)
    in
    let ts =
      ([tin;tout]
       @(List.map ~f:Type.mk_named (Context.keys context.tc))
       @(Context.data context.ec)
       @(List.map ~f:(Typecheck.typecheck_value context.ec context.tc context.vc) all_values))
    in
    let ds =
      C.create_ds_from_t_list_context
        ~context
        ts
    in
    (*This guarantees that, if v1 < v2, in terms of subvalue partial ordering,
      then v1 comes before v2 in terms of generating their FTAs. This is
      necessrary for ensuring that recursion is appropriately added *)
    Consts.log (fun () -> "inputs: " ^ (string_of_list Value.show inputs));
    synthesize_caller
      a
      ~inputs
      ~pred
      ~ds
end
