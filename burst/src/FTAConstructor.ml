open MyStdLib
open Lang

module State =
struct
  type t =
    | Vals of (Value.t * Predicate.t) list * ClassifiedType.t
    | Top
  [@@deriving eq, hash, ord, show]

  let imply
      (s1:t)
      (s2:t)
    : bool =
    begin match (s1,s2) with
      | (_,Top) -> true
      | (Top,_) -> false
      | (Vals (vps1,(t1,_)),Vals (vps2,(t2,_))) ->
        if Type.equal t1 t2 then
          List.for_all
            ~f:(fun (v2,p2) ->
                let p1 = List.Assoc.find_exn ~equal:Value.equal vps1 v2 in
                Value.equal p1 p2)
            vps2
        else
          false
    end

  let destruct_vals
      (x:t)
    : ((Value.t * Predicate.t) list * ClassifiedType.t) option =
    begin match x with
      | Vals (vs,t) -> Some (vs,t)
      | _ -> None
    end

  let destruct_vals_exn
      (x:t)
    : ((Value.t * Predicate.t) list * ClassifiedType.t) =
    Option.value_exn (destruct_vals x)

  let normalize
      (x:t)
    : t =
    begin match x with
      | Top -> Top
      | Vals (vps,(t,tc)) -> Vals (vps,(t,TermClassification.Introduction))
    end

  let top = Top

  let vals vvs t = Vals (vvs,t)

  let print a b = pp b a

  let product a b =
    begin match (a,b) with
      | (Vals (avs,at), Vals (bvs,bt)) ->
        if ClassifiedType.equal at bt then
          Some (Vals ((avs@bvs),at))
        else
          None
      | (Top, _) -> Some b
      | (_, Top) -> Some a
    end
end

module Transition =
struct
  type id =
    | FunctionApp of Expr.t
    | Apply
    | VariantConstruct of Id.t
    | UnsafeVariantDestruct of Id.t
    | TupleConstruct of int
    | TupleDestruct of int
    | Var
    | LetIn
    | Rec
    | VariantSwitch of Id.t list
  [@@deriving eq, hash, ord, show]
  type t_node = (id * Type.t * int)
  [@@deriving eq, hash, ord, show]
  type t = t_node hash_consed
  [@@deriving eq, hash, ord, show]

  let to_expr
      (t:t)
      (es:AngelicEval.expr list)
    : AngelicEval.expr =
    begin match fst3 t.node with
      | FunctionApp e -> AngelicEval.from_exp e
      | Apply ->
        begin match es with
          | [e1;e2] -> AngelicEval.App (e1,e2)
          | _ -> failwith "bad1"
        end
      | VariantConstruct i ->
        begin match es with
          | [e] -> AngelicEval.Ctor (i,e)
          | _ -> failwith ("bad2:" ^ (string_of_list AngelicEval.show_expr es))
        end
      | UnsafeVariantDestruct i ->
        begin match es with
          | [e] -> AngelicEval.Unctor (i,e)
          | _ -> failwith "bad3"
        end
      | TupleConstruct _ ->
        AngelicEval.Tuple es
      | TupleDestruct i ->
        begin match es with
          | [e] -> AngelicEval.Proj (i,e)
          | _ -> failwith "bad4"
        end
      | Var -> AngelicEval.Var (Id.create "x")
      | LetIn -> failwith "bad5"
      | Rec ->
        begin match es with
          | [e] ->
            AngelicEval.AngelicF e
          | _ ->
            failwith "bad6"
        end
      | VariantSwitch ids ->
        begin match es with
          | e::es ->
            let branches =
              List.map2_exn
                ~f:(fun i e -> (Pattern.Ctor (i,Pattern.Wildcard),e))
                ids
                es
            in
            AngelicEval.Match (e,branches)
          | _ -> failwith "bad7"
        end
    end

  let table = HashConsTable.create 1000

  let create
      (node:t_node)
    : t =
    HashConsTable.hashcons
      hash_t_node
      compare_t_node
      table
      node

  let node
      (v:t)
    : t_node =
    v.node

  let cost
      (x:t)
    : int =
    begin match fst3 (node x) with
      | FunctionApp _ -> 1
      | Apply -> 0
      | VariantConstruct _ -> 2
      | UnsafeVariantDestruct _ -> 1
      | TupleConstruct _ -> 1
      | TupleDestruct _ -> 1
      | Var -> 0
      | LetIn -> 0
      | Rec -> 1
      | VariantSwitch _ -> 2
    end

  let id
      (v:t)
    : id =
    fst3 (node v)

  let get_type
      (v:t)
    : Type.t =
    snd3 (node v)

  let print_id id =
    match id with
    | FunctionApp x -> Expr.show x
    | VariantConstruct x -> "Variant(" ^ MyStdLib.Id.to_string x ^ ")"
    | TupleConstruct i -> "Tuple(" ^ (string_of_int i) ^ ")"
    | Var -> "Var"
    | LetIn -> "LetIn"
    | Rec -> "Rec"
    | UnsafeVariantDestruct t -> "VariantUnsafe(" ^ (Id.show t) ^ ")"
    | TupleDestruct i ->
      "TupleProj("
      ^ (string_of_int i)
      ^ ")"
    | VariantSwitch (bs) ->
      "SwitchOn(" ^ (String.concat ~sep:"," (List.map ~f:Id.to_string bs)) ^ ")"
    | Apply ->
      "Apply"
  

  (*let rec_ = create (Rec,1)*)

  let arity = trd3 % node
end

module Make(A : Automata.Automaton with module Symbol := Transition and module State := State) = struct
  module TypeDS = struct
    include
      DisjointSetWithSetDataOf
        (struct
          include Type
          let preferred t1 t2 =
            begin match (Type.node t1,Type.node t2) with
              | (Variant _,Variant _)
              | (Arrow _,Arrow _)
              | (Tuple _,Tuple _) ->
                Type.size t1 < Type.size t2
              | _ ->
                begin match Type.node t1 with
                  | Variant _
                  | Arrow _
                  | Tuple _ -> true
                  | _ -> false
                end
            end
        end)
        (BoolModule)
        (struct
          type t = Type.t -> bool
          let v = (Option.is_some % Type.destruct_mu)
        end)
        (struct
          type t = bool -> bool -> bool
          let v = (||)
        end)

    let is_recursive_type
        (x:t)
        (t:Type.t)
      : bool =
      snd
        (find_representative
           x
           t)
  end

  module StateSet = SetOf(State)
  module TypeToStates = DictOf(ClassifiedType)(StateSet)
  module TransitionSet = SetOf(Transition)

  type t =
    {
      a                  : A.t                        ;
      mutable d          : TypeToStates.t    ;
      mutable ds         : TypeDS.t                   ;
      inputs             : Value.t list               ;
      mutable tset       : TransitionSet.t            ;
      final_candidates   : Value.t -> Value.t -> bool ;
      all_types          : Type.t list                ;
      mutable up_to_date : bool                       ;
      input_type         : Type.t                     ;
      output_type        : Type.t                     ;
      value_filter       : Value.t -> bool            ;
      mutable all_states : StateSet.t                 ;
      mutable min_term_state : A.TermState.t option option ;
      mutable dupe_ref   : t option                   ;
    }
  [@@deriving show]

  let update_ds
      (ds:TypeDS.t)
      (c:t)
    : unit =
    c.ds <- ds

  let copy (c:t)
    : t =
    begin match c.dupe_ref with
      | Some d -> d
      | None ->
        let duped =
          Consts.time
            Consts.copy_times
            (fun () ->
               { c with
                 a = A.copy c.a ;
               })
        in
        c.dupe_ref <- Some duped;
        duped
    end

  let clear_copy (c:t)
    : unit =
    c.dupe_ref <- None

  let equal _ _ = failwith "not implemented"
  let hash_fold_t _ _ = failwith "not implemented"
  let hash _ = failwith "not implemented"
  let compare _ _ = failwith "not implemented"

  let fid = Id.create "f"
  let xid = Id.create "x"

  let rec term_to_exp_internals
      (Term (t,ts):A.term)
    : Expr.t =
    begin match Transition.id t with
      | Apply ->
        begin match ts with
          | [t1;t2] ->
            let e1 = term_to_exp_internals t1 in
            let e2 = term_to_exp_internals t2 in
            Expr.mk_app e1 e2
          | _ -> failwith "not permitted"
        end
      | FunctionApp e ->
        List.fold
          ~f:(fun acc bt ->
              Expr.mk_app
                acc
                (term_to_exp_internals bt))
          ~init:e
          ts
      | VariantConstruct c ->
        begin match ts with
          | [t] ->
            Expr.mk_ctor c (term_to_exp_internals t)
          | _ -> failwith "incorrect setup"
        end
      | UnsafeVariantDestruct c ->
        begin match ts with
          | [t] ->
            Expr.mk_unctor
              c
              (term_to_exp_internals t)
          | _ -> failwith "incorrect setup"
        end
      | TupleConstruct _ ->
        Expr.mk_tuple
          (List.map
             ~f:term_to_exp_internals
             ts)
      | Var ->
        Expr.mk_var xid
      | Rec ->
        begin match ts with
          | [t] ->
            Expr.mk_app (Expr.mk_var fid) (term_to_exp_internals t)
          | _ -> failwith "incorrect"
        end
      | VariantSwitch is ->
        begin match ts with
          | t::ts ->
            (* TODO, make destructors *)
            let e = term_to_exp_internals t in
            let its = List.zip_exn is ts in
            let branches = List.map ~f:(fun (i,t) -> (Pattern.Ctor (i,Pattern.Wildcard),term_to_exp_internals t)) its in
            Expr.mk_match e branches
          | [] -> failwith "cannot happen"
        end
      | TupleDestruct i ->
        Expr.mk_proj i (term_to_exp_internals (List.hd_exn ts))
      | _ -> failwith "not permitted"
    end

  let term_to_exp
      (tin:Type.t)
      (tout:Type.t)
      (t:A.Term.t)
    : Expr.t =
    let internal = term_to_exp_internals t in
    Expr.mk_fix
      fid
      (Type.mk_arrow tin tout)
      (Expr.mk_func (xid,tin) internal)

  let rec term_to_safe_eval_internals
      (Term (t,ts):A.term)
    : SafeEval.expr =
    begin match Transition.id t with
      | Apply ->
        begin match ts with
          | [t1;t2] ->
            let e1 = term_to_safe_eval_internals t1 in
            let e2 = term_to_safe_eval_internals t2 in
            SafeEval.App (e1,e2)
          | _ -> failwith "not permitted"
        end
      | FunctionApp e ->
        List.fold
          ~f:(fun acc bt ->
              SafeEval.App
                (acc,term_to_safe_eval_internals bt))
          ~init:(SafeEval.from_exp e)
          ts
      | VariantConstruct c ->
        begin match ts with
          | [t] ->
            SafeEval.Ctor (c,(term_to_safe_eval_internals t))
          | _ -> failwith "incorrect setup"
        end
      | UnsafeVariantDestruct c ->
        begin match ts with
          | [t] ->
            SafeEval.Unctor
              (c,term_to_safe_eval_internals t)
          | _ -> failwith "incorrect setup"
        end
      | TupleConstruct _ ->
        SafeEval.Tuple
          (List.map
             ~f:term_to_safe_eval_internals
             ts)
      | Var ->
        SafeEval.Var xid
      | Rec ->
        begin match ts with
          | [t] ->
            SafeEval.App (SafeEval.Var fid,SafeEval.Check (term_to_safe_eval_internals t))
          | _ -> failwith "incorrect"
        end
      | VariantSwitch is ->
        begin match ts with
          | t::ts ->
            (* TODO, make destructors *)
            let e = term_to_safe_eval_internals t in
            let its = List.zip_exn is ts in
            let branches = List.map ~f:(fun (i,t) -> (Pattern.Ctor (i,Pattern.Wildcard),term_to_safe_eval_internals t)) its in
            SafeEval.Match (e,branches)
          | [] -> failwith "cannot happen"
        end
      | TupleDestruct i ->
        SafeEval.Proj (i,(term_to_safe_eval_internals (List.hd_exn ts)))
      | _ -> failwith "not permitted"
    end

  let term_to_safe_eval
      (tin:Type.t)
      (tout:Type.t)
      (t:A.term)
      (checker:Value.t -> Value.t -> bool)
    : SafeEval.expr =
    let internal = term_to_safe_eval_internals t in
    let internal = SafeEval.UpdateChecks ((fun v1 v2 ->
        let v1 = (SafeEval.to_value v1) in
        let v2 = (SafeEval.to_value v2) in
        checker v1 v2), SafeEval.Var xid, internal) in
    SafeEval.Fix
      (fid
      ,Type.mk_arrow tin tout
      ,SafeEval.Func ((xid,tin),internal))

  let term_to_angelic_exp
      (tin:Type.t)
      (t:A.term)
    : AngelicEval.expr =
    let rec term_to_angelic_exp
        (Term (t,ts):A.term)
      : AngelicEval.expr =
      AngelicEval.(begin match Transition.id t with
          | Apply ->
            begin match ts with
              | [t1;t2] ->
                let e1 = term_to_angelic_exp t1 in
                let e2 = term_to_angelic_exp t2 in
                App (e1,e2)
              | _ -> failwith "not permitted"
            end
          | FunctionApp e ->
            List.fold
              ~f:(fun acc bt ->
                  App
                    (acc
                    ,(term_to_angelic_exp bt)))
              ~init:(AngelicEval.from_exp e)
              ts
          | VariantConstruct c ->
            begin match ts with
              | [t] ->
                Ctor (c,term_to_angelic_exp t)
              | _ -> failwith "incorrect setup"
            end
          | UnsafeVariantDestruct c ->
            begin match ts with
              | [t] ->
                Unctor
                  (c
                  ,term_to_angelic_exp t)
              | _ -> failwith "incorrect setup"
            end
          | TupleConstruct _ ->
            Tuple
              (List.map
                 ~f:term_to_angelic_exp
                 ts)
          | Var ->
            Var xid
          | Rec ->
            begin match ts with
              | [t] ->
                AngelicF (term_to_angelic_exp t)
              | _ -> failwith "incorrect"
            end
          | VariantSwitch is ->
            begin match ts with
              | t::ts ->
                (* TODO, make destructors *)
                let e = term_to_angelic_exp t in
                let its = List.zip_exn is ts in
                let branches = List.map ~f:(fun (i,t) -> (Pattern.Ctor (i,Pattern.Wildcard),term_to_angelic_exp t)) its in
                Match (e,branches)
              | [] -> failwith "cannot happen"
            end
          | TupleDestruct i ->
            Proj (i,(term_to_angelic_exp (List.hd_exn ts)))
          | _ -> failwith "not permitted"
        end)
    in
    Func
      ((xid,tin)
      ,term_to_angelic_exp t)

  let rec term_of_type ds t =
    let (desired_t,_) = TypeDS.find_representative ds t in
    begin match Type.node desired_t with
      | Named i -> failwith "ah"
      | Arrow (t1,t2) -> failwith "ah"
      | Tuple ts ->
        let eso = List.map ~f:(term_of_type ds) ts in
        begin match distribute_option eso with
          | None -> None
          | Some es ->
            Some
              (A.Term
                 (Transition.create
                    (Transition.TupleConstruct (List.length es)
                    ,desired_t
                    ,List.length es)
                 ,es))
        end
      | Mu (_,t) ->
        term_of_type ds t
      | Variant branches ->
        List.fold
          ~f:(fun acco (i,t) ->
              begin match acco with
                | None ->
                  let eo = term_of_type ds t in
                  Option.map
                    ~f:(fun e ->
                        A.Term
                          (Transition.create
                             (Transition.VariantConstruct i
                             ,desired_t
                             ,1)
                          ,[e]))
                    eo
                | Some e -> Some e
              end)
          ~init:None
          branches
    end

  let term_of_type_exn
      (ds:TypeDS.t)
      (x:Type.t)
    : A.Term.t =
    Option.value_exn (term_of_type ds x)

  let rec extract_unbranched_states_internal
      (TS (t,state,ts):A.term_state)
    : A.term_state list =
    begin match Transition.id t with
       | Apply ->
         begin match ts with
           | [t1;t2] ->
             let l1 = extract_unbranched_states_internal t1 in
             let l2 = extract_unbranched_states_internal t2 in
             l1@l2
           | _ -> failwith "not permitted"
         end
       | FunctionApp _ ->
         List.concat_map ~f:extract_unbranched_states_internal ts
       | VariantConstruct c ->
         begin match ts with
           | [t] ->
             extract_unbranched_states_internal t
           | _ -> failwith "incorrect setup"
         end
       | UnsafeVariantDestruct i ->
         begin match ts with
           | [t] ->
             let l = extract_unbranched_states_internal t in
             t::l
           | _ -> failwith "incorrect setup"
         end
       | TupleConstruct _ ->
         List.concat_map ~f:extract_unbranched_states_internal ts
       | Var ->
         []
       | Rec ->
         begin match ts with
           | [t] ->
             extract_unbranched_states_internal t
           | _ -> failwith "incorrect"
         end
       | VariantSwitch is ->
         begin match ts with
           | t::ts ->
             let matched_term = A.TermState.to_term t in
             let l = extract_unbranched_states_internal t in
             l@
             (List.concat_map
                ~f:(fun t ->
                    let l = extract_unbranched_states_internal t in
                    List.filter ~f:(fun t -> not (A.Term.equal matched_term (A.TermState.to_term t))) l)
                ts)
           | [] -> failwith "cannot happen"
         end
       | TupleDestruct _ ->
         begin match ts with
           | [t] ->
             extract_unbranched_states_internal t
           | _ -> failwith "not permitted"
         end
       | LetIn -> failwith "not permitted"
    end

  let rec extract_unbranched_states
      ((*TS (t,state,ts)*)ts:A.term_state)
    : State.t list =
    List.map ~f:A.(State.normalize % TermState.get_state) (extract_unbranched_states_internal ts)
    (*begin match Transition.id t with
       | Apply ->
         begin match ts with
           | [t1;t2] ->
             let l1 = extract_unbranched_states t1 in
             let l2 = extract_unbranched_states t2 in
             l1@l2
           | _ -> failwith "not permitted"
         end
       | FunctionApp _ ->
         List.concat_map ~f:extract_unbranched_states ts
       | VariantConstruct c ->
         begin match ts with
           | [t] ->
             extract_unbranched_states t
           | _ -> failwith "incorrect setup"
         end
       | UnsafeVariantDestruct i ->
         begin match ts with
           | [t] ->
             let l = extract_unbranched_states t in
             (State.normalize (A.TermState.get_state t))::l
           | _ -> failwith "incorrect setup"
         end
       | TupleConstruct _ ->
         List.concat_map ~f:extract_unbranched_states ts
       | Var ->
         []
       | Rec ->
         begin match ts with
           | [t] ->
             extract_unbranched_states t
           | _ -> failwith "incorrect"
         end
       | VariantSwitch is ->
         begin match ts with
           | t::ts ->
             let matched_state = State.normalize (A.TermState.get_state t) in
             let l = extract_unbranched_states t in
             l@
             (List.concat_map
                ~f:(fun t ->
                    let l = extract_unbranched_states t in
                    List.filter ~f:(fun t -> not (State.imply matched_state t)) l)
                ts)
           | [] -> failwith "cannot happen"
         end
       | TupleDestruct _ ->
         begin match ts with
           | [t] ->
             extract_unbranched_states t
           | _ -> failwith "not permitted"
         end
       | LetIn -> failwith "not permitted"
      end*)

  let rec extract_unbranched_switches
      (Term (t,ts):A.term)
    : (A.term * Id.t) list =
    begin match Transition.id t with
       | Apply ->
         begin match ts with
           | [t1;t2] ->
             let l1 = extract_unbranched_switches t1 in
             let l2 = extract_unbranched_switches t2 in
             l1@l2
           | _ -> failwith "not permitted"
         end
       | FunctionApp _ ->
         List.concat_map ~f:extract_unbranched_switches ts
       | VariantConstruct c ->
         begin match ts with
           | [t] ->
             extract_unbranched_switches t
           | _ -> failwith "incorrect setup"
         end
       | UnsafeVariantDestruct i ->
         begin match ts with
           | [t] ->
             let l = extract_unbranched_switches t in
             (t,i)::l
           | _ -> failwith "incorrect setup"
         end
       | TupleConstruct _ ->
         List.concat_map ~f:extract_unbranched_switches ts
       | Var ->
         []
       | Rec ->
         begin match ts with
           | [t] ->
             extract_unbranched_switches t
           | _ -> failwith "incorrect"
         end
       | VariantSwitch is ->
         begin match ts with
           | t::ts ->
             let matched_t = t in
             let l = extract_unbranched_switches t in
             l@
             (List.concat_map
                ~f:(fun t ->
                    let l = extract_unbranched_switches t in
                    List.filter ~f:(fun (t,_) -> not (A.Term.equal t matched_t)) l)
                ts)
           | [] -> failwith "cannot happen"
         end
       | TupleDestruct _ ->
         begin match ts with
           | [t] ->
             extract_unbranched_switches t
           | _ -> failwith "not permitted"
         end
       | LetIn -> failwith "not permitted"
    end

  let is_nonfiltered_state
      (c:t)
      (s:State.t)
    : bool =
    begin match s with
      | Top -> true
      | Vals (vps,_) ->
        List.for_all ~f:(c.value_filter % snd) vps
    end

  let rec ensure_switches
      (ds:TypeDS.t)
      (context:Context.t)
      (e:A.Term.t)
      (desired_type:Type.t)
    : A.Term.t =
    let unbranched = extract_unbranched_switches e in
    let all_ts_by_exp =
      group_by
        ~key:(fst)
        ~equal:A.Term.equal
        unbranched
    in
    if List.is_empty all_ts_by_exp then
      e
    else
      let e =
        List.fold
          ~f:(fun t tbis ->
              let t_orig = t in
              begin match tbis with
                | (tb,i)::_ ->
                  let i_orig = i in
                  let vc = context.vc in
                  let its = Context.find_exn vc i in
                  let (t,_) = TypeDS.find_representative ds (Type.mk_variant its) in
                  let its = Type.destruct_variant_exn t in
                  let ts =
                    List.map
                      ~f:(fun (i,_) ->
                          if Id.equal i i_orig then
                            t_orig
                          else
                            term_of_type_exn ds desired_type)
                      its
                  in
                  let is = List.map ~f:fst its in
                  A.Term
                    (Transition.create
                       (Transition.VariantSwitch is
                       ,t
                       ,1+(List.length is))
                    ,tb::ts)
                | _ -> failwith "bad"
              end)
          ~init:e
          all_ts_by_exp
      in
      ensure_switches
        ds
        context
        e
        desired_type

  module EasyTerm = struct
    type t_node =
      | App of string * t list
      | VC of string * t
      | UVD of string * t
      | TC of t list
      | TD of int * t
      | Var
      | Rec of t
      | VSwitch of string list * t list
    and t = (Type.t * t_node)

    let rec to_term
        ((ty,e):t)
      : A.Term.t =
      let mk_term
          (id:Transition.id)
          (children:A.Term.t list)
        : A.Term.t =
        let s = List.length children in
        A.Term (Transition.create (id,ty,s),children)
      in
      begin match e with
        | Var ->
          mk_term Transition.Var []
        | App (i,ets) ->
          let ts = List.map ~f:to_term ets in
          mk_term (Transition.FunctionApp (Expr.mk_var (Id.create i))) ts
        | VC (i,et) ->
          mk_term (Transition.VariantConstruct (Id.create i)) [to_term et]
        | UVD (i,et) ->
          mk_term (Transition.UnsafeVariantDestruct (Id.create i)) [to_term et]
        | TC (ets) ->
          let ts = List.map ~f:to_term ets in
          mk_term (Transition.TupleConstruct (List.length ets)) ts
        | TD (i2,et) ->
          mk_term (Transition.TupleDestruct (i2)) [to_term et]
        | Rec et ->
          mk_term (Transition.Rec) [to_term et]
        | VSwitch (ids,ets) ->
          let ts = List.map ~f:to_term ets in
          mk_term (Transition.VariantSwitch (List.map ~f:Id.create ids)) ts
      end
    end

  let get_type_rep
      (c:t)
      (t:Type.t)
    : Type.t =
    fst
      (TypeDS.find_representative
         c.ds
         t)

  let is_recursive_type
      (c:t)
      (t:Type.t)
    : bool =
    snd
      (TypeDS.find_representative
         c.ds
         t)

  let invalidate_computations
      (c:t)
    : unit =
    c.min_term_state <- None

  let get_final_values
      (c:t)
      (vin:Value.t)
    : Predicate.t list =
    let final_states = A.final_states c.a in
    (*print_endline "hey fs";
    List.iter
      ~f:(fun fs ->
          print_endline (State.show fs))
      final_states;*)
    List.dedup_and_sort
      ~compare:Value.compare
      (List.concat_map
         ~f:(fun s ->
             begin match s with
               | Vals ((vinsvouts),_) ->
                 List.filter_map
                   ~f:(fun (vin',vout) ->
                       if Value.equal vin vin' then
                         Some vout
                       else
                         None)
                   vinsvouts
               | _ -> failwith "invalid final values"
             end)
         final_states)

  let get_states
      (c:t)
      ((t,cl):ClassifiedType.t)
    : State.t list =
    begin match TypeToStates.lookup c.d (get_type_rep c t,cl) with
      | None -> []
      | Some ss -> StateSet.as_list ss
    end

  let top_state : State.t = State.top

  let val_state
      (c:t)
      (vinsvouts:(Value.t * Predicate.t) list)
      ((t,cl):ClassifiedType.t)
    : State.t =
    let t = get_type_rep c t in
    State.vals vinsvouts (t,cl)

  let add_state
      (c:t)
      (vinsvouts:(Value.t * Predicate.t) list)
      ((t,cl):ClassifiedType.t)
    : bool =
    let t = get_type_rep c t in
    let s = val_state c vinsvouts (t,cl) in
    let to_add =
      begin match TypeToStates.lookup c.d (t,cl) with
        | None ->
          StateSet.singleton s
        | Some ss ->
          StateSet.insert s ss
      end
    in
    let (all_states,news) = StateSet.insert_and_new s c.all_states in
    let d =
      TypeToStates.insert
        c.d
        (t,cl)
        to_add
    in
    begin
      if Type.equal t c.output_type
         && TermClassification.equal cl TermClassification.Introduction
         && List.for_all ~f:(uncurry c.final_candidates) vinsvouts then
        A.add_final_state c.a s
      else
        ()
    end;
    c.d <- d;
    c.all_states <- all_states;
    invalidate_computations c;
    news

  let update_tset
      (c:t)
      (trans:Transition.t)
    : unit =
    if TransitionSet.member c.tset trans then
      ()
    else
      begin
        A.add_transition
          c.a
          trans
          (List.init ~f:(func_of State.top) (Transition.arity trans))
          State.top;
        c.tset <- TransitionSet.insert trans c.tset;
        invalidate_computations c
      end

  type transition_repsonse =
    | AlreadyAdded
    | Filtered
    | NewlyAdded

  let add_transition
      (c:t)
      (trans_id:Transition.id)
      (sins:State.t list)
      (sout:State.t)
      (tout:Type.t)
      (ensure_state:bool)
    : transition_repsonse =
    let tout = get_type_rep c tout in
    update_tset
      c
      (Transition.create (trans_id,tout,List.length sins));
    let is_nonfiltered = is_nonfiltered_state c sout in
    if ensure_state && is_nonfiltered then
      begin
        let added =
          begin match sout with
            | Top -> false
            | Vals (vinsvouts,t) ->
              add_state c vinsvouts t
          end
        in
        A.add_transition
          c.a
          (Transition.create (trans_id,tout,List.length sins))
          sins
          sout;
        invalidate_computations c;
        if added then
          NewlyAdded
        else
          AlreadyAdded
      end
    else if StateSet.member c.all_states sout then
      begin
        A.add_transition
          c.a
          (Transition.create (trans_id,tout,List.length sins))
          sins
          sout;
        invalidate_computations c;
        AlreadyAdded
      end
    else
      Filtered

  let remove_transition
      (c:t)
      (trans:Transition.t)
      (sins:State.t list)
      (sout:State.t)
    : unit =
    A.remove_transition c.a trans sins sout;
    invalidate_computations c

  let remove_final_state
      (c:t)
      (s:State.t)
    : unit =
    A.remove_final_state c.a s;
    invalidate_computations c

  let evaluate
      (c:t)
      (input:Predicate.t list)
      (f:Value.t list -> Value.t list)
      (args:State.t list)
      ((t,cl):ClassifiedType.t)
    : State.t list =
    let vs = List.map ~f:State.destruct_vals_exn args in
    let vs = List.map ~f:(List.map ~f:snd % fst) vs in
    let args =
      begin match vs with
        | [] -> List.init ~f:(func_of []) (List.length input)
        | _ -> List.transpose_exn vs
      end
    in
    let outos = List.map ~f args in
    let outsl = List.transpose_exn outos in
    List.map
      ~f:(fun outs ->
          let in_outs = List.zip_exn input outs in
          val_state c in_outs (t,cl))
      outsl
    (*let args =
      List.map
        ~f:(List.map
              ~f:Value.to_exp)
        args
      in
    let full_exps =
      List.map
        ~f:(List.fold
              ~f:Expr.mk_app
              ~init:e)
        args
    in
      let outs = List.map ~f:Eval.evaluate full_exps in*)

  let update_from_conversions
      ?(ensure_state:bool = true)
      (c:t)
      (conversions:
         ((Transition.id
           * (Value.t list -> Value.t list)
           * (ClassifiedType.t list) * ClassifiedType.t) list))
    : (State.t list * State.t list) =
    let ids_ins_outs =
      List.concat_map
        ~f:(fun (i,e,tins,tout) ->
            if Type.equal (fst tout) Type._unit
            && List.length tins > 0 then
              []
            else
              let args_choices =
                      List.map
                        ~f:(fun t -> get_states c t)
                        tins
                    in
                    let args_list =
                      combinations
                        args_choices
                    in
                    List.concat_map
                      ~f:(fun ins ->
                          let outs = evaluate c c.inputs e ins tout in
                          List.map
                            ~f:(fun out -> (i,ins,out,fst tout))
                            outs)
                      args_list)
        conversions
    in
    (split_by_either
       (List.filter_map
          ~f:(fun (i,ins,out,tout) ->
              let news =
                add_transition
                  c
                  i
                  ins
                  out
                  tout
                  ensure_state
              in
              begin match news with
                | AlreadyAdded -> None
                | NewlyAdded -> Some (Left out)
                | Filtered -> Some (Right out)
              end)
          ids_ins_outs))

  let create_ds_from_t_list_context
      ~(context:Context.t)
      (ts:Type.t list)
    : TypeDS.t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes context.tc)
           ts)

    in
    TypeDS.create_from_list
      ~equiv:(Typecheck.type_equiv context.tc)
      all_types

  let create_ds_from_t_list
      ~(problem:Problem.t)
      (ts:Type.t list)
    : TypeDS.t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes problem.tc)
           ts)

    in
    TypeDS.create_from_list
      ~equiv:(Typecheck.type_equiv problem.tc)
      all_types

  let initialize_context
      ~(context:Context.t)
      ~(value_filter:Value.t -> bool)
      (ts:Type.t list)
      (inputs:Value.t list)
      ((input_type,output_type):Type.t * Type.t)
      (final_candidates:Value.t -> Value.t -> bool)
    : t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes context.tc)
           ts)

    in
    let ds = create_ds_from_t_list_context ~context ts in
    let a = A.empty () in
    let d = TypeToStates.empty in
    let input_vals = inputs in
    let tset = TransitionSet.empty in
    let (input_type,_) = TypeDS.find_representative ds input_type in
    let (output_type,_) = TypeDS.find_representative ds output_type in
    let all_states = StateSet.empty in
    let c =
      {
        a                 ;
        d                 ;
        ds                ;
        inputs            ;
        tset              ;
        final_candidates  ;
        all_types         ;
        up_to_date = true ;
        input_type        ;
        output_type       ;
        min_term_state = None;
        all_states        ;
        value_filter      ;
        dupe_ref = None   ;
      }
    in
    List.iter
      ~f:(fun i ->
          let _ =
            add_transition
              c
              Var
              []
              (val_state c [(i,i)] (input_type,TermClassification.Elimination))
              input_type
              true
          in
          let _ =
            add_transition
              c
              Var
              []
              (val_state c [(i,i)] (input_type,TermClassification.Introduction))
              input_type
              true
          in
          ())
      input_vals;
    c

  let initialize
      ~(problem:Problem.t)
      ~(value_filter:Value.t -> bool)
      (ts:Type.t list)
      (inputs:Value.t list)
      ((input_type,output_type):Type.t * Type.t)
      (final_candidates:Value.t -> Value.t -> bool)
    : t =
    let all_types =
      List.dedup_and_sort ~compare:Type.compare
        (List.concat_map
           ~f:(Typecheck.all_subtypes problem.tc)
           ts)

    in
    let ds = create_ds_from_t_list ~problem ts in
    let a = A.empty () in
    let d = TypeToStates.empty in
    let input_vals = inputs in
    let tset = TransitionSet.empty in
    let (input_type,_) = TypeDS.find_representative ds input_type in
    let (output_type,_) = TypeDS.find_representative ds output_type in
    let all_states = StateSet.empty in
    let c =
      {
        a                 ;
        d                 ;
        ds                ;
        inputs            ;
        tset              ;
        final_candidates  ;
        all_types         ;
        up_to_date = true ;
        input_type        ;
        output_type       ;
        min_term_state = None;
        all_states        ;
        value_filter      ;
        dupe_ref = None   ;
      }
    in
    List.iter
      ~f:(fun i ->
          let _ =
            add_transition
              c
              Var
              []
              (val_state c [(i,i)] (input_type,TermClassification.Elimination))
              input_type
              true
          in
          let _ =
            add_transition
              c
              Var
              []
              (val_state c [(i,i)] (input_type,TermClassification.Introduction))
              input_type
              true
          in
          ())
      input_vals;
    c

  let get_all_types
      (c:t)
    : Type.t list =
    c.all_types

  let get_all_state_pairs
      (c:t)
    : (Value.t list) list =
    let all_states = A.states c.a in
    let all_pairs =
      List.filter_map
        ~f:(fun s ->
            begin match State.destruct_vals s with
              | Some (vsps,_) ->
                Some (List.map ~f:fst vsps)
              | _ ->
                None
            end)
        all_states
    in
    List.dedup_and_sort
      ~compare:(compare_list ~cmp:Value.compare)
      all_pairs

  (*let add_let_ins
      (c:t)
    : unit =
    List.iter
      ~f:(fun (s1,s2) ->
          begin match (s1,s2) with
            | (Vals ([v11,v12],_), Vals ([v21,v22],t)) ->
              if c.final_candidates v21 v22 &&
                 (Value.equal v12 v21) &&
                 List.mem ~equal:Value.equal (Value.strict_subvalues v11) v12
              then
                add_transition
                  c
                  LetIn
                  [s1;s2]
                  (val_state c [v11,v22] t)
                  true
              else
                ()
            | _ -> ()
          end)
      (List.cartesian_product (A.states c.a) (A.states c.a))*)

  let add_final_state
      (c:t)
      (s:State.t)
    : unit =
    A.add_final_state c.a s;
    invalidate_computations c

  let minimize
      (c:t)
    : t =
    Consts.time
      Consts.minify_times
      (fun _ ->
         let a = A.minimize c.a in
         { c with a ; up_to_date=false })

  let add_destructors
      (c:t)
    : unit =
    let all_destructor_types =
      List.dedup_and_sort
        ~compare:Type.compare
        (List.filter
           ~f:(Option.is_some % Type.destruct_variant)
           (List.map
              ~f:(fst % TypeDS.find_representative c.ds)
              c.all_types))
    in
    let all_final_states = A.final_states c.a in
    let all_transformations =
      List.concat_map
        ~f:(fun (t:Type.t) ->
            let ct = (t,TermClassification.Elimination) in
            let branch_ids = List.map ~f:fst (Type.destruct_variant_exn t) in
            let tid = Transition.VariantSwitch branch_ids in
            cartesian_map
              ~f:(fun (smatch:State.t) (sfinal:State.t) ->
                  begin match smatch with
                    | Vals ([_,v],_) ->
                      begin match Value.node v with
                        | Ctor (i,_) ->
                          let ins =
                            smatch::
                            List.map
                              ~f:(fun i' ->
                                  if Id.equal i i' then
                                    sfinal
                                  else
                                    State.top)
                              branch_ids
                          in
                          (tid,ins,sfinal)
                        | _ -> failwith "invalid"
                      end
                    | _ -> failwith "invalid"
                  end)
              (StateSet.as_list (TypeToStates.lookup_default ~default:StateSet.empty c.d ct))
              all_final_states
          )
        all_destructor_types
    in
    List.iter
      ~f:(fun (t,ins,out) ->
          let _ =
            add_transition
              c
              t
              ins
              out
              c.output_type
              true
          in
          ())
      all_transformations


  let add_states
      (c:t)
      (states:((Value.t * Value.t) list * ClassifiedType.t) list)
    : bool list =
    List.map
      ~f:(fun (vvs,t) ->
          add_state c vvs t)
      states

  let recursion_targets
      (c:t)
    : State.t list =
    List.filter
      ~f:(fun s ->
          let ps = A.transitions_from c.a s in
          (not (State.equal s State.top)) &&
          List.exists
            ~f:(fun (t,ss,_) ->
                begin match (Transition.id t,ss) with
                  | (Transition.LetIn,[_;s2])
                    (*when State.equal s2 s*) ->
                    true
                  | _ -> false
                end)
            ps)
      (A.states c.a)

  let intersect
      (c1:t)
      (c2:t)
    : t =
    (*print_endline @$ string_of_int (A.size c1.a);
      print_endline @$ string_of_int (A.size c2.a);*)
    Consts.time
      Consts.isect_times
      (fun () ->
         let merge_tset
             (c1:TransitionSet.t)
             (c2:TransitionSet.t)
           : TransitionSet.t =
           let merged = TransitionSet.union c1 c2 in
           (*let all_ts_by_id =
             group_by
               ~key:(Transition.id)
               ~equal:Transition.equal_id
               (TransitionSet.as_list merged)
           in
           List.iter
             ~f:(fun l ->
                 print_endline "here";
                 List.iter
                   ~f:(fun l -> print_endline @$ Transition.show l)
                   l;
                 assert (List.length l = 1))
             all_ts_by_id;*)
           merged
         in
         let ts =
           TransitionSet.as_list
             (merge_tset c1.tset c2.tset)
         in
         List.iter
           ~f:(update_tset c1)
           ts;
         List.iter
           ~f:(update_tset c2)
           ts;
         let ts_initial = List.filter ~f:(fun t -> Transition.arity t = 0) ts in
         let a = A.intersect ts_initial c1.a c2.a in
         let inputs = c1.inputs@c2.inputs in
         let c = { c1 with a; inputs } in
         invalidate_computations c;
         c)

  module StateToTree = DictOf(State)(A.Term)
  module StateToTree' = DictOf(State)(PairOf(IntModule)(A.Term))
  module StateToProd = DictOf(State)(PairOf(Transition)(ListOf(State)))

  let rec term_size
      (t:A.Term.t)
    : int =
    begin match t with
      | Term (_,ts) -> List.fold_left ~f:(fun i t -> i+(term_size t)) ~init:1 ts
    end

  module ProductionPQ = PriorityQueueOf(struct
      module Priority = IntModule
      type t = int * A.Term.t * State.t
      [@@deriving eq, hash, ord, show]
      let priority = fst3
    end)

  type min_tree_acc = StateToTree.t * (Transition.t * State.t list * State.t) list
  module PQ = PriorityQueueOf(struct
      module Priority = IntModule
      type t = (int * StateToProd.t * State.t list * StateSet.t)
      let priority (i,_,_,_) = i

      let compare _ _ = failwith "no impl"
      let hash _ = failwith "no impl"
      let hash_fold_t _ _ = failwith "no impl"
      let equal _ _ = failwith "no impl"
      let pp _ _ = failwith "no impl"
      let show _ = failwith "no impl"
    end)
  type min_tree_acc' = StateToTree.t * (A.term * State.t) list

  let min_tree'
      (c:t)
    : A.term =
    let get_produced_from
        (st:StateToTree'.t)
        (t:Transition.t)
        (ss:State.t list)
      : (int * A.Term.t) option =
      let subs =
        List.map
          ~f:(fun s -> StateToTree'.lookup st s)
          ss
      in
      Option.map
        ~f:(fun iss ->
            let (ints,ss) = List.unzip iss in
            let size = List.fold ~f:(+) ~init:1 ints in
            (size,A.Term (t,ss)))
        (distribute_option subs)
    in
    let rec min_tree_internal
        (st:StateToTree'.t)
        (pq:ProductionPQ.t)
      : A.Term.t =
      begin match ProductionPQ.pop pq with
        | Some ((i,t,s),_,pq) ->
          if A.is_final_state c.a s then
            t
          else if StateToTree'.member st s then
            min_tree_internal st pq
          else
            let st = StateToTree'.insert st s (i,t) in
            let triggered_transitions = A.transitions_from c.a s in
            let produced =
              List.filter_map
                ~f:(fun (t,ss,s) ->
                    Option.map
                      ~f:(fun (i,t) -> (i,t,s))
                      (get_produced_from st t ss))
                triggered_transitions
            in
            let pq = ProductionPQ.push_all pq produced in
            min_tree_internal st pq
        | None ->
          failwith "no tree"
      end
    in
    let initial_terms =
      List.filter_map
        ~f:(fun (t,ss,s) ->
            Option.map
              ~f:(fun (i,t) -> (i,t,s))
              (get_produced_from StateToTree'.empty t ss))
        (A.transitions c.a)
    in
    min_tree_internal
      StateToTree'.empty
      (ProductionPQ.from_list initial_terms)

  let rec contains_var
      (Term (t,ts):A.Term.t)
    : bool =
    (Transition.equal_id (Transition.id t) Transition.Var)
    || (List.exists ~f:contains_var ts)

  let rec contains_rec
      (Term (t,ts):A.Term.t)
    : bool =
    (Transition.equal_id (Transition.id t) Transition.Rec)
    || (List.exists ~f:contains_rec ts)

  let term_cost ?(print=false) t =
    if !Consts.use_random then
      1.0
    else
      let terms = ref [] in
      let rec term_cost_internal
          (Term (t,ts) as fullt:A.Term.t)
        : Float.t =
        if List.mem ~equal:A.Term.equal !terms fullt then
          2.0
        else
          let simple_subcost ts =
            List.fold
              ~f:(+.)
              ~init:0.
              (List.map ~f:(term_cost_internal) ts)
          in
          terms := fullt::!terms;
          begin match Transition.id t with
            | FunctionApp _ -> (Float.of_int (List.length ts)) +. simple_subcost ts
            | Apply ->
              simple_subcost ts
            | VariantConstruct i -> 2. +. simple_subcost ts
            | UnsafeVariantDestruct _ ->
              1. +. simple_subcost ts
            | TupleConstruct _ ->
              1. +. simple_subcost ts
            | TupleDestruct _ ->
              begin match ts with
                | [Term (t,_)] ->
                  begin match Transition.id t with
                    | Var -> 1.
                    | _ -> 1. +. simple_subcost ts
                  end
                | _ -> failwith "invalid"
              end
            | Var -> (*0.*)
              1.
            | Rec -> (*1. +. simple_subcost ts*)
              1. +. simple_subcost ts
            | VariantSwitch is -> (*2. +. simple_subcost ts*)
              5. +. (Float.of_int (List.length is)) +. simple_subcost ts
            | LetIn -> failwith "ah"
          end
      in
      term_cost_internal t

  let termstate_cost ?(print=false) t =
    term_cost (A.TermState.to_term t)

  let call_cost
      ((vin,vout):Value.t * Value.t)
    : Float.t =
    Float.of_int (Value.size vout - Value.size vin)

  let rec extract_recursive_calls
      (ts:A.TermState.t)
    : (A.TermState.t * State.t) list =
    begin match ts with
      | TS (t,target,[source_ts]) ->
        if Transition.equal_id (Transition.id t) Transition.Rec then
          (source_ts,target)::(extract_recursive_calls source_ts)
        else
          List.concat_map
            ~f:(extract_recursive_calls)
            [source_ts]
      | TS (_,_,tss) ->
        List.concat_map
          ~f:(extract_recursive_calls)
          tss
    end

  let extract_recursive_requirements
      (sin:A.TermState.t)
      (sout:State.t)
    : (Value.t * Value.t * Value.t * A.Term.t) list =
    begin match (State.destruct_vals (A.TermState.get_state sin),State.destruct_vals sout) with
      | (Some (vvsin,_), Some (vvsout,_)) ->
        let t = A.TermState.to_term sin in
        let outs = List.map ~f:snd vvsout in
        let inouts = List.zip_exn vvsin outs in
        List.map ~f:(fun ((exv,vsin),vsout) -> (exv,vsin,vsout,t)) inouts
      | (None, None) ->
        []
      | _ -> failwith "when would this happen?"
    end

  let calls
      (ts:A.TermState.t)
    : (Value.t * Value.t) list =
    List.dedup_and_sort ~compare:(pair_compare Value.compare Value.compare)
      (List.concat_map
         ~f:(fun (ts,s) ->
             let vss = extract_recursive_requirements ts s in
             List.map ~f:(fun (_,v1,v2,_) -> (v1,v2)) vss)
         (extract_recursive_calls ts))

  let cost t =
    term_cost (A.TermState.to_term t)

  let rec is_valid_term
      (Term (t,ts):A.Term.t)
    : bool =
    begin match Transition.id t with
      | Rec ->
        (List.exists ~f:contains_var ts) && not (List.exists ~f:contains_rec ts)
      | VariantConstruct i ->
        begin match ts with
          | [Term (t,_)] ->
            begin match Transition.id t with
              | UnsafeVariantDestruct i' ->
                not (Id.equal i i')
              | _ -> true
            end
          | _ -> true
        end
      | UnsafeVariantDestruct i ->
        begin match ts with
          | [Term (t,_)] ->
            begin match Transition.id t with
              | VariantConstruct i' ->
                not (Id.equal i i')
              | _ -> true
            end
          | _ -> true
        end
      | _ -> true
    end

  let is_valid_calls
      (c:(Value.t * Value.t) list)
    : bool =
    let kg = group_by_keys ~is_eq:Value.equal c in
    List.for_all ~f:(fun (_,vs) -> List.length vs = 1) kg

  let is_valid_ts
      (ts:A.TermState.t)
    : bool =
    is_valid_term (A.TermState.to_term ts)
    && is_valid_calls (calls ts)

  let min_term_state
      (c:t)
    : A.TermState.t option =
    begin match c.min_term_state with
      | Some mts -> mts
      | None ->
        let mts =
          let basic_mts =
            Consts.time
              Consts.min_elt_times
              (fun _ -> A.min_term_state c.a ~f:is_valid_ts ~cost ~reqs:calls)
          in
          begin match basic_mts with
            | None ->
              basic_mts
            | Some mts ->
              basic_mts
              (*if List.is_empty (extract_unbranched_switches (A.TermState.to_term mts)) then
                basic_mts
                else
                Consts.time
                  Consts.min_elt_times
                  (fun _ -> A.min_term_state c.a ~f:is_valid_term ~cost:term_cost ~reqs:(List.dedup_and_sort ~compare:State.compare % extract_unbranched_states)(*fun _ -> []*))*)
          end
        in
        c.min_term_state <- Some mts;
        mts
    end

  let min_term_state_silly
      (c:t)
      (contained:A.Term.t -> bool)
      (endcontained:A.Term.t -> bool)
    : A.TermState.t option =
    begin match c.min_term_state with
      | Some mts -> mts
      | None ->
        let mts =
          let basic_mts =
            Consts.time
              Consts.min_elt_times
              (fun _ -> A.min_term_state_silly c.a ~f:(fun ts -> is_valid_ts ts && not (endcontained (A.TermState.to_term ts))) ~cost ~reqs:(fun ts -> contained (A.TermState.to_term ts)))
          in
          begin match basic_mts with
            | None ->
              basic_mts
            | Some mts ->
              basic_mts
              (*if List.is_empty (extract_unbranched_switches (A.TermState.to_term mts)) then
                basic_mts
                else
                Consts.time
                  Consts.min_elt_times
                  (fun _ -> A.min_term_state c.a ~f:is_valid_term ~cost:term_cost ~reqs:(List.dedup_and_sort ~compare:State.compare % extract_unbranched_states)(*fun _ -> []*))*)
          end
        in
        c.min_term_state <- Some mts;
        mts
    end

  let size (c:t)
    : int =
    A.size c.a

  (*let accepts_term
      (c:t)
      (t:A.Term.t)
    : bool =
    Consts.time
      Consts.accepts_term_time
      (fun _ -> A.accepts_term c.a t)*)

  let size_compare
      (c1:t)
      (c2:t)
    : int =
    Int.compare (size c1) (size c2)

  let rec all_transitions
      (Term (t,ts):A.Term.t)
    : Transition.t list =
    t::(List.concat_map ~f:all_transitions ts)

  let accepts_term
      (x:t)
      (term:A.Term.t)
    : bool =
    let all_transitions = all_transitions term in
    List.iter
      ~f:(update_tset x)
      all_transitions;
    Option.is_some (A.accepting_term_state x.a term)

  let rec_
      (c:t)
    : Transition.t =
    Transition.create (Transition.Rec, c.output_type, 1)
end
