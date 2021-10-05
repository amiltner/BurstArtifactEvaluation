open MyStdLib

module type Symbol =
sig
  include Data
  val arity : t -> int
  val cost : t -> int
end

module type State =
sig
  include Data
  val product : t -> t -> t option
end

module type Automaton =
sig
  module Symbol : Symbol
  module State : State

  type term =  Term of Symbol.t * (term list)
  module Term : sig
    include Data with type t = term
  end

  type term_state = TS of Symbol.t * State.t * term_state list
  module TermState :
  sig
    include Data with type t = term_state

    val to_term : t -> term

    val get_state : t -> State.t
  end

  type t
  val show : t shower
  val pp : t pper
  val compare : t comparer
  val equal : t equality_check

  val empty : unit -> t
  val intersect : Symbol.t list -> t -> t -> t
  val copy : t -> t
  val add_transition : t -> Symbol.t -> State.t list -> State.t -> unit
  val remove_transition : t -> Symbol.t -> State.t list -> State.t -> unit
  val states : t -> State.t list
  val final_states : t -> State.t list
  val is_final_state : t -> State.t -> bool
  val add_final_state : t -> State.t -> unit
  val remove_final_state : t -> State.t -> unit
  val has_state : t -> State.t -> bool
  (*val is_empty : t -> bool*)
  (*val accepts_term : t -> Term.t -> bool*)
  val accepting_term_state : t -> Term.t -> TermState.t option
  val transitions_from
    : t
    -> State.t
    -> (Symbol.t * (State.t list) * State.t) list
  val transitions_to : t -> State.t -> (Symbol.t * (State.t list)) list
  val transitions : t -> (Symbol.t * (State.t list) * State.t) list
  val minimize : t -> t
  val size : t -> int
  val min_term_state :
    f:(TermState.t -> bool) ->
    cost:(TermState.t -> Float.t) ->
    reqs:(TermState.t -> (Lang.Value.t * Lang.Value.t) list) ->
    t ->
    term_state option
  val min_term_state_silly :
    f:(TermState.t -> bool) ->
    cost:(TermState.t -> Float.t) ->
    reqs:(TermState.t -> bool) ->
    t ->
    term_state option
end

module type AutomatonBuilder =
  functor (Symbol : Symbol) ->
  functor (State : State) ->
    Automaton with module Symbol := Symbol
               and module State := State

module TimbukBuilder : AutomatonBuilder =
  functor (Symbol : Symbol) ->
  functor (State : State) ->
  struct
    (* A is the timbuk automaton module *)
    module A =
    struct
      module Symb =
      struct
        include Symbol

        let print a b = pp b a
      end

      module St =
      struct
        include State

        let print a b = pp b a
      end

      include Timbuk.Automaton.Make(Symb)(St)

      let equal a1 a2 = is_equal (compare a1 a2)
      let pp a b = print b a
    end

    type t = A.t
    [@@deriving eq, ord, show]

    module Symbol = Symbol
    module State = State

    type term = Term of Symbol.t * (term list)
    [@@deriving hash, eq, ord, show]

    module Term = struct
      type t = term
      [@@deriving hash, eq, ord, show]
    end

    type term_state = TS of Symbol.t * State.t * term_state list
    [@@deriving hash, eq, ord, show]

    module TermState =
    struct
      type t = term_state
      [@@deriving eq, hash, ord, show]

      let rec to_term
          (TS (t,_,tss):t)
        : Term.t =
        Term (t,List.map ~f:to_term tss)

      let get_state
          (TS (_,s,tss):t)
        : State.t =
        s
    end

    let empty = A.empty

    let copy = A.copy

    let intersect s a1 a2 =
      A.inter s a1 a2

    let add_transition a s sts st =
      A.add_transition
        (A.Configuration.create (
           (s
           ,
               sts)))
        st
        a

    let remove_transition a s sts st =
      A.remove_transition
        (A.Configuration.create (
           (s
           ,
               sts)))
        st
        a

    let states a =
      A.StateSet.as_list
        (A.states a)

    let final_states a =
      A.StateSet.as_list
        (A.final_states a)

    let is_final_state a s =
      A.StateSet.contains
        s
        (A.final_states a)

    let add_final_state a f =
      A.add_final_state f a

    let remove_final_state a f =
      A.remove_final_state f a

    let has_state
        a
        s
      =
      A.StateSet.contains s (A.states a)

    (*let is_empty a =
      Option.is_some
        (A.pick_term_opt
           a)

    let pick_term a =
      let bt =
        Option.value_exn
          (A.pick_term_opt
             a)
      in
      let rec c_bt
          ((bt,_):A.BoundTerm.t)
        : term =
        begin match bt with
          | A.BoundTerm.Term (s,bts) ->
            let ts = List.map ~f:c_bt bts in
            Term (s,ts)
          | _ -> failwith "ah"
        end
      in
      c_bt bt*)

    let transitions_from a s =
      let ps = A.state_parents s a in
      let cs = A.ConfigurationSet.as_list ps in
      List.concat_map
        ~f:(fun c ->
            let ss =
              A.StateSet.as_list
                (A.states_for_configuration c a)
            in
            let (i,vs) = A.Configuration.node c in
            List.map ~f:(fun s -> (i,vs,s)) ss)
        cs

    let transitions_to
        a
        s
      : (Symbol.t * (State.t list)) list =
      let configs =
        A.configurations_for_state
          s
          a
      in
      List.map
        ~f:(fun c ->
            A.Configuration.node c)
        (A.ConfigurationSet.as_list configs)

    let transitions
        (c:t)
      : (Symbol.t * (State.t list) * State.t) list =
      A.fold_transitions
        (fun (sy,ss) s acc -> (sy,ss,s)::acc)
        c
        []

    let minimize = A.prune_useless

    let size = A.state_count

    (*let accepts_term a t =
      let rec term_to_aterm t : Symbol.t Timbuk.Term.term =
        begin match t with
          | Term (i,ts) ->
            Term (i,List.map ~f:term_to_aterm ts)
        end
      in
      A.recognizes (term_to_aterm t) a*)

    type comparison =
      | Incomparable
      | Equal
      | StrictlyLess
      | StrictlyGreater

    module TSData = ListOf(TripleOf(FloatModule)(ListOf(PairOf(Lang.Value)(Lang.Value)))(TermState))
    module StateToTS = DictOf(State)(TSData)

    let compare_terms
        ((c1,r1s,t1):Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t)
        ((c2,r2s,t2):Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t)
      : comparison =
      let cc =
        Float.(
          if c1 <. c2 then
            StrictlyLess
          else if c1 >. c2 then
            StrictlyGreater
          else
            Equal)
      in
      let rc =
        let size1 = List.length r1s in
        let size2 = List.length r2s in
        if size1 = size2 then
          if List.equal
              (fun (v11,v12) (v21,v22) ->
                 Lang.Value.equal v11 v21 && Lang.Value.equal v12 v22)
              r1s
              r2s then
            Equal
          else
            Incomparable
        else if size1 < size2 then
          if sublist_on_sorted ~cmp:(pair_compare Lang.Value.compare Lang.Value.compare) r1s r2s then
              StrictlyLess
            else
              Incomparable
          else
          if sublist_on_sorted ~cmp:(pair_compare Lang.Value.compare Lang.Value.compare) r2s r1s then
            StrictlyGreater
          else
            Incomparable
      in
      begin match (cc,rc) with
        | (Incomparable, _) -> Incomparable
        | (_, Incomparable) -> Incomparable
        | (Equal, _) -> rc
        | (_, Equal) -> cc
        | (StrictlyLess, StrictlyLess) -> StrictlyLess
        | (StrictlyGreater, StrictlyGreater) -> StrictlyGreater
        | _ -> Incomparable
      end

    let extract_minimal_list
        (ls:(Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t) list)
        (input:(Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t))
      : (Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t) list option =
      let rec extract_minimal_list_internal
          (acc:(Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t) list)
          (ls:(Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t) list)
        : (Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t) list option =
        begin match ls with
          | [] ->
            Some (input::acc)
          | h::t ->
            begin match compare_terms input h with
              | Incomparable ->
                extract_minimal_list_internal
                  (h::acc)
                  t
              | Equal | StrictlyGreater ->
                None
              | StrictlyLess ->
                extract_minimal_list_internal
                  acc
                  t
            end

        end
      in
      let mlo = extract_minimal_list_internal [] ls in
      Option.map ~f:(List.sort ~compare:(triple_compare Float.compare (List.compare (pair_compare Lang.Value.compare Lang.Value.compare)) compare_term_state)) mlo

    module TSPQ = PriorityQueueOf(struct
        module Priority = FloatModule
        type t = Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t * State.t
        [@@deriving eq, hash, ord, show]
        let priority = fun (x,_,_,_) -> x
      end)
    let min_term_state
        ~(f:TermState.t -> bool)
        ~(cost:TermState.t -> Float.t)
        ~(reqs:TermState.t -> (Lang.Value.t * Lang.Value.t) list)
        (a:t)
      : TermState.t option =
      let pops = ref 0 in
      let get_produced_from
          (st:StateToTS.t)
          (t:Symbol.t)
          (s:State.t)
          (ss:State.t list)
        : (Float.t * (Lang.Value.t * Lang.Value.t) list * TermState.t) list =
        let subs =
          List.map
            ~f:(fun s -> StateToTS.lookup_default ~default:[] st s)
            ss
        in
        List.map
          ~f:(fun iss ->
              let (ints,_,ss) = List.unzip3 iss in
              let ts = TS (t,s,ss) in
              let reqs = reqs ts in
              let size = cost ts in
              (size,reqs,TS (t,s,ss)))
          (combinations subs)
      in
      let rec min_tree_internal
          (st:StateToTS.t)
          (pq:TSPQ.t)
        : TermState.t option =
        (*print_endline "BEGIN";
        print_endline @$ StateToTS.show st;
        print_endline @$ string_of_int @$ TSPQ.length pq;
          print_endline "END\n\n\n\n";*)
        pops := !pops+1;
        begin match TSPQ.pop pq with
          | Some ((c,rs,t,s),_,pq) ->
            (*print_endline ("State: " ^ (State.show s));*)
            if f t then
              if is_final_state a s (*&& List.is_empty rs*) then
                begin
                  (*print_endline (string_of_int !pops);*)
                  (*print_endline (Float.to_string c);*)
                  Some t
                end
              else
                begin match StateToTS.lookup st s with
                  | None ->
                    (*print_endline "NEW ONE";*)
                    let st = StateToTS.insert st s [(c,rs,t)] in
                    let triggered_transitions = transitions_from a s in
                    (*List.iter
                      ~f:(fun (sy,ss,out) ->
                          if (List.length ss = 1) then
                            begin
                              print_endline (Symbol.show sy);
                              print_endline (State.show out);
                              print_endline "\n";
                            end
                          else
                            ()
                        )
                      triggered_transitions;
                      print_endline ("StateDone:");*)
                    let produced =
                      List.concat_map
                        ~f:(fun (t,ss,s) ->
                            List.map
                              ~f:(fun (i,ss,t) -> (i,ss,t,s))
                              (get_produced_from st t s ss))
                        triggered_transitions
                    in
                    let pq = TSPQ.push_all pq produced in
                    min_tree_internal st pq
                  | Some ts ->
                    begin match extract_minimal_list ts (c,rs,t) with
                      | None ->
                        (*print_endline "OLD ONE NO CHANGE";*)
                        min_tree_internal st pq
                      | Some ml ->
                        (*print_endline "OLD ONE YES CHANGE";
                          print_endline (StateToTS.show_value ts);
                          print_endline (StateToTS.show_value ml);*)
                        let st = StateToTS.insert st s ml in
                        let st_for_produced = StateToTS.insert st s [(c,rs,t)] in
                        let triggered_transitions = transitions_from a s in
                        let produced =
                          List.concat_map
                            ~f:(fun (t,ss,s) ->
                                List.map
                                  ~f:(fun (i,ss,t) -> (i,ss,t,s))
                                  (get_produced_from st_for_produced t s ss))
                            triggered_transitions
                        in
                        let pq = TSPQ.push_all pq produced in
                        min_tree_internal st pq
                    end
                end
            else
              min_tree_internal st pq
          | None ->
            (*List.iter
              ~f:(fun kv -> print_endline @$ (string_of_pair State.show TSData.show) kv)
              (StateToTS.as_kvp_list st);*)
            None
        end
      in
      let initial_terms =
        List.concat_map
          ~f:(fun (t,ss,s) ->
              List.map
                ~f:(fun (i,ss,t) -> (i,ss,t,s))
                (get_produced_from StateToTS.empty t s ss))
          (transitions a)
      in
      min_tree_internal
        StateToTS.empty
        (TSPQ.from_list initial_terms)

    let accepting_term_state (a:t) (t:term) : TermState.t option =
      let rec accepting_term_state_state t q =
        begin match t with
          | Term (i,ts) ->
            List.find_map
              ~f:(fun (i',ss) ->
                  if Symbol.equal i i' then
                    let ts_ss = List.zip_exn ts ss in
                    Option.map
                      ~f:(fun ts -> TS (i,q,ts))
                      (distribute_option
                         (List.map
                            ~f:(uncurry accepting_term_state_state)
                            ts_ss))
                  else
                    None)
              (transitions_to a q)
        end
      in
      List.find_map ~f:(accepting_term_state_state t) (final_states a)

    type myholder = Float.t * bool * TermState.t
    [@@deriving eq, hash, ord, show]

    module TSPQSilly = PriorityQueueOf(struct
        module Priority = FloatModule
        type t = Float.t * bool * TermState.t * State.t
        [@@deriving eq, hash, ord, show]
        let priority = fun (x,_,_,_) -> x
      end)

    module TSDataSilly = ListOf(TripleOf(FloatModule)(BoolModule)(TermState))
    module StateToTSSilly = DictOf(State)(TSDataSilly)

    let compare_terms
        ((c1,b1,t1):Float.t * bool * TermState.t)
        ((c2,b2,t2):Float.t * bool * TermState.t)
      : comparison =
      let cc =
        Float.(
          if c1 <. c2 then
            StrictlyLess
          else if c1 >. c2 then
            StrictlyGreater
          else
            Equal)
      in
      let rc =
        begin match (b1,b2) with
          | (true,true) -> Incomparable
          | (true,false) -> StrictlyGreater
          | (false,true) -> StrictlyLess
          | (false,false) -> Equal
        end
      in
      begin match (cc,rc) with
        | (Incomparable, _) -> Incomparable
        | (_, Incomparable) -> Incomparable
        | (Equal, _) -> rc
        | (_, Equal) -> cc
        | (StrictlyLess, StrictlyLess) -> StrictlyLess
        | (StrictlyGreater, StrictlyGreater) -> StrictlyGreater
        | _ -> Incomparable
      end

    let extract_minimal_list
        (ls:(Float.t * bool * TermState.t) list)
        (input:(Float.t * bool * TermState.t))
      : (Float.t * bool * TermState.t) list option =
      let rec extract_minimal_list_internal
          (acc:(Float.t * bool * TermState.t) list)
          (ls:(Float.t * bool * TermState.t) list)
        : (Float.t * bool * TermState.t) list option =
        if (List.mem ~equal:equal_myholder acc input) then
          None
        else
          begin match ls with
            | [] ->
              Some (input::acc)
            | h::t ->
              begin match compare_terms input h with
                | Incomparable ->
                  extract_minimal_list_internal
                    acc
                    t
                | Equal | StrictlyGreater ->
                  None
                | StrictlyLess ->
                  extract_minimal_list_internal
                    acc
                    t
              end

          end
      in
      let mlo = extract_minimal_list_internal [] ls in
      Option.map ~f:(List.sort ~compare:(triple_compare Float.compare Bool.compare compare_term_state)) mlo

    let min_term_state_silly
        ~(f:TermState.t -> bool)
        ~(cost:TermState.t -> Float.t)
        ~(reqs:TermState.t -> bool)
        (a:t)
      : TermState.t option =
      let pops = ref 0 in
      let get_produced_from
          (st:StateToTSSilly.t)
          (t:Symbol.t)
          (s:State.t)
          (ss:State.t list)
        : (Float.t * bool * TermState.t) list =
        let subs =
          List.map
            ~f:(fun s -> StateToTSSilly.lookup_default ~default:[] st s)
            ss
        in
        List.map
          ~f:(fun iss ->
              let (ints,_,ss) = List.unzip3 iss in
              let ts = TS (t,s,ss) in
              let reqs = reqs ts in
              let size = cost ts in
              (size,reqs,TS (t,s,ss)))
          (combinations subs)
      in
      let rec min_tree_internal
          (st:StateToTSSilly.t)
          (pq:TSPQSilly.t)
        : TermState.t option =
        (*print_endline "BEGIN";
        print_endline @$ StateToTS.show st;
        print_endline @$ string_of_int @$ TSPQ.length pq;
          print_endline "END\n\n\n\n";*)
        pops := !pops+1;
        begin match TSPQSilly.pop pq with
          | Some ((c,rs,t,s),_,pq) ->
            (*print_endline ("State: " ^ (State.show s));*)
            if f t then
              if is_final_state a s (*&& List.is_empty rs*) then
                begin
                  (*print_endline (string_of_int !pops);*)
                  (*print_endline (Float.to_string c);*)
                  Some t
                end
              else
                begin match StateToTSSilly.lookup st s with
                  | None ->
                    (*print_endline "NEW ONE";*)
                    let st = StateToTSSilly.insert st s [(c,rs,t)] in
                    let triggered_transitions = transitions_from a s in
                    (*List.iter
                      ~f:(fun (sy,ss,out) ->
                          if (List.length ss = 1) then
                            begin
                              print_endline (Symbol.show sy);
                              print_endline (State.show out);
                              print_endline "\n";
                            end
                          else
                            ()
                        )
                      triggered_transitions;
                      print_endline ("StateDone:");*)
                    let produced =
                      List.concat_map
                        ~f:(fun (t,ss,s) ->
                            List.map
                              ~f:(fun (i,ss,t) -> (i,ss,t,s))
                              (get_produced_from st t s ss))
                        triggered_transitions
                    in
                    let pq = TSPQSilly.push_all pq produced in
                    min_tree_internal st pq
                  | Some ts ->
                    begin match extract_minimal_list ts (c,rs,t) with
                      | None ->
                        (*print_endline "OLD ONE NO CHANGE";*)
                        min_tree_internal st pq
                      | Some ml ->
                        (*print_endline "OLD ONE YES CHANGE";
                          print_endline (StateToTSSilly.show_value ts);
                          print_endline (StateToTSSilly.show_value ml);*)
                        let st = StateToTSSilly.insert st s ml in
                        let st_for_produced = StateToTSSilly.insert st s [(c,rs,t)] in
                        let triggered_transitions = transitions_from a s in
                        let produced =
                          List.concat_map
                            ~f:(fun (t,ss,s) ->
                                List.map
                                  ~f:(fun (i,ss,t) -> (i,ss,t,s))
                                  (get_produced_from st_for_produced t s ss))
                            triggered_transitions
                        in
                        let pq = TSPQSilly.push_all pq produced in
                        min_tree_internal st pq
                    end
                end
            else
              min_tree_internal st pq
          | None ->
            (*List.iter
              ~f:(fun kv -> print_endline @$ (string_of_pair State.show TSData.show) kv)
              (StateToTS.as_kvp_list st);*)
            None
        end
      in
      let initial_terms =
        List.concat_map
          ~f:(fun (t,ss,s) ->
              List.map
                ~f:(fun (i,ss,t) -> (i,ss,t,s))
                (get_produced_from StateToTSSilly.empty t s ss))
          (transitions a)
      in
      min_tree_internal
        StateToTSSilly.empty
        (TSPQSilly.from_list initial_terms)

    let accepting_term_state_silly (a:t) (t:term) : TermState.t option =
      let rec accepting_term_state_state t q =
        begin match t with
          | Term (i,ts) ->
            List.find_map
              ~f:(fun (i',ss) ->
                  if Symbol.equal i i' then
                    let ts_ss = List.zip_exn ts ss in
                    Option.map
                      ~f:(fun ts -> TS (i,q,ts))
                      (distribute_option
                         (List.map
                            ~f:(uncurry accepting_term_state_state)
                            ts_ss))
                  else
                    None)
              (transitions_to a q)
        end
      in
      List.find_map ~f:(accepting_term_state_state t) (final_states a)
  end
