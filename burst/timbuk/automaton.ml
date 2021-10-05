open Collections

module type STATE = Pattern.VARIABLE
module type TYPE = TypedTerm.TYPE

module type ConfigS = sig
  include MyStdLib.Data

  type t_node
  val node : t -> t_node
  val product : t -> t -> t option
  val create : t_node -> t
end

module type BASE = sig
  module Sym : Symbol.S
  module State : STATE
  module Configuration : ConfigS with type t = (Sym.t * State.t list) (*MyStdLib.hash_consed*) and type t_node = Sym.t * State.t list
  module StateSet : MyStdLib.HashSet.ImperativeSet with type elt = State.t
  module StateMap : MyStdLib.HashTable.ImperativeDict with type key = State.t
  module ConfigurationSet : MyStdLib.HashSet.ImperativeSet with type elt = Configuration.t
  module ConfigurationMap : MyStdLib.HashTable.ImperativeDict with type key = Configuration.t
  type t
  type data
  val create : data -> t
  val empty : unit -> t
  val data : t -> data
  val clear : t -> t
  val copy : t -> t
  val final_states : t -> StateSet.t
  val configurations_for_states : t -> ConfigurationSet.t StateMap.t
  val configurations_for_state : State.t -> t -> ConfigurationSet.t
  val configurations_for_state_nonmutate : State.t -> t -> ConfigurationSet.t
  val states_for_configurations : t -> StateSet.t ConfigurationMap.t
  val states_for_configuration : Configuration.t -> t -> StateSet.t
  val state_parents : State.t -> t -> ConfigurationSet.t
  val add_final_state : State.t -> t -> unit
  val remove_final_state : State.t -> t -> unit
  val add_final_states : StateSet.t -> t -> unit
  val set_final_states : StateSet.t -> t -> unit
  val add_transition : Configuration.t -> State.t -> t -> unit
  val remove_transition : Configuration.t -> State.t -> t -> unit
end

module type S = sig
  include BASE
  module Binding : sig
    type t = State.t option
    val product : t -> t -> t option
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val hash : t -> int
    val print : t -> Format.formatter -> unit
  end
  module SymSet : Set.S with type elt = Sym.t
  module BoundTerm : TypedTerm.S with type Sym.t = Sym.t and type Type.t = Binding.t
  module BoundConfiguration : TypedPattern.S with type Sym.t = Sym.t and type Var.t = Var.t and type Type.t = Binding.t
  type transition = Configuration.t * State.t
  val alphabet: t -> SymSet.t
  val states : t -> StateSet.t
  val is_final : t -> State.t -> bool
  val state_count : t -> int
  val is_state_empty : State.t -> t -> bool
  val configurations_for_state : State.t -> t -> ConfigurationSet.t
  val fold_configurations_for_binding : (Configuration.t -> State.t -> 'a -> 'a) -> Binding.t -> t -> 'a -> 'a
  val iter_configurations_for_binding : (Configuration.t -> State.t -> unit) -> Binding.t -> t -> unit
  val fold_configurations_for_epsilon_state : (Configuration.t -> 'a -> 'a) -> State.t -> t -> 'a -> 'a
  val iter_configurations_for_epsilon_state : (Configuration.t -> unit) -> State.t -> t -> unit
  val fold_epsilon_class : (State.t -> 'a -> 'a) -> State.t -> t -> 'a -> 'a
  val state_transitive_parents : State.t -> t -> ConfigurationSet.t
  val sub_automaton : StateSet.t -> t -> t
  val mem : Configuration.t -> State.t -> t -> bool
  val mem_configuration : Configuration.t -> t -> bool
  val mem_state : State.t -> t -> bool
  val type_term_in : State.t -> Sym.t Term.term -> t -> BoundTerm.t option
  val type_term : Sym.t Term.term -> t -> BoundTerm.t option
  val recognizes_in : State.t -> Sym.t Term.term -> t -> bool
  val recognizes : Sym.t Term.term -> t -> bool
  val recognizes_state_in : State.t -> State.t -> t -> bool
  val pick_binding_inhabitant : ?epsilon:bool -> Binding.t -> t -> BoundTerm.t
  val pick_binding_inhabitant_opt : ?epsilon:bool -> Binding.t -> t -> BoundTerm.t option
  val pick_term : ?smallest:bool -> ?epsilon:bool -> t -> BoundTerm.t
  val pick_term_opt : ?smallest:bool -> ?epsilon:bool -> t -> BoundTerm.t option
  val pick_term_in : ?epsilon:bool -> State.t -> t -> BoundTerm.t
  val pick_term_in_opt : ?epsilon:bool -> State.t -> t -> BoundTerm.t option
  val map : ?filter:(Configuration.t -> State.t -> t -> bool) -> (State.t -> State.t) -> t -> t
  val filter : (Configuration.t -> State.t -> bool) -> t -> t
  val fold_states : bool -> (State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val fold_transitions : (Configuration.t -> State.t -> 'a -> 'a) -> t -> 'a -> 'a
  val label : ((State.t -> 'a) -> State.t -> 'a) -> (State.t -> 'a) -> t -> (State.t -> 'a)
  val inter : Sym.t list -> t -> t -> t
  val reachable_states : ?epsilon:bool -> t -> StateSet.t
  val reachable_values : t -> BoundTerm.t StateMap.t
  val reduce : ?epsilon:bool -> ?from_finals:bool -> t -> t
  val unepsilon : t -> t
  val prune_useless : t -> t
  type renaming = State.t StateMap.t
  type normalizer = Sym.t -> State.t list -> State.t
  val print : t -> Format.formatter -> unit
  module Patterns (Var : Pattern.VARIABLE) : sig
    type pattern = (Sym.t, Var.t) Pattern.pattern
    val recognizes_pattern_in : State.t -> pattern -> t -> bool
    val configuration_of_pattern : (Var.t -> State.t) -> pattern -> Configuration.t
  end
  type dynamic_filter =
    | NoFilter
    | Filter of (State.t -> (bool * dynamic_filter))
end

(** Find or creates an element in a Hastbl.
    e is the key. If no element is mapped to e,
    (f e) is mapped to it and retuned. *)
let find_or_create f map e =
  match Hashtbl.find_opt map e with
  | Some x -> x
  | None ->
    let x = f e in
    Hashtbl.add map e x;
    x

module MakeBase (F : Symbol.S) (Q : STATE) = struct
  module Sym =
  struct
    include F

    let pp x y = print y x
    let show = MyStdLib.show_of_pp pp
  end
  module State =
  struct
    include Q

    let pp x y = print y x
    let show = MyStdLib.show_of_pp pp
  end

  module Configuration =
  struct
    open MyStdLib
    type t_node = Sym.t * State.t list
    [@@deriving hash, eq, ord, show]

    type t = t_node (*hash_consed*)
    [@@deriving hash, eq, ord, show]

    (*let table = HashConsTable.create 1000*)

    let create
        (node:t_node)
      : t =
      (*HashConsTable.hashcons
        hash_t_node
        compare_t_node
        table*)
        node

    let node
        (v:t)
      : t_node =
      v(*.node*)

    let product
        (c1:t)
        (c2:t)
      : t option =
      if equal c1 c2 then
        Some c1
      else
        let (i1,ss1) = node c1 in
        let (i2,ss2) = node c2 in
        if Sym.equal i1 i2 then
          begin match MyStdLib.distribute_option (List.map2_exn ~f:State.product ss1 ss2) with
            | None -> None
            | Some ss -> Some (create (i1,ss))
          end
        else
          None
  end

  module StateP = struct
    include State

    let pp x y = print y x
    let show = MyStdLib.show_of_pp pp
  end

  module StateSet = MyStdLib.HashSet.HSWrapper (StateP)
  module StateMap = MyStdLib.HashTable.Make(StateP)

  module ConfigurationSet = MyStdLib.HashSet.HSWrapper (Configuration)
  module ConfigurationMap = MyStdLib.HashTable.Make (Configuration)

  type t = {
    mutable roots : StateSet.t; (* Final states. *)
    state_confs : ConfigurationSet.t StateMap.t; (* Associates to each state the set of configurations leading to it. *)
    conf_states : StateSet.t ConfigurationMap.t; (* Associates to each configuration the set of states to go to. *)
    state_parents : ConfigurationSet.t StateMap.t (* Associates to each state the set of configurations it appears in. *)
  }

  type data = unit

  let empty () = {
    roots = (StateSet.empty ());
    state_confs = StateMap.empty ();
    conf_states = ConfigurationMap.create 50;
    state_parents = StateMap.empty () ;
  }

  let create _ = empty ()

  let data _ = ()

  let clear _ = empty ()

  let copy x =
    let state_confs = StateMap.empty () in
    StateMap.iter
      (fun k cs ->
         if not (ConfigurationSet.is_empty cs) then
           StateMap.add k (ConfigurationSet.copy cs) state_confs)
      x.state_confs;
    let conf_states = ConfigurationMap.empty () in
    ConfigurationMap.iter
      (fun k ss ->
         if not (StateSet.is_empty ss) then
           ConfigurationMap.add k (StateSet.copy ss) conf_states)
      x.conf_states;
    let state_parents = StateMap.empty () in
    StateMap.iter
      (fun k cs ->
         if not (ConfigurationSet.is_empty cs) then
           StateMap.add k (ConfigurationSet.copy cs) state_parents)
      x.state_parents;
    {
      roots = StateSet.copy x.roots ;
      state_confs = state_confs ;
      conf_states = conf_states ;
      state_parents = state_parents ;
    }

  let final_states a = a.roots

  let configurations_for_states a =
    a.state_confs

  let states_for_configurations a =
    a.conf_states

  let state_parents q a =
    StateMap.find_or_add
      q
      (fun () -> (ConfigurationSet.empty ()))
      a.state_parents

  let add_final_state q a =
    StateSet.add q a.roots

  let remove_final_state q a =
    StateSet.remove q a.roots

  let add_final_states set a =
    StateSet.iter
      (fun e -> StateSet.add e a.roots)
      set

  let set_final_states set a =
    a.roots <- set

  type hook = Configuration.t -> State.t -> unit

  let configurations_for_state q a =
    StateMap.find_or_add
      q
      (fun _ -> ConfigurationSet.empty ())
      a.state_confs

  let configurations_for_state_nonmutate q a =
    begin match StateMap.find_opt q a.state_confs with
      | None -> ConfigurationSet.create 0
      | Some cs -> cs
    end

  let states_for_configuration conf a =
    ConfigurationMap.find_or_add
      conf
      (fun _ -> StateSet.empty ())
      a.conf_states

  let add_transition (conf) q (a:t) =
    let add_parent_to q =
      let cs = state_parents q a in
      ConfigurationSet.add
        conf
        cs;
    in
    ConfigurationSet.add (conf) (configurations_for_state q a);
    StateSet.add q (states_for_configuration conf a);
    List.iter add_parent_to (snd (Configuration.node conf))

  let remove_transition (conf) q (a:t) =
    let remove_parent_from q =
      let cs = (state_parents q a) in
      (ConfigurationSet.remove conf cs);
    in
    ConfigurationSet.remove conf (configurations_for_state q a);
    let sc = states_for_configuration conf a in
    StateSet.remove q sc;
    if StateSet.is_empty sc then
      List.iter remove_parent_from (snd (Configuration.node conf))
    else
      ()
end

module Extend (B: BASE) = struct
  include B

  type transition = Configuration.t * State.t

  module Option = struct
    let product f a b =
      match a, b with
      | Some a, Some b ->
        begin match f a b with
          | Some p -> Some (Some p)
          | None -> None
        end
      | None, None -> Some None
      | Some a, _ -> Some (Some a)
      | _, Some b -> Some (Some b)

    let compare f a b =
      match a, b with
      | Some a, Some b -> f a b
      | Some _, None -> 1
      | None, Some _ -> -1
      | None, None -> 0

    let equal f a b =
      match a, b with
      | Some a, Some b -> f a b
      | None, None -> true
      | _, _ -> false

    let hash f = function
      | Some lq -> f lq
      | None -> 0

    let print f t out =
      match t with
      | Some lq -> f lq out
      | None -> Format.fprintf out "~"
  end

  module Binding = struct
    let hash_fold_option = MyStdLib.hash_fold_option
    type t = State.t option
    [@@deriving hash]

    let product qa qb =
      match Option.product State.product qa qb with
      | Some q -> Some (q)
      | _ -> None

    let compare qa qb =
      Option.compare State.compare qa qb

    let equal qa qb =
      Option.equal State.equal qa qb

    let hash (q : t) = Option.hash State.hash q

    let print q out =
      Format.fprintf out ":%t" (Option.print State.print q)
  end

  module SymSet = Set.Make (Sym)

  module BoundTerm = TypedTerm.Make (Sym) (Binding)
  module BoundConfiguration = TypedPattern.Make (Sym) (Var) (Binding)

  let is_state_empty q a =
    let confs = configurations_for_state q a in
    ConfigurationSet.is_empty confs

  let fold_transitions f a x =
    let fold_state_confs q confs x =
      let fold_labeled_confs conf = f conf q in
      ConfigurationSet.fold (fold_labeled_confs) confs x
    in
    StateMap.fold (fold_state_confs) (configurations_for_states a) x

  let fold_states f a x =
    let table = Hashtbl.create 8 in
    let uniq_f q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        f q x
    in
    let rec fold_state q x =
      match Hashtbl.find_opt table q with
      | Some () -> x
      | None ->
        Hashtbl.add table q ();
        ConfigurationSet.fold (fold_configuration) (configurations_for_state_nonmutate q a) (f q x)
    and fold_configuration conf x =
      let (_,ss) = Configuration.node conf in
      List.fold_right fold_state ss x
    and fold_transition conf q x =
      fold_configuration conf (uniq_f q x)
    in
    let x = StateSet.fold (uniq_f) (final_states a) x in
    fold_transitions (fold_transition) a x

  let states a =
    let ss = StateSet.empty () in
    fold_states (fun x () -> StateSet.add x ss) a ();
    ss

  let is_final a q =
    StateSet.contains q (final_states a)

  let state_count a =
    fold_states (fun _ k -> k + 1) a 0

  let mem conf label state a =
    let states = states_for_configuration conf a in
    StateSet.contains state states

  let mem_configuration conf a =
    begin match ConfigurationMap.find_opt conf (states_for_configurations a) with
      | Some _ -> true
      | None -> false
    end

  let mem_state q a =
    begin match StateMap.find_opt q (configurations_for_states a) with
      | None -> false
      | Some _ -> true
    end || StateSet.contains q (final_states a)

  let rec fold_configurations_for_binding func ty t x =
    match ty with
    | (Some q, label) ->
      let confs = configurations_for_state q t in
      let foreach_conf conf x =
          func conf q x
      in
      ConfigurationSet.fold foreach_conf confs x
    | (None, label) ->
      let foreach_state q x =
        fold_configurations_for_binding func (Some q, label) t x
      in
      fold_states foreach_state t x

  let iter_configurations_for_binding f ty t =
    fold_configurations_for_binding (fun c q () -> f c q) ty t ()

  let list_map_opt f l =
    let for_each_element e = function
      | Some acc ->
        begin
          match f e with
          | Some e -> Some (e::acc)
          | None -> None
        end
      | None -> None
    in
    List.fold_right for_each_element l (Some [])

  let rec list_map2_opt f l1 l2 =
    match l1, l2 with
    | [], [] -> Some []
    | e1::l1, e2::l2 ->
      begin
        match list_map2_opt f l1 l2 with
        | Some l ->
          begin
            match f e1 e2 with
            | Some e -> Some (e::l)
            | None -> None
          end
        | None -> None
      end
    | _, _ -> None

  let label f default _ = (* FIXME why is the automaton not used? *)
    let table = Hashtbl.create 8 in
    let rec label q : 'a =
      match Hashtbl.find_opt table q with
      | Some (Some v) -> v (* label is already computed *)
      | Some (None) -> default q (* label is being computed (cycle) *)
      | None -> (* label is not computed *)
        Hashtbl.add table q None;
        let v = f label q in
        Hashtbl.add table q (Some v);
        v
    in label

  type normalizer = Sym.t -> State.t list -> State.t

  let filter p t =
    let aut = empty () in
    let add conf q () =
      if p conf label q then
        add_transition conf q aut
      else
        ()
    in
    fold_transitions add t ();
    let add_final q =
      add_final_state q aut
    in
    StateSet.iter add_final (final_states t);
    aut


  let sub_automaton states t =
    let u = empty () in
    let visited = Hashtbl.create 8 in
    let rec visit_state q () =
      match Hashtbl.find_opt visited q with
      | Some () -> ()
      | None ->
        Hashtbl.add visited q ();
        let confs = configurations_for_state q t in
        let add_conf conf () =
          let u = add_transition conf q u in
          visit_conf conf u
        in
        ConfigurationSet.fold add_conf confs ()
    and visit_conf_internal conf () =
      match conf with
      | (_, l) ->
        List.fold_right visit_state l ()
    and visit_conf x u = visit_conf_internal (Configuration.node x) ()
    in
    (set_final_states states u);
    StateSet.fold visit_state states ();
    u

  let inter initials a b =
    let aut = empty () in
    let added_states = StateSet.empty () in
    (*let processed_configs = ConfigurationSet.empty () in*)
    let initial_configs =
      List.concat_map
        (fun t ->
           let config = Configuration.create (t,[]) in
           let full_ss =
             StateSet.fold2
               (fun a_state b_state ss -> (a_state,b_state)::ss)
               (states_for_configuration config a)
               (states_for_configuration config b)
               []
           in
           List.map
             (fun (a,b) -> (config,a,b))
             full_ss)
        initials
    in
    let add_configs
        (configs)
      : unit =
      let continuing = ref true in
      let configs_ref = ref configs in
      while !continuing do
        begin match !configs_ref with
          | [] -> continuing := false
          | (config,s1,s2)::t ->
            begin match State.product s1 s2 with
              | None ->
                configs_ref := t
              | Some s ->
                add_transition config s aut;
                if StateSet.contains s added_states then
                  configs_ref := t
                else
                  begin
                    StateSet.add s added_states;
                    let configs =
                      ConfigurationSet.fold2
                        (fun c1 c2 cs ->
                           begin match Configuration.product c1 c2 with
                             | None -> cs
                             | Some p -> (c1,c2,p)::cs
                           end)
                        (state_parents s1 a)
                        (state_parents s2 b)
                        []
                    in
                    let configs_output =
                      List.concat_map
                        (fun (c1,c2,c) ->
                           (*if ConfigurationSet.contains c processed_configs then
                             []
                             else*)
                           let (t,ss) = Configuration.node c in
                           if List.for_all
                               (fun s -> StateSet.contains s added_states)
                               ss
                           then
                             begin
                               (*ConfigurationSet.add c processed_configs;*)
                               StateSet.fold2
                                 (fun s1 s2 sps ->
                                    (c,s1,s2)::sps
                                 )
                                 (states_for_configuration c1 a)
                                 (states_for_configuration c2 b)
                                 []
                             end
                           else
                             [])
                        configs
                    in
                    configs_ref := configs_output@t;
                  end
            end
        end
      done;
    in
    let _ = add_configs initial_configs in
    StateSet.fold2
      (fun s1 s2 () ->
         begin match State.product s1 s2 with
           | None -> ()
           | Some s ->
             if StateSet.contains s added_states then
               add_final_state s aut
             else
               ()
         end)
      (final_states a)
      (final_states b)
      ();
    aut

  let reachable_states a =
    let visited = Hashtbl.create 8 in
    let reachable set c = StateSet.contains c set in
    let set = StateSet.empty () in
    let rec reach_conf conf set =
      reach_conf_states conf (states_for_configuration conf a) set
    and reach_conf_states conf lbl_states () =
      let (i,ss) = Configuration.node conf in
      let fold q () =
        match Hashtbl.find_opt visited q with
        | Some () -> ()
        | None ->
          Hashtbl.add visited q ();
          ConfigurationSet.fold (reach_conf) (state_parents q a) (StateSet.add q set)
      in
      if (List.for_all (reachable set) ss) then
        StateSet.fold (fold) lbl_states ()
      else ()
    in
    ConfigurationMap.fold (reach_conf_states) ((states_for_configurations a)) ();
    set

  let reduce ?(from_finals=true) t =
    let rt = empty () in
    let reachable_states = reachable_states t in
    let is_reachable_state q = StateSet.contains q reachable_states in
    let is_reachable_conf c =
      let (_,ss) = Configuration.node c in
      List.for_all is_reachable_state ss in
    let for_each_transition conf q () =
      if is_reachable_state q && is_reachable_conf conf then
        add_transition conf q rt
      else
        ()
    in
    fold_transitions for_each_transition t ();
    let for_each_final_state q () =
      if is_reachable_state q then
        add_final_state q rt
      else ()
    in
    (if from_finals then
      StateSet.fold for_each_final_state (final_states t) ()
    else
      fold_states for_each_final_state t ());
    rt

  (*let alphabet t =
    let rec fold_conf conf alphabet =
      match conf with
      | Configuration.Cons (f, l) ->
        List.fold_right fold_conf l (SymSet.add f alphabet)
      | Configuration.Var _ -> alphabet
    in
    let fold_transition conf _ alphabet =
      fold_conf (Configuration.node conf) alphabet
    in
    fold_transitions fold_transition t (SymSet.empty)*)


  let unepsilon _ =
    failwith "TODO: unepsilon: Not implemented yet."

  let prune_useless (x:t)
    : t =
    let x = reduce x in
    let fs = final_states x in
      let x = sub_automaton fs x in
    x

  let prune_useless_full (x:t)
    : t =
    let x = reduce x in
    let fs = final_states x in
    let x = sub_automaton fs x in
    x

  let prune_useless (x:t)
    : t =
    (*let x = reduce x in*)
    let fs = final_states x in
    let x = sub_automaton fs x in
    x

  type renaming = State.t StateMap.t

  exception Found of renaming

  let print t out =
    let print_state_confs q confs =
      let print_conf conf =
        Format.fprintf out "%t -> %t\n" (fun f -> Configuration.pp f conf) (State.print q)
      in
      ConfigurationSet.iter (print_conf) confs
    and print_state q =
      Format.fprintf out "%t " (State.print q)
    in
    Format.fprintf out "States ";
    StateSet.iter print_state (states t);
    Format.fprintf out "\n\nFinal States ";
    StateSet.iter print_state (final_states t);
    Format.fprintf out "\n\nTransitions\n";
    StateMap.iter print_state_confs (configurations_for_states t)

    (*let recognizes_pattern pattern t =
      StateSet.exists (function q -> recognizes_pattern_in q pattern t) (final_states t)*)
end

module Make (F : Symbol.S) (Q : STATE) = struct
  module Base = MakeBase (F) (Q)
  include Extend (Base)

  let empty = Base.empty

  let compare x y = 0
end

module MakeStateOption (Q : STATE) = struct
  type t = Q.t option

  let product q1 q2 =
    match q1, q2 with
    | Some q1, Some q2 ->
      if Q.compare q1 q2 = 0 then
        Some (Some q1)
      else
        None
    | Some q1, _ -> Some (Some q1)
    | _, Some q2 -> Some (Some q2)
    | _, _ -> Some None

  let compare q1 q2 =
    match q1, q2 with
    | Some q1, Some q2 -> Q.compare q1 q2
    | Some _, None -> 1
    | None, Some _ -> -1
    | None, None -> 0

  let equal q1 q2 =
    match q1, q2 with
    | Some q1, Some q2 -> Q.equal q1 q2
    | None, None -> true
    | _, _ -> false

  let hash = Hashtbl.hash

  let print t out =
    match t with
    | Some q ->
      (*				Format.pp_print_string ppf ":";*)
      Q.print q out
    | None ->
      Format.fprintf out "~"
end

module MakeStateProduct (A : STATE) (B : STATE) = struct
  type t = A.t * B.t

  let product (a1, b1) (a2, b2) =
    match A.product a1 a2, B.product b1 b2 with
    | Some a, Some b -> Some (a, b)
    | _, _ -> None

  let compare (a1, b1) (a2, b2) =
    let c = A.compare a1 a2 in
    if c = 0 then B.compare b1 b2 else c

  let equal (a1, b1) (a2, b2) =
    A.equal a1 a2 && B.equal b1 b2

  let hash (a, b) =
    (A.hash a) lxor (B.hash b)

  let print (a, b) out =
    Format.fprintf out "%t.%t" (A.print a) (B.print b)
end
