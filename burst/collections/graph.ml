module type BASE = sig
  type node

  module NodeSet : Set.S with type elt = node

  type t

  val empty : t

  val nodes : t -> NodeSet.t

  val successors : t -> node -> NodeSet.t

  val fold : (node -> node -> 'a -> 'a) -> t -> 'a -> 'a

  val add : node -> t -> t

  val connect : node -> node -> t -> t

  val scheduling : t -> node list
end

module type S = sig
  include BASE

  val components_graph : t -> (module BASE with type node = NodeSet.t and type t = 'a) -> 'a
end

module Make (Node : HashTable.HashedType) = struct
  type node = Node.t

  module NodeSet = Set.Make (Node)
  module NodeTable = HashTable.Make (Node)

  type t = {
    nodes: NodeSet.t;
    connections: (NodeSet.t * NodeSet.t) NodeTable.t
  }

  let empty =
    {
      nodes = NodeSet.empty;
      connections = NodeTable.create 8
    }

  let nodes t =
    t.nodes

  let successors t node =
    match NodeTable.find_opt node t.connections with
    | Some (_, succs) -> succs
    | None -> NodeSet.empty

  let predecessors t node =
    match NodeTable.find_opt node t.connections with
    | Some (preds, _) -> preds
    | None -> NodeSet.empty

  let fold (f : node -> node -> 'a -> 'a) (t : t) (x : 'a) : 'a =
    NodeTable.fold (
      fun node (_, succs) x ->
        NodeSet.fold (fun node' (x : 'a) -> f node node' x) succs x
    ) t.connections x

  let add node t =
    { t with nodes = NodeSet.add node t.nodes }

  let connect a b t =
    let t = add b (add a t) in
    let connections = NodeTable.set a (predecessors t a, NodeSet.add b (successors t a)) t.connections in
    let connections = NodeTable.set b (NodeSet.add a (predecessors t b), successors t b)   connections in
    { t with connections = connections }

  let scheduling t =
    let table = Hashtbl.create (NodeSet.cardinal t.nodes) in
    let rec add node scheduling : node list =
      match Hashtbl.find_opt table node with
      | Some () -> scheduling
      | None ->
        Hashtbl.add table node ();
        let preds : NodeSet.t = predecessors t node in
        let scheduling = NodeSet.fold add preds scheduling in
        node::scheduling
    in
    List.rev (NodeSet.fold add t.nodes [])

  type node_component_data = {
    mutable index: int;
    mutable low_link: int;
    mutable on_stack: bool
  }

  let components_graph (type cgraph) t (module ComponentsGraph : BASE with type node = NodeSet.t and type t = cgraph) : cgraph =
    let table = Hashtbl.create (NodeSet.cardinal t.nodes) in
    let stack = Stack.create () in
    let cgraph : ComponentsGraph.t ref = ref ComponentsGraph.empty in
    let component_table = Hashtbl.create 8 in
    let set_component node c = Hashtbl.add component_table node c in
    let component_of node = Hashtbl.find component_table node in
    let count = ref 0 in
    let next_index () =
      let index = !count in
      count := index + 1;
      index
    in
    let rec strong_connect node =
      match Hashtbl.find_opt table node with
      | Some node_data -> node_data
      | None ->
        Stack.push node stack;
        let index = next_index () in
        let node_data = { index = index; low_link = index; on_stack = true } in
        Hashtbl.add table node node_data;

        NodeSet.iter (
          function succ ->
          match Hashtbl.find_opt table succ with
          | None ->
            let succ_data = strong_connect succ in
            node_data.low_link <- min node_data.low_link succ_data.low_link
          | Some succ_data when succ_data.on_stack ->
            node_data.low_link <- min node_data.low_link succ_data.index
          | Some _ -> ()
        ) (successors t node);

        if node_data.low_link = node_data.index then begin
          let rec build_component component =
            let member = Stack.pop stack in
            let member_data = Hashtbl.find table member in
            member_data.on_stack <- false;
            let component = NodeSet.add member component in
            if Node.equal node member then component else build_component component
          in
          let component = build_component NodeSet.empty in
          NodeSet.iter (
            function node -> set_component node component
          ) component;
          cgraph := ComponentsGraph.add component !cgraph
        end;
        node_data
    in
    NodeSet.iter (function node -> ignore (strong_connect node)) t.nodes;
    fold (
      fun node node' (cgraph : ComponentsGraph.t) ->
        let c = component_of node in
        let c' = component_of node' in
        if NodeSet.equal c c' then cgraph else
          ComponentsGraph.connect c c' cgraph
    ) t (!cgraph : ComponentsGraph.t)
end
