module type CLASS = sig
  type t

  val equal: t -> t -> bool

  val union: t -> t -> t
end

module type S = sig
  type elt
  type repr
  type t
  type factory = elt -> repr
  val create: ?size:int -> unit -> t
  val find: ?default:factory -> elt -> t -> repr
  val find_opt: ?default:factory -> elt -> t -> repr option
  val union: ?default:factory -> ?hook:(repr -> repr -> unit) -> elt -> elt -> t -> t
end

module Make (Elt: HashTable.HashedType) (Class: CLASS) = struct
  type elt = Elt.t
	type repr = Class.t

  module HashTable = HashTable.Make (Elt)

  module Node = struct
    type t = {
      elt: elt;
      rank: int;
      parent: parent
    }

    and parent =
      | Parent of elt
      | Root of repr

    let create e k = {
      elt = e;
      rank = 0;
      parent = Root k
    }

    let set_parent p t = {
      t with parent = Parent p
    }

    let set_root k t = {
      t with parent = Root k
    }

    let incr t = {
      t with rank = t.rank + 1
    }
  end

  type factory = elt -> repr

  type t = {
    mutable table: Node.t HashTable.t
  }

  let create ?(size = 8) () = {
    table = HashTable.create size
  }

  let root_class r =
    match r.Node.parent with
    | Root k -> k
    | _ -> raise Not_found

  let node_find node t =
    let rec aux node table =
      match node.Node.parent with
      | Parent pnode ->
        let table, root = aux (HashTable.find pnode table) table in
        let table = HashTable.set node.Node.elt (Node.set_parent root.Node.elt node) table in
        table, root
      | Root _ -> table, node
    in
    let table, root = aux node t.table in
    t.table <- table;
    root

  let node_get default e t =
    match HashTable.find_opt e t.table with
    | Some node -> Some node
    | None ->
      begin
        match default with
        | Some f ->
          let node = Node.create e (f e) in
          t.table <- HashTable.set e node t.table;
          Some node
        | None -> None
      end

  let find_opt ?default e t =
    match node_get default e t with
    | Some node ->
      let root = node_find node t in
      Some (root_class root)
    | None -> None

  let find ?default e t =
    match find_opt ?default e t with
    | Some node -> node
    | None -> raise Not_found

  let union ?default ?hook a b t =
    (* get the nodes *)
    match node_get default a t, node_get default b t with
    | Some a, Some b ->
      begin
        (* get the roots *)
        let ra = node_find a t in
        let rb = node_find b t in
        (* get the classes *)
        let ca = root_class ra in
        let cb = root_class rb in
        (* merge the classes *)
        if not (Class.equal ca cb) then
          begin
            begin
              match hook with
              | Some f -> f ca cb
              | None -> ()
            end;
            let c = Class.union ca cb in
            let table =
              if ra.rank > rb.rank then
                let table = HashTable.set ra.Node.elt (Node.set_root c ra) t.table in
                HashTable.set rb.Node.elt (Node.set_parent ra.Node.elt rb) table
              else if ra.rank < rb.rank then
                let table = HashTable.set rb.Node.elt (Node.set_root c rb) t.table in
                HashTable.set ra.Node.elt (Node.set_parent rb.Node.elt ra) table
              else
                let table = HashTable.set ra.Node.elt (Node.set_root c (Node.incr ra)) t.table in
                HashTable.set rb.Node.elt (Node.set_parent ra.Node.elt rb) table
            in { table = table }
          end
        else
          t
      end
    | _, _ -> t
end
