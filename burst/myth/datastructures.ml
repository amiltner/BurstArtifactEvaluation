open Core
open Util.Operators

(***** Lookup Table Infrastructure {{{ *****)

(* A simple dictionary interface that gets the job done for our purposes.           *)
module type Dictionary = sig
    type ('k, 'v) t
    val empty    : ('k -> 'k -> bool) -> ('k, 'v) t
    val is_empty : ('k, 'v) t -> bool
    val set      : 'k -> 'v -> ('k, 'v) t -> ('k, 'v) t
    val remove   : 'k -> ('k, 'v) t -> ('k, 'v) t
    val find     : 'k -> ('k, 'v) t -> 'v option
    val find_exn : 'k -> ('k, 'v) t -> 'v
    val keys     : ('k, 'v) t -> 'k list
    val vals     : ('k, 'v) t -> 'v list
    val map      : ('k -> 'v -> 'w)  -> ('k, 'v) t -> ('k, 'w) t
    val filter   : ('k -> 'v -> bool) -> ('k, 'v) t -> ('k, 'v) t
    val set_all  : ('k, 'v) t -> ('k, 'v) t -> ('k, 'v) t
end

(* A list-based implementation of a LookupTable.                                    *)
module ListDictionary : Dictionary = struct
    type ('k, 'v) t = { table : ('k * 'v) list
                      ; cmp   : ('k -> 'k -> bool)
                      }

    let empty cmp = { table = []; cmp = cmp }
    let is_empty g = match g.table with [] -> true | _ -> false
    
    let set key value g = 
      let rec try_update = function
        | [] -> None
        | (k, v) :: tl -> if g.cmp k key then Some ((key, value) :: tl)
                          else try_update tl >?> (fun ls -> Some ((k, v) :: ls))
      in
      match try_update g.table with
      | None    -> { g with table = (key, value) :: g.table }
      | Some ls -> { g with table = ls }

    let remove key g = 
      let rec remove_rec = function
        | [] -> failwith "remove: key not found"
        | (k, v) :: tl -> if g.cmp k key then tl else (k, v) :: remove_rec tl
      in
      { g with table = remove_rec g.table } 

    let find key g =
        let rec find_rec = function
          | [] -> None
          | (k, v) :: tl -> if g.cmp k key then Some v
                            else find_rec tl
        in
        find_rec g.table

    let find_exn key g = match find key g with
      | Some ans -> ans
      | None -> failwith "find_exn: key not found"

    let keys g = List.map ~f:(fun (k, _) -> k) g.table
    let vals g = List.map ~f:(fun (_, v) -> v) g.table

    let map    f g = { g with table = List.map    ~f:(fun (k, v) -> (k, f k v)) g.table }
    let filter f g = { g with table = List.filter ~f:(fun (k, v) -> f k v)      g.table }

    let set_all from g =
      List.fold_left ~f:(fun g (k, v) -> set k v g) ~init:g from.table
end

(***** }}} *****)

(***** Set datastructure derived from a lookup table {{{ *****)

module type Set_Sig = sig
    type 'k t
    val empty    : ('k -> 'k -> bool) -> 'k t
    val is_empty : 'k t -> bool
    val add      : 'k -> 'k t -> 'k t
    val remove   : 'k -> 'k t -> 'k t
    val has      : 'k -> 'k t -> bool
    val keys     : 'k t -> 'k list
    val filter   : ('k -> bool) -> 'k t -> 'k t
    val join     : 'k t -> 'k t -> 'k t
end

module SetOfDictionary (Dict : Dictionary) : Set_Sig = struct
    type 'k t = ('k, unit) Dict.t

    let empty    = Dict.empty
    let is_empty = Dict.is_empty
    let add k s  = Dict.set k () s
    let remove   = Dict.remove
    let has k s  = Option.is_some (Dict.find k s)
    let keys     = Dict.keys
    let join     = Dict.set_all

    let filter f s = Dict.filter (fun k _ -> f k) s
end

(***** }}} *****)
