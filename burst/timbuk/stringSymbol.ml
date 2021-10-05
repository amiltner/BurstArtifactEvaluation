module Id = struct
	type t = string

	let compare = String.compare
end

type t = {
	name : Id.t;
	arity : int
}

let create name arity = {
	name = name;
	arity = arity
}

let id f = f.name

let name = id

let arity f = f.arity

let compare f g =
	let c = String.compare f.name g.name in
	if c = 0 then f.arity - g.arity else c

let equal f g =
	f.arity = g.arity && String.equal f.name g.name

let hash f = Hashtbl.hash f

let print f out =
	Format.fprintf out "%s" f.name
