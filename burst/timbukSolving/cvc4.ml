open Collections
open Async_unix

let log_src = Logs.Src.create "timbuk.solving.cvc4"
module Log = (val Logs.src_log log_src : Logs.LOG)

module type CONF = sig
  (* path to the CVC4 executable. *)
  val path : unit -> string

  val log : unit -> (string * out_channel) option
end

module Make (Conf : CONF) (Var : Solver.VARIABLE) = struct
  module Var = Var

  type const = string

  type atom =
    | Variable of Var.t
    | Constant of const

  type expr =
    | Eq of atom * atom
    | Neq of atom * atom
    | Or of expr list
    | And of expr list
    | Impl of expr * expr

  type owner = {
    proc: Process.t;
    vars: Var.t list;
    commands: Smt2.command list;
    consts: const list;
    log: (string * out_channel) option
  }

  type cvc4 =
    | Owner of owner
    | Past of {
        vars: Var.t list;
        commands: Smt2.command list;
        consts: const list
      }

  type t = cvc4 ref

  module Model = Map.Make (Var)

  type model = int Model.t

  type 'a result =
    | Sat of 'a
    | Unsat
    | Unknown (* when there is a timeout. *)

  type error =
    | UndefinedVariable of Var.t

  exception Error of error

  (* module Model = struct
     type t = model

     let size (n, _) = n

     let binding x (_, defs) =
      let rec find = function
        | [] -> raise (Error (UndefinedVariable x))
        | (y, i)::l -> if Var.equal x y then i else find l
      in
      find defs

     let fold f (_, defs) x =
      let g (v, i) x = f v i x in
      List.fold_right g defs x
     end *)
  let vars = function
    | Owner o -> o.vars
    | Past p -> p.vars

  let commands = function
    | Owner o -> o.commands
    | Past p -> p.commands

  let send log smt2 proc =
    begin match log with
      | Some (_, log) ->
        let out = Format.formatter_of_out_channel log in
        Smt2.print smt2 out;
        Format.pp_print_flush out ()
      | None -> ()
    end;
    let out = Writer.to_formatter (Process.stdin proc) in
    Smt2.print smt2 out;
    Format.pp_print_flush out ()
  (* ;
     Smt2.print smt2 stdout;
     flush stdout *)

  let create_process () =
    (* NODE the --finite-model-find is very important. It the one guarantying us to find the SMALLEST solution. *)
    Core.Or_error.ok_exn (Core.Option.value_exn (Async_unix__Import.Deferred.peek (Process.create ~prog:(Conf.path ()) ~args:["--incremental";"--finite-model-find";"--produce-model";"--lang=smtlib2"] ())))

  let create () =
    let proc = create_process () in
    let commands = [Smt2.SetLogic (Smt2.QF_UF); Smt2.DeclareSort ("Q", 0)] in
    let log = Conf.log () in
    send log commands proc;
    ref (Owner {
        proc = proc;
        vars = [];
        commands = commands;
        consts = [];
        log = log
      })

  let release t =
    match !t with
    | Owner o -> () (*ignore (Process.close o.proc)*)
    | _ -> ()

  let index_of v vars =
    let rec find i = function
      | [] -> None
      | x::l -> if Var.compare v x = 0 then Some i else find (i+1) l
    in
    find 0 vars

  let var_id v vars =
    match index_of v vars with
    | Some i -> "x"^(string_of_int i)
    | None -> raise (Error (UndefinedVariable v))

  let var_of_id id vars =
    if String.sub id 0 1 = "x" then
      let len = (String.length id)-1 in
      let i = int_of_string (String.sub id 1 len) in
      Some (List.nth vars i)
    else
      None

  let var_to_smt2 v vars =
    Smt2.Var (var_id v vars)

  let const_to_smt2 c =
    Smt2.Var c

  let own = function
    | Owner o -> o
    | Past p ->
      let proc = create_process () in
      let log = Conf.log () in
      send log p.commands proc;
      {
        proc = proc;
        vars = p.vars;
        commands = p.commands;
        consts = p.consts;
        log = log
      }

  let declared v vars =
    List.mem v vars

  let declare v t =
    let cvc4 = own !t in
    if declared v cvc4.vars then t else
      begin
        let vars = cvc4.vars @ [v] in
        let id = var_id v vars in
        begin match cvc4.log with
          | Some (_, log) ->
            let out = Format.formatter_of_out_channel log in
            Format.fprintf out "; %s: %t\n" id (Var.print v);
            Format.pp_print_flush out ()
          | None -> ()
        end;
        let cmd = Smt2.DeclareConst (id, Sort "Q") in
        (* let leq = Smt2.Assert (And [Geq (Smt2.Var id, Smt2.Const (IntConst 0)); (Leq (Smt2.Var id, Smt2.Var "n"))]) in *)
        let new_cmds = [cmd] in
        let commands = cvc4.commands @ new_cmds in
        send cvc4.log new_cmds cvc4.proc;
        let new_t = ref (Owner {
            proc = cvc4.proc;
            vars = vars;
            commands = commands;
            consts = cvc4.consts;
            log = cvc4.log
          })
        in
        t := Past {
            vars = cvc4.vars;
            commands = cvc4.commands;
            consts = cvc4.consts
          };
        new_t
      end

  let new_const t =
    let cvc4 = own !t in
    let c = "c" ^ (string_of_int (List.length cvc4.consts)) in
    let consts = c::cvc4.consts in
    let cmd = Smt2.DeclareFun (c, Sort "Q") in
    let new_cmds = cmd :: (List.fold_right (
        fun c' cmds ->
          let cmd = Smt2.Assert (Smt2.Neq (Smt2.Var c, Smt2.Var c')) in
          cmd::cmds
      ) cvc4.consts [])
    in
    send cvc4.log new_cmds cvc4.proc;
    let commands = cvc4.commands @ new_cmds in
    let new_t = ref (Owner {
        proc = cvc4.proc;
        vars = cvc4.vars;
        commands = commands;
        consts = consts;
        log = cvc4.log
      })
    in
    t := Past {
        vars = cvc4.vars;
        commands = cvc4.commands;
        consts = cvc4.consts
      };
    new_t, c

  let atom_to_smt2 vars = function
    | Variable x -> var_to_smt2 x vars
    | Constant c -> const_to_smt2 c

  let rec expr_to_smt2 vars = function
    | Eq (a, b) -> (Smt2.Eq (atom_to_smt2 vars a, atom_to_smt2 vars b))
    | Neq (a, b) -> (Smt2.Neq (atom_to_smt2 vars a, atom_to_smt2 vars b))
    | Or l -> Smt2.Or (List.map (expr_to_smt2 vars) l)
    | And l -> Smt2.And (List.map (expr_to_smt2 vars) l)
    | Impl (a, b) -> Smt2.Impl (expr_to_smt2 vars a, expr_to_smt2 vars b)

  let mem c t =
    let cvc4 = !t in
    let cmd = Smt2.Assert (expr_to_smt2 (vars cvc4) c) in
    List.mem cmd (commands cvc4)

  let add_cmd cmd t cvc4 =
    let commands = cvc4.commands @ [cmd] in
    send cvc4.log [cmd] cvc4.proc;
    let new_t = ref (Owner {
        proc = cvc4.proc;
        vars = cvc4.vars;
        commands = commands;
        consts = cvc4.consts;
        log = cvc4.log
      })
    in
    t := Past {
        vars = cvc4.vars;
        commands = cvc4.commands;
        consts = cvc4.consts
      };
    new_t

  let rec simplify = function
    | Or l ->
      begin
        let l = List.fold_right (
            fun e l ->
              match simplify e with
              | Some e -> e::l
              | None -> l
          ) l []
        in
        match l with
        | [] -> None
        | e::[] -> Some e
        | l -> Some (Or l)
      end
    | And l ->
      begin
        let l = List.fold_right (
            fun e l ->
              match simplify e with
              | Some e -> e::l
              | None -> l
          ) l []
        in
        match l with
        | [] -> None
        | e::[] -> Some e
        | l -> Some (And l)
      end
    | Impl (a, b) ->
      begin
        match simplify a, simplify b with
        | Some a, Some b -> Some (Impl (a, b))
        | None, Some b -> Some b
        | _ -> None
      end
    | e -> Some e

  let declare_atom t = function
    | Variable x -> declare x t
    | Constant _ -> t

  let rec declare_expr t = function
    | Eq (a, b) -> declare_atom (declare_atom t a) b
    | Neq (a, b) -> declare_atom (declare_atom t a) b
    | Or l -> List.fold_left declare_expr t l
    | And l -> List.fold_left declare_expr t l
    | Impl (a, b) -> declare_expr (declare_expr t a) b

  let add c t =
    match simplify c with
    | Some c ->
      let t = declare_expr t c in
      if mem c t then t else
        begin
          let cvc4 = own !t in
          let cmd = Smt2.Assert (expr_to_smt2 cvc4.vars c) in
          add_cmd cmd t cvc4
        end
    | None -> t

  let to_smt2 t =
    commands !t

  let parse_result lexbuf =
    Smt2Parser.result (Smt2Lexer.token) lexbuf

  let parse_model lexbuf =
    Smt2Parser.model (Smt2Lexer.token) lexbuf

  let model_of_smt2 m vars =
    (* Smt2.print m stderr;
       Format.pp_print_string ppf "extract.";
       Format.pp_force_newline ppf ();
       Format.pp_print_flush ppf (); *)
    let table = Hashtbl.create 8 in
    let int_value = function
      | Smt2.SortConst ("Q", value) ->
        begin
          match Hashtbl.find_opt table value with
          | Some i -> i
          | None ->
            let i = Hashtbl.length table in
            Hashtbl.add table value i;
            i
        end
      | _ -> failwith "ill-defined model: non-Q value"
    in
    let fold_command model = function
      | Smt2.DefineFun (id, const) ->
        (* Format.pp_print_string ppf "define: ";
           Format.pp_print_string ppf id;
           Format.pp_force_newline ppf ();
           Format.pp_print_flush ppf (); *)
        begin
          match var_of_id id vars with
          | Some x ->
            Model.add x (int_value const) model
          | None ->
            model
        end
      | _ ->
        model
    in
    List.fold_left fold_command Model.empty m

  let line_stream_of_channel channel =
    Stream.from
      (fun _ ->
         try Some (input_line channel) with End_of_file -> None);;

  let get_model ?(debug=false) t =
    let cvc4 = own !t in
    let out = Writer.to_formatter (Process.stdin cvc4.proc) in
    begin match cvc4.log with
      | Some (id, _) -> Log.debug (fun m -> m "CVC4 solving `%s`...@." id)
      | None -> () (* Log.debug (fun m -> m "CVC4 solving...@.") *)
    end;
    Smt2.print [Smt2.Check] out;
    Format.pp_print_flush out ();
    match parse_result (Lexing.from_string (Core.Option.value_exn (Async_unix__Import.Deferred.peek (Reader.contents (Process.stdout cvc4.proc))))) with
    | Smt2.Sat ->
      Smt2.print [Smt2.GetModel] out;
      Format.pp_print_flush out ();
      let model = parse_model (Lexing.from_string (Core.Option.value_exn (Async_unix__Import.Deferred.peek (Reader.contents (Process.stdout cvc4.proc))))) in
      Sat (model_of_smt2 model cvc4.vars)
    | Smt2.Unsat -> Unsat
    | Smt2.Unknown -> Unknown

  let solve ?(debug=false) t = get_model ~debug t

  let next t =
    match solve t with
    | Sat model ->
      let cvc4 = own !t in
      let constrain_variable x v l =
        let fold y w l =
          if x = y then l else
          if v = w then ((Smt2.Neq (var_to_smt2 x cvc4.vars, var_to_smt2 y cvc4.vars))::l)
          else ((Smt2.Eq (var_to_smt2 x cvc4.vars, var_to_smt2 y cvc4.vars))::l)
        in
        Model.fold fold model l
      in
      let l = (Model.fold constrain_variable model []) in
      if l = []
      then Unsat
      else
        let cmd = Smt2.Or l in
        Sat (add_cmd (Smt2.Assert cmd) t cvc4)
    | Unsat -> Unsat
    | Unknown -> Unknown

  let print t fmt =
    List.iteri (
      fun i x ->
        Format.fprintf fmt "; %d: %t\n" i (Var.print x);
    ) (vars !t);
    let smt2 = to_smt2 t in
    Smt2.print smt2 fmt
end
