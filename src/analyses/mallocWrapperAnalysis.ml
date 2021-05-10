(** An analysis that handles the case when malloc is called from a wrapper function all over the code. *)

open Prelude.Ana
open Analyses
open GobConfig

module Spec : Analyses.MCPSpec =
struct
  include Analyses.DefaultSpec

  module PL = Lattice.Flat (CilType.Location) (struct
    let top_name = "Unknown line"
    let bot_name = "Unreachable line"
  end)

  let name () = "mallocWrapper"
  module D = PL
  module G = BoolDomain.MayBool
  module C = D

  module Q = Queries

  let wrappers = Hashtbl.create 13

  (* transfer functions *)
  let assign ctx (lval:lval) (rval:exp) : D.t =
    ctx.local

  let branch ctx (exp:exp) (tv:bool) : D.t =
    ctx.local

  let body ctx (f:fundec) : D.t =
    ctx.local

  let return ctx (exp:exp option) (f:fundec) : D.t =
    ctx.local

  let enter ctx (lval: lval option) (f:fundec) (args:exp list) : (D.t * D.t) list =
    let calleeofinterest = Hashtbl.mem wrappers f.svar.vname in
    let calleectx = if calleeofinterest then
       if ctx.local = `Top then
        `Lifted (Node.location ctx.node) (* if an interesting callee is called by an uninteresting caller, then we remember the callee context *)
        else ctx.local (* if an interesting callee is called by an interesting caller, then we remember the caller context *)
      else D.top () in  (* if an uninteresting callee is called, then we forget what was called before *)
    [(ctx.local, calleectx)]

  let combine ctx (lval:lval option) fexp (f:fundec) (args:exp list) fc (au:D.t) : D.t =
    ctx.local

  let special ctx (lval: lval option) (f:varinfo) (arglist:exp list) : D.t =
    ctx.local

  let startstate v = D.bot ()
  let threadenter ctx lval f args = [D.top ()]
  let threadspawn ctx lval f args fctx = ctx.local
  let exitstate  v = D.top ()

  type id_type = Sid of int | Vid of int
  let heap_hash = Hashtbl.create 113

  let get_heap_var sideg nodeId =
    (* Use existing varinfo instead of allocating a duplicate,
       which would be equal by determinism of create_var though. *)
    (* TODO: is this poor man's hashconsing? *)
    try Hashtbl.find heap_hash nodeId
    with Not_found ->
      let name = match nodeId with
        | Sid i -> "(alloc@" ^ "sid" ^ ":" ^ string_of_int i ^ ")"
        | Vid i -> "(alloc@" ^ "vid" ^ ":" ^ string_of_int i ^ ")" in
      let newvar = Goblintutil.create_var (makeGlobalVar name voidType) in
      Hashtbl.add heap_hash nodeId newvar;
      sideg newvar true;
      newvar

  let query (ctx: (D.t, G.t, C.t) ctx) (type a) (q: a Q.t): a Queries.result =
    match q with
    | Q.HeapVar ->
      let nodeId = (match ctx.node with
          | Statement s -> Sid s.sid
          | Function f -> Vid f.svar.vid
          | _ -> raise (Failure "A function entry node can never be the node after a malloc")) in
      `Lifted (get_heap_var ctx.sideg nodeId)
    | Q.IsHeapVar v ->
      ctx.global v
    | Q.IsMultiple v ->
      ctx.global v
    | _ -> Queries.Result.top q

    let init () =
      List.iter (fun wrapper -> Hashtbl.replace wrappers wrapper ()) (get_string_list "exp.malloc.wrappers");
      Hashtbl.clear heap_hash
end

let _ =
  MCP.register_analysis (module Spec : MCPSpec)
