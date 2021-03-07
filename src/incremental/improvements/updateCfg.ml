open Cil
open Node
open CompareCFG
open Tracing

let store_node_location (n: node) (l: location): unit =
  NodeMap.add !location_map n l

type max_ids = {
  max_sid: int;
  max_vid: int;
}

let update_ids (old_file: file) (ids: max_ids) (new_file: file) (map: (global_identifier, Cil.global * VersionLookup.commitID) Hashtbl.t) (current_commit: string) (changes: change_info) =
  let vid_max = ref ids.max_vid in
  let sid_max = ref ids.max_sid in

  let update_vid_max vid =
    if vid > !vid_max then vid_max := vid
  in

  let update_sid_max sid =
    if sid > !sid_max then sid_max := sid
  in

  let make_vid () =
    vid_max := !vid_max +1;
    !vid_max
  in
  let make_sid () =
    sid_max := !sid_max +1;
    !sid_max
  in
  let override_fundec (target: fundec) (src: fundec) =
    target.sbody <- src.sbody;
    target.sallstmts <- src.sallstmts;
    target.sformals <- src.sformals;
    target.slocals <- src.slocals;
    target.smaxid <- src.smaxid;
    target.smaxstmtid <- src.smaxstmtid;
    target.svar <- src.svar;
  in
  let reset_fun (f: fundec) (old_f: fundec) =
    f.svar.vid <- old_f.svar.vid;
    List.iter (fun (l, o_l) -> l.vid <- o_l.vid) (List.combine f.slocals old_f.slocals);
    List.iter (fun (lo, o_f) -> lo.vid <- o_f.vid) (List.combine f.sformals old_f.sformals);
    List.iter (fun (s, o_s) -> s.sid <- o_s.sid) (List.combine f.sallstmts old_f.sallstmts);
    List.iter (fun s -> store_node_location (Statement s) (get_stmtLoc s.skind)) f.sallstmts;

    store_node_location (Function f.svar) f.svar.vdecl;
    store_node_location (FunctionEntry f.svar) f.svar.vdecl;
    override_fundec f old_f;
    List.iter (fun l -> update_vid_max l.vid) f.slocals;
    List.iter (fun f -> update_vid_max f.vid) f.sformals;
    List.iter (fun s -> update_sid_max s.sid) f.sallstmts;
    update_vid_max f.svar.vid;
  in
  let reset_var (v: varinfo) (old_v: varinfo)=
    v.vid <- old_v.vid;
    update_vid_max v.vid;
  in
  let reset_globals (glob: global) =
    try
      let (old_glob, commit) = Hashtbl.find map (CompareCFG.identifier_of_global glob) in
      match (glob, old_glob) with
      | GFun (nw, _), GFun (old, _) -> reset_fun nw old
      | GVar (nw, _, _), GVar (old, _, _) -> reset_var nw old
      | GVarDecl (nw, _), GVarDecl (old, _) -> reset_var nw old
      | _ -> ()
    with Failure m -> ()
  in
  let reset_unchanged_nodes (matches: (node * node) list) =
    let assign_same_id (old_n, n) = match old_n, n with
    | Statement old_s, Statement s -> s.sid <- old_s.sid; update_sid_max s.sid
    | FunctionEntry old_f, FunctionEntry f -> f.vid <- old_f.vid; update_vid_max f.vid
    | Function old_f, Function f -> f.vid <- old_f.vid; update_vid_max f.vid
    | _ -> raise (Failure "Node tuple falsely classified as unchanged nodes") in
    List.iter (fun (old_n, n) -> assign_same_id (old_n, n)) matches;
  in
  let reset_changed_stmts (changed: node list) =
    let assign_new_id n = match n with
      | Statement s -> s.sid <- make_sid ()
      (* function id is explicitly assigned in reset_changed_fun. Other than that there should be no other id generation
      through the Function node in the change set to avoid incorrect re-generation *)
      | FunctionEntry f -> ()
      | Function f -> () in
    List.iter (fun n -> assign_new_id n) changed;
  in
  let reset_changed_fun (f: fundec) (old_f: fundec) (diff: nodes_diff option) =
    match diff with
    | None -> (* None is returned if the function header changed and the cfg was not compared.
      In this case, preceed as before and renew all ids of the function. *)
      f.svar.vid <- old_f.svar.vid;
      update_vid_max f.svar.vid;
      List.iter (fun l -> l.vid <- make_vid ()) f.slocals;
      List.iter (fun f -> f.vid <- make_vid ()) f.sformals;
      List.iter (fun s -> s.sid <- make_sid ()) f.sallstmts;
    | Some d -> (* Some is returned only if the function header did not change and the cfg was compared.
      In this case, reset all ids of f, its locals, formals and unchanged nodes and renew all ids of the remaining nodes. *)
      f.svar.vid <- old_f.svar.vid;
      update_vid_max f.svar.vid;
      List.iter (fun (l, o_l) -> l.vid <- o_l.vid) (List.combine f.slocals old_f.slocals);
      List.iter (fun (lo, o_f) -> lo.vid <- o_f.vid) (List.combine f.sformals old_f.sformals);
      List.iter (fun l -> update_vid_max l.vid) f.slocals;
      List.iter (fun f -> update_vid_max f.vid) f.sformals;
      reset_unchanged_nodes d.unchangedNodes;
      reset_changed_stmts d.changedNodes
  in
  let reset_changed_globals (changed: changed_global) =
    match (changed.current, changed.old) with
    | GFun (nw, _), GFun (old, _) -> reset_changed_fun nw old changed.diff
    | _ -> ()
  in
  let update_fun (f: fundec) (old_f: fundec) =
    f.svar.vid <- make_vid ();
    List.iter (fun l -> l.vid <- make_vid ()) f.slocals;
    List.iter (fun f -> f.vid <- make_vid ()) f.sformals;
    List.iter (fun s -> s.sid <- make_sid ()) f.sallstmts;
  in
  let update_var (v: varinfo) (old_v: varinfo) =
    v.vid <- make_vid ()
  in
  let update_globals (glob: global) =
    try
      let (old_glob, commit) = Hashtbl.find map (CompareCFG.identifier_of_global glob) in
      if (String.equal commit current_commit) then (
        match (glob, old_glob) with
        | GFun (nw, _), GFun (old, _) -> update_fun nw old
        | GVar (nw, _, _), GVar (old, _, _) -> update_var nw old
        | GVarDecl (nw, _), GVarDecl (old, _) -> update_var nw old
        | _ -> ())
    with Failure m -> ()
  in
  let update_sids (glob: global) = match glob with
    | GFun (fn, loc) -> List.iter (fun s -> update_sid_max s.sid) fn.sallstmts
    | _ -> ()
  in

  let update_vids (glob: global) = match glob with
    | GFun (fn, loc) -> List.iter (List.iter (fun v -> update_vid_max v.vid)) [fn.slocals; fn.sformals]
    | GVar (v,_,_) -> update_vid_max v.vid
    | GVarDecl (v,_) -> update_vid_max v.vid
    | _ -> ()
  in
  let update_ids (glob: global) =
    update_vids glob; update_sids glob;
  in
  (* Update the sid_max based on the ids in the new file to avoid duplications that could otherwise occur because not 
  all node ids in a function are updated *)
  Cil.iterGlobals new_file update_sids;

  List.iter reset_globals changes.unchanged;
  List.iter reset_changed_globals changes.changed;
  List.iter update_globals changes.added;

  (* Update the sid_max and vid_max *)
  Cil.iterGlobals new_file update_ids;
  (* increment the sid so that the *unreachable* nodes that are introduced afterwards get unique sids *)
  while !sid_max > Cil.new_sid () do
    ()
  done;
  {max_sid = !sid_max; max_vid = !vid_max}