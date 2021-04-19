(** An analyzer that takes the CFG from [MyCFG], a solver from [Selector], constraints from [Constraints] (using the specification from [MCP]) *)

open Prelude
open Cil
open MyCFG
open Analyses
open GobConfig
open Constraints

module type S2S = functor (X : Spec) -> Spec
(* gets Spec for current options *)
let get_spec () : (module SpecHC) =
  let open Batteries in
  (* apply functor F on module X if opt is true *)
  let lift opt (module F : S2S) (module X : Spec) = (module (val if opt then (module F (X)) else (module X) : Spec) : Spec) in
  let module S1 = (val
            (module MCP.MCP2 : Spec)
            |> lift (get_bool "exp.widen-context" && get_bool "exp.full-context") (module WidenContextLifter)
            |> lift (get_bool "exp.widen-context" && neg get_bool "exp.full-context") (module WidenContextLifterSide)
            (* hashcons before witness to reduce duplicates, because witness re-uses contexts in domain and requires tag for PathSensitive3 *)
            |> lift (get_bool "ana.opt.hashcons" || get_bool "ana.sv-comp.enabled") (module HashconsContextLifter)
            |> lift (get_bool "ana.sv-comp.enabled") (module HashconsLifter)
            |> lift (get_bool "ana.sv-comp.enabled") (module WitnessConstraints.PathSensitive3)
            |> lift (not (get_bool "ana.sv-comp.enabled")) (module PathSensitive2)
            |> lift true (module DeadCodeLifter)
            |> lift (get_bool "dbg.slice.on") (module LevelSliceLifter)
            |> lift (get_int "dbg.limit.widen" > 0) (module LimitLifter)
            |> lift (get_bool "ana.opt.equal" && not (get_bool "ana.opt.hashcons")) (module OptEqual)
          ) in
  (module (val if get_bool "ana.opt.hashcons" then (module HashconsLifter (S1)) else (module NoHashconsLifter (S1)) : SpecHC))

(** Given a [Cfg], computes the solution to [MCP.Path] *)
module AnalyzeCFG (Cfg:CfgBidir) =
struct

  (** The main function to preform the selected analyses. *)
  let analyze (file: file) (startfuns, exitfuns, otherfuns: Analyses.fundecs)  (module Spec : SpecHC) (increment: increment_data) =

    let module Inc = struct let increment = increment end in

    (* The Equation system *)
    let module EQSys = FromSpec (Spec) (Cfg) (Inc) in

    (* Hashtbl for locals *)
    let module LHT   = BatHashtbl.Make (EQSys.LVar) in
    (* Hashtbl for globals *)
    let module GHT   = BatHashtbl.Make (EQSys.GVar) in

    (* The solver *)
    let module Slvr  = Selector.Make (EQSys) (LHT) (GHT) in
    (* The verifyer *)
    let module Vrfyr = Verify2 (EQSys) (LHT) (GHT) in
    (* The comparator *)
    let module Comp = Compare (Spec) (EQSys) (LHT) (GHT) in

    (* Triple of the function, context, and the local value. *)
    let module RT = Analyses.ResultType2 (Spec) in
    (* Set of triples [RT] *)
    let module LT = SetDomain.HeadlessSet (RT) in
    (* Analysis result structure---a hashtable from program points to [LT] *)
    let module Result = Analyses.Result (LT) (struct let result_name = "analysis" end) in

    (* SV-COMP and witness generation *)
    let module WResult = Witness.Result (Cfg) (Spec) (EQSys) (LHT) (GHT) in

    (* print out information about dead code *)
    let print_dead_code (xs:Result.t) =
      let dead_locations : unit Deadcode.Locmap.t = Deadcode.Locmap.create 10 in
      let module NH = Hashtbl.Make (MyCFG.Node) in
      let live_nodes : unit NH.t = NH.create 10 in
      let count = ref 0 in
      let module StringMap = BatMap.Make (String) in
      let open BatPrintf in
      let live_lines = ref StringMap.empty in
      let dead_lines = ref StringMap.empty in
      let add_one (l,n,f) v =
        let add_fun  = BatISet.add l.line in
        let add_file = StringMap.modify_def BatISet.empty f.svar.vname add_fun in
        let is_dead = LT.for_all (fun (_,x,f) -> Spec.D.is_bot x) v in
        if is_dead then (
          dead_lines := StringMap.modify_def StringMap.empty l.file add_file !dead_lines;
          Deadcode.Locmap.add dead_locations l ();
        ) else (
          live_lines := StringMap.modify_def StringMap.empty l.file add_file !live_lines;
          NH.add live_nodes n ()
        );
      in
      Result.iter add_one xs;
      let live file fn =
        try StringMap.find fn (StringMap.find file !live_lines)
        with Not_found -> BatISet.empty
      in
      dead_lines := StringMap.mapi (fun fi -> StringMap.mapi (fun fu ded -> BatISet.diff ded (live fi fu))) !dead_lines;
      dead_lines := StringMap.map (StringMap.filter (fun _ x -> not (BatISet.is_empty x))) !dead_lines;
      dead_lines := StringMap.filter (fun _ x -> not (StringMap.is_empty x)) !dead_lines;
      let print_func f xs =
        let one_range b e first =
          count := !count + (e - b + 1);
          if not first then printf ", ";
          if b=e then
            printf "%d" b
          else
            printf "%d..%d" b e;
          false
        in
        printf "  function '%s' has dead code on lines: " f;
        ignore (BatISet.fold_range one_range xs true);
        printf "\n"
      in
      let print_file f =
        printf "File '%s':\n" f;
        StringMap.iter print_func
      in
      if get_bool "dbg.print_dead_code" then (
        if StringMap.is_empty !dead_lines
        then printf "No lines with dead code found by solver (there might still be dead code removed by CIL).\n" (* TODO https://github.com/goblint/analyzer/issues/94 *)
        else (
          StringMap.iter print_file !dead_lines;
          printf "Found dead code on %d line%s!\n" !count (if !count>1 then "s" else "")
        )
      );
      let str = function true -> "then" | false -> "else" in
      let report tv (loc, dead) =
        if Deadcode.Locmap.mem dead_locations loc then
          match dead, Deadcode.Locmap.find_option Deadcode.dead_branches_cond loc with
          | true, Some exp -> ignore (Pretty.printf "Dead code: the %s branch over expression '%a' is dead! (%a)\n" (str tv) d_exp exp d_loc loc)
          | true, None     -> ignore (Pretty.printf "Dead code: an %s branch is dead! (%a)\n" (str tv) d_loc loc)
          | _ -> ()
      in
      if get_bool "dbg.print_dead_code" then (
        let by_fst (a,_) (b,_) = compare a b in
        Deadcode.Locmap.to_list Deadcode.dead_branches_then |> List.sort by_fst |> List.iter (report true) ;
        Deadcode.Locmap.to_list Deadcode.dead_branches_else |> List.sort by_fst |> List.iter (report false) ;
        Deadcode.Locmap.clear Deadcode.dead_branches_then;
        Deadcode.Locmap.clear Deadcode.dead_branches_else
      );
      NH.mem live_nodes
    in

    (* convert result that can be out-put *)
    let solver2source_result h : Result.t =
      (* processed result *)
      let res = Result.create 113 in

      (* Adding the state at each system variable to the final result *)
      let add_local_var (n,es) state =
        let loc = Tracing.getLoc n in
        if loc <> locUnknown then try
            let (_,_, fundec) as p = loc, n, MyCFG.getFun n in
            if Result.mem res p then
              (* If this source location has been added before, we look it up
               * and add another node to it information to it. *)
              let prev = Result.find res p in
              Result.replace res p (LT.add (es,state,fundec) prev)
            else
              Result.add res p (LT.singleton (es,state,fundec))
          (* If the function is not defined, and yet has been included to the
           * analysis result, we generate a warning. *)
          with Not_found ->
            Messages.warn ("Calculated state for undefined function: unexpected node "^Ana.sprint MyCFG.pretty_node n)
      in
      LHT.iter add_local_var h;
      res
    in

    (* exctract global xml from result *)
    let make_global_fast_xml f g =
      let open Printf in
      let print_globals k v =
        fprintf f "\n<glob><key>%s</key>%a</glob>" (Goblintutil.escape (Basetype.Variables.short 800 k)) Spec.G.printXml v;
      in
      GHT.iter print_globals g
    in

    (* add extern variables to local state *)
    let do_extern_inits ctx (file : file) : Spec.D.t =
      let module VS = Set.Make (Basetype.Variables) in
      let add_glob s = function
          GVar (v,_,_) -> VS.add v s
        | _            -> s
      in
      let vars = foldGlobals file add_glob VS.empty in
      let set_bad v st =
        Spec.assign {ctx with local = st} (var v) MyCFG.unknown_exp
      in
      let add_externs s = function
        | GVarDecl (v,_) when not (VS.mem v vars || isFunctionType v.vtype) -> set_bad v s
        | _ -> s
      in
      foldGlobals file add_externs (Spec.startstate MyCFG.dummy_func.svar)
    in

    (* analyze cil's global-inits function to get a starting state *)
    let do_global_inits (file: file) : Spec.D.t * fundec list * (varinfo * Spec.G.t) list =
      (* Simulate globals before analysis. *)
      (* TODO: make extern/global inits part of constraint system so all of this would be unnecessary. *)
      let gh = GHT.create 13 in
      let getg v = GHT.find_default gh v (Spec.G.bot ()) in
      let sideg v d = GHT.replace gh v (Spec.G.join (getg v) d) in
      (* Old-style global function for context.
       * This indirectly prevents global initializers from depending on each others' global side effects, which would require proper solving. *)
      let getg v = Spec.G.bot () in
      let ctx =
        { ask     = (fun _ -> Queries.Result.top ())
        ; node    = MyCFG.dummy_node
        ; prev_node = MyCFG.dummy_node
        ; control_context = Obj.repr (fun () -> ctx_failwith "Global initializers have no context.")
        ; context = (fun () -> ctx_failwith "Global initializers have no context.")
        ; edge    = MyCFG.Skip
        ; local   = Spec.D.top ()
        ; global  = getg
        ; presub  = []
        ; postsub = []
        ; spawn   = (fun _ -> failwith "Global initializers should never spawn threads. What is going on?")
        ; split   = (fun _ -> failwith "Global initializers trying to split paths.")
        ; sideg   = sideg
        ; assign  = (fun ?name _ -> failwith "Global initializers trying to assign.")
        }
      in
      let edges = MyCFG.getGlobalInits file in
      if (get_bool "dbg.verbose") then print_endline ("Executing "^string_of_int (List.length edges)^" assigns.");
      let funs = ref [] in
      (*let count = ref 0 in*)
      let transfer_func (st : Spec.D.t) (edge, loc) : Spec.D.t =
        if M.tracing then M.trace "con" "Initializer %a\n" d_loc loc;
        (*incr count;
          if (get_bool "dbg.verbose")&& (!count mod 1000 = 0)  then Printf.printf "%d %!" !count;    *)
        Tracing.current_loc := loc;
        match edge with
        | MyCFG.Entry func        ->
          if M.tracing then M.trace "global_inits" "Entry %a\n" d_lval (var func.svar);
          Spec.body {ctx with local = st} func
        | MyCFG.Assign (lval,exp) ->
          if M.tracing then M.trace "global_inits" "Assign %a = %a\n" d_lval lval d_exp exp;
          (match lval, exp with
            | (Var v,o), (AddrOf (Var f,NoOffset))
              when v.vstorage <> Static && isFunctionType f.vtype ->
              (try funs := Cilfacade.getdec f :: !funs with Not_found -> ())
            | _ -> ()
          );
          Spec.assign {ctx with local = st} lval exp
        | _                       -> failwith "Unsupported global initializer edge"
      in
      let with_externs = do_extern_inits ctx file in
      (*if (get_bool "dbg.verbose") then Printf.printf "Number of init. edges : %d\nWorking:" (List.length edges);    *)
      let result : Spec.D.t = List.fold_left transfer_func with_externs edges in
      result, !funs, GHT.to_list gh
    in

    let print_globals glob =
      let out = M.get_out (Spec.name ()) !GU.out in
      let print_one v st =
        ignore (Pretty.fprintf out "%a -> %a\n" EQSys.GVar.pretty_trace v Spec.G.pretty st)
      in
      GHT.iter print_one glob
    in

    (* real beginning of the [analyze] function *)
    if get_bool "ana.sv-comp.enabled" then
      WResult.init file; (* TODO: move this out of analyze_loop *)

    GU.global_initialization := true;
    GU.earlyglobs := false;
    Spec.init ();
    Access.init file;

    let test_domain (module D: Lattice.S): unit =
      let module DP = DomainProperties.All (D) in
      ignore (Pretty.printf "domain testing...: %s\n" (D.name ()));
      let errcode = QCheck_runner.run_tests DP.tests in
      if (errcode <> 0) then
        failwith "domain tests failed"
    in
    let _ =
      if (get_bool "dbg.test.domain") then (
        ignore (Pretty.printf "domain testing analysis...: %s\n" (Spec.name ()));
        test_domain (module Spec.D);
        test_domain (module Spec.G);
      )
    in

    let startstate, more_funs, entrystates_global =
      if (get_bool "dbg.verbose") then print_endline ("Initializing "^string_of_int (MyCFG.numGlobals file)^" globals.");
      Stats.time "global_inits" do_global_inits file
    in

    let otherfuns = if get_bool "kernel" then otherfuns @ more_funs else otherfuns in

    let enter_with st fd =
      let st = st fd.svar in
      let ctx =
        { ask     = (fun _ -> Queries.Result.top ())
        ; node    = MyCFG.dummy_node
        ; prev_node = MyCFG.dummy_node
        ; control_context = Obj.repr (fun () -> ctx_failwith "enter_func has no context.")
        ; context = (fun () -> ctx_failwith "enter_func has no context.")
        ; edge    = MyCFG.Skip
        ; local   = st
        ; global  = (fun _ -> Spec.G.bot ())
        ; presub  = []
        ; postsub = []
        ; spawn   = (fun _ -> failwith "Bug1: Using enter_func for toplevel functions with 'otherstate'.")
        ; split   = (fun _ -> failwith "Bug2: Using enter_func for toplevel functions with 'otherstate'.")
        ; sideg   = (fun _ -> failwith "Bug3: Using enter_func for toplevel functions with 'otherstate'.")
        ; assign  = (fun ?name _ -> failwith "Bug4: Using enter_func for toplevel functions with 'otherstate'.")
        }
      in
      let args = List.map (fun x -> MyCFG.unknown_exp) fd.sformals in
      let ents = Spec.enter ctx None fd.svar args in
      List.map (fun (_,s) -> fd.svar, s) ents
    in

    (try MyCFG.dummy_func.svar.vdecl <- (List.hd otherfuns).svar.vdecl with Failure _ -> ());

    let startvars =
      if startfuns = []
      then [[MyCFG.dummy_func.svar, startstate]]
      else
        let morph f = Spec.morphstate f startstate in
        List.map (enter_with morph) startfuns
    in

    let exitvars = List.map (enter_with Spec.exitstate) exitfuns in
    let otherstate st v =
      let ctx =
        { ask     = (fun _ -> Queries.Result.top ())
        ; node    = MyCFG.dummy_node
        ; prev_node = MyCFG.dummy_node
        ; control_context = Obj.repr (fun () -> ctx_failwith "enter_func has no context.")
        ; context = (fun () -> ctx_failwith "enter_func has no context.")
        ; edge    = MyCFG.Skip
        ; local   = st
        ; global  = (fun _ -> Spec.G.bot ())
        ; presub  = []
        ; postsub = []
        ; spawn   = (fun _ -> failwith "Bug1: Using enter_func for toplevel functions with 'otherstate'.")
        ; split   = (fun _ -> failwith "Bug2: Using enter_func for toplevel functions with 'otherstate'.")
        ; sideg   = (fun _ -> failwith "Bug3: Using enter_func for toplevel functions with 'otherstate'.")
        ; assign  = (fun ?name _ -> failwith "Bug4: Using enter_func for toplevel functions with 'otherstate'.")
        }
      in
      Spec.threadenter ctx None v []
      (* TODO: do threadspawn to mainfuns? *)
    in
    let prestartstate = Spec.startstate MyCFG.dummy_func.svar in (* like in do_extern_inits *)
    let othervars = List.map (enter_with (otherstate prestartstate)) otherfuns in
    let startvars = List.concat (startvars @ exitvars @ othervars) in
    if startvars = [] then
      failwith "BUG: Empty set of start variables; may happen if enter_func of any analysis returns an empty list.";

    GU.earlyglobs := get_bool "exp.earlyglobs";
    GU.global_initialization := false;

    let startvars' =
      if get_bool "exp.forward" then
        List.map (fun (n,e) -> (MyCFG.FunctionEntry n, Spec.context e)) startvars
      else
        List.map (fun (n,e) -> (MyCFG.Function n, Spec.context e)) startvars
    in

    let entrystates = List.map (fun (n,e) -> (MyCFG.FunctionEntry n, Spec.context e), e) startvars in

    let solve_and_postprocess () =
      (* handle save_run/load_run *)
      let append_opt opt file = let o = get_string opt in if o = "" then "" else o ^ Filename.dir_sep ^ file in
      let solver_file = "solver.marshalled" in
      let save_run = append_opt "save_run" solver_file in
      let load_run = append_opt "load_run" solver_file in
      let compare_runs = get_string_list "compare_runs" in

      let lh, gh = if load_run <> "" then (
          if get_bool "dbg.verbose" then
            print_endline ("Loading the solver result of a saved run from " ^ load_run);
            let lh,gh = Serialize.unmarshal load_run in
            if get_bool "ana.opt.hashcons" then (
              let lh' = LHT.create (LHT.length lh) in
              let gh' = GHT.create (GHT.length gh) in
              LHT.iter (fun k v -> let k' = EQSys.LVar.relift k in let v' = EQSys.D.join (EQSys.D.bot ()) v in LHT.replace lh' k' v') lh;
              GHT.iter (fun k v -> let k' = EQSys.GVar.relift k in let v' = EQSys.G.join (EQSys.G.bot ()) v in GHT.replace gh' k' v') gh;
              lh', gh'
            ) else lh,gh
        ) else if compare_runs <> [] then (
          match compare_runs with
          | d1::d2::[] -> (* the directories of the runs *)
            if d1 = d2 then print_endline "Beware that you are comparing a run with itself! There should be no differences.";
            let r1, r2 = Tuple2.mapn (fun d -> Serialize.unmarshal (d ^ Filename.dir_sep ^ solver_file)) (d1, d2) in
            Comp.compare (d1, d2) r1 r2;
            r1 (* return the result of the first run for further options -- maybe better to exit early since compare_runs is its own mode. Only excluded verify below since it's on by default. *)
          | _ -> failwith "Currently only two runs can be compared!";
        ) else (
          if get_bool "dbg.verbose" then
            print_endline ("Solving the constraint system with " ^ get_string "solver" ^ ". Show stats with ctrl+c, quit with ctrl+\\.");
          if get_bool "dbg.earlywarn" then Goblintutil.should_warn := true;
          let lh, gh = Stats.time "solving" (Slvr.solve entrystates entrystates_global) startvars' in
          if save_run <> "" then (
            let config = append_opt "save_run" "config.json" in
            let meta = append_opt "save_run" "meta.json" in
            if get_bool "dbg.verbose" then (
              print_endline ("Saving the solver result to " ^ save_run ^ ", the current configuration to " ^ config ^ " and meta-data about this run to " ^ meta);
            );
            ignore @@ GU.create_dir (get_string "save_run"); (* ensure the directory exists *)
            Serialize.marshal (lh, gh) save_run;
            GobConfig.write_file config;
            let module Meta = struct
                type t = { command : string; timestamp : float; localtime : string } [@@deriving to_yojson]
                let json = to_yojson { command = GU.command; timestamp = Unix.time (); localtime = localtime () }
              end
            in
            (* Yojson.Safe.to_file meta Meta.json; *)
            Yojson.Safe.pretty_to_channel (Stdlib.open_out meta) Meta.json (* the above is compact, this is pretty-printed *)
          );
          lh, gh
        )
      in

      if get_string "comparesolver" <> "" then (
        let compare_with (module S2 :  GenericGlobSolver) =
          let module S2' = S2 (EQSys) (LHT) (GHT) in
          let r2 = S2'.solve entrystates entrystates_global startvars' in
          Comp.compare (get_string "solver", get_string "comparesolver") (lh,gh) (r2)
        in
        compare_with (Slvr.choose_solver (get_string "comparesolver"))
      );

      if get_bool "verify" && compare_runs = [] then (
        if (get_bool "dbg.verbose") then print_endline "Verifying the result.";
        Goblintutil.should_warn := true;
        Stats.time "verify" (Vrfyr.verify lh) gh;
      );

      if get_bool "ana.sv-comp.enabled" then (
        (* prune already here so local_xml and thus HTML are also pruned *)
        let module Reach = Reachability (EQSys) (LHT) (GHT) in
        Stats.time "reachability" (Reach.prune lh gh) startvars'
      );

      if get_bool "dbg.uncalled" then (
        let out = M.get_out "uncalled" Legacy.stdout in
        let insrt k _ s = match k with
          | (MyCFG.Function fn,_) -> if not (get_bool "exp.forward") then Set.Int.add fn.vid s else s
          | (MyCFG.FunctionEntry fn,_) -> if (get_bool "exp.forward") then Set.Int.add fn.vid s else s
          | _ -> s
        in
        (* set of ids of called functions *)
        let calledFuns = LHT.fold insrt lh Set.Int.empty in
        let is_bad_uncalled fn loc =
          not (Set.Int.mem fn.vid calledFuns) &&
          not (Str.last_chars loc.file 2 = ".h") &&
          not (LibraryFunctions.is_safe_uncalled fn.vname)
        in
        let print_uncalled = function
          | GFun (fn, loc) when is_bad_uncalled fn.svar loc->
              let msg = "Function \"" ^ fn.svar.vname ^ "\" will never be called." in
              ignore (Pretty.fprintf out "%s (%a)\n" msg Basetype.ProgLines.pretty loc)
          | _ -> ()
        in
        List.iter print_uncalled file.globals
      );

      (* check for dead code at the last state: *)
      let main_sol = try LHT.find lh (List.hd startvars') with Not_found -> Spec.D.bot () in
      if get_bool "dbg.debug" && Spec.D.is_bot main_sol then
        Printf.printf "NB! Execution does not reach the end of Main.\n";

      if get_bool "dump_globs" then
        print_globals gh;

      (* run activated transformations with the analysis result *)
      let active_transformations = get_list "trans.activated" |> List.map Json.string in
      (if List.length active_transformations > 0 then
        (* Transformations work using Cil visitors which use the location, so we join all contexts per location. *)
        let joined =
          let open Batteries in let open Enum in
          let e = LHT.enum lh |> map (Tuple2.map1 (MyCFG.getLoc % fst)) in (* drop context from key and get location from node *)
          let h = Hashtbl.create (if fast_count e then count e else 123) in
          iter (fun (k,v) ->
            (* join values for the same location *)
            let v' = try Spec.D.join (Hashtbl.find h k) v with Not_found -> v in
            Hashtbl.replace h k v') e;
          h
        in
        let ask loc =
          (* build a ctx for using the query system *)
          let rec ctx =
            { ask    = query
            ; node   = MyCFG.dummy_node (* TODO maybe ask should take a node (which could be used here) instead of a location *)
            ; prev_node = MyCFG.dummy_node
            ; control_context = Obj.repr (fun () -> ctx_failwith "No context in query context.")
            ; context = (fun () -> ctx_failwith "No context in query context.")
            ; edge    = MyCFG.Skip
            ; local  = Hashtbl.find joined loc
            ; global = GHT.find gh
            ; presub = []
            ; postsub= []
            ; spawn  = (fun v d    -> failwith "Cannot \"spawn\" in query context.")
            ; split  = (fun d e tv -> failwith "Cannot \"split\" in query context.")
            ; sideg  = (fun v g    -> failwith "Cannot \"split\" in query context.")
            ; assign = (fun ?name _ -> failwith "Cannot \"assign\" in query context.")
            }
          and query x = Spec.query ctx x in
          Spec.query ctx
        in
        List.iter (fun name -> Transform.run name ask file) active_transformations
      );

      lh, gh
    in

    MyCFG.write_cfgs := MyCFG.dead_code_cfg file (module Cfg:CfgBidir);

    (* Use "normal" constraint solving *)
    let lh, gh = Goblintutil.timeout solve_and_postprocess () (float_of_int (get_int "dbg.timeout"))
      (fun () -> Messages.waitWhat "Timeout reached!") in
    let local_xml = solver2source_result lh in

    let liveness =
      if get_bool "dbg.print_dead_code" then
        print_dead_code local_xml
      else
        fun _ -> true (* TODO: warn about conflicting options *)
    in

    if get_bool "ana.sv-comp.enabled" then
      WResult.write lh gh entrystates;

    if get_bool "exp.cfgdot" then
      MyCFG.dead_code_cfg file (module Cfg : CfgBidir) liveness;

    Spec.finalize ();

    if get_bool "dbg.verbose" && get_string "result" <> "none" then print_endline ("Generating output: " ^ get_string "result");
    Result.output (lazy local_xml) gh make_global_fast_xml file


  let analyze file fs change_info =
    analyze file fs (get_spec ()) change_info

  let rec analyze_loop file fs change_info =
    try
      analyze file fs change_info
    with Witness.RestartAnalysis ->
      analyze_loop file fs change_info
end

(** The main function to perform the selected analyses. *)
let analyze change_info (file: file) fs =
  if (get_bool "dbg.verbose") then print_endline "Generating the control flow graph.";
  let cfgF, cfgB = MyCFG.getCFG file in
  let cfgB' = function
    | MyCFG.Statement s as n -> ([get_stmtLoc s.skind,MyCFG.SelfLoop], n) :: cfgB n
    | n -> cfgB n
  in
  let cfgB = if (get_bool "ana.osek.intrpts") then cfgB' else cfgB in
  let module CFG = struct let prev = cfgB let next = cfgF end in
  let module A = AnalyzeCFG (CFG) in
  A.analyze_loop file fs change_info
