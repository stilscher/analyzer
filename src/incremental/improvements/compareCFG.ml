open MyCFG
open Queue
open Defaults
open Cil
open Format

module StdS = Set.Make (
  struct
    let compare = compare
    type t = (node * node) * (edge list * edge list) * (node * node)
  end
)

module DiffS = Set.Make (
  struct
    let compare = compare
    type t = (node * node) * edge list * node 
  end  
)

module FunDiffMap = Map.Make(
  struct
    let compare = compare
    type t = node
  end
)

module NodeSet = Set.Make (
    struct
      let compare = compare
      type t = node
    end  
)

let waitingList : (node * node) t = Queue.create ()

let print_queue q = 
    let f (n1, n2) = printf "(%s,%s)\n" (Pretty.sprint 200 (pretty_node () n1)) (Pretty.sprint 200 (pretty_node () n2)) in 
  printf "queue: "; if Queue.is_empty q then printf "empty\n" else Queue.iter f q

let node_to_string n = Pretty.sprint 200 (pretty_node () n)
let edge_to_string e = Pretty.sprint 200 (pretty_edge () e)
let node_to_id_string n = 
  let id = match n with
    | Statement s -> s.sid
    | FunctionEntry f -> f.vid
    | Function f -> f.vid
    in string_of_int id

let print_std_set s = 
  let print_elem ((fromNode1, fromNode2), (edgeList1, edgeList2), (toNode1, toNode2)) = 
    printf "(%s, %s)\n" (node_to_string fromNode2) (node_to_string toNode2) in 
  printf "std set: "; if StdS.is_empty s then printf "empty\n" else StdS.iter print_elem s

let print_diff_set s =
  let print_elem ((fromNode1, fromNode2), edgeList2, toNode2) = 
    printf "((%s, %s), %s)\n" (node_to_string fromNode1) (node_to_string fromNode2) (node_to_string toNode2) in 
  printf "diff set: "; if DiffS.is_empty s then printf "empty\n" else DiffS.iter print_elem s

(* in contrast to the original eq_varinfo in CompareAST, this method also ignores vinline and vaddrof *)
let eq_varinfo' (a: varinfo) (b: varinfo) = a.vname = b.vname && CompareAST.eq_typ a.vtype b.vtype && CompareAST.eq_list CompareAST.eq_attribute a.vattr b.vattr &&
                                           a.vstorage = b.vstorage && a.vglob = b.vglob
(* Ignore the location, vid, vreferenced, vdescr, vdescrpure, vinline, vaddrof*)

let eq_instr' (a: instr) (b: instr) = match a, b with
  | Set (lv1, exp1, _l1), Set (lv2, exp2, _l2) -> CompareAST.eq_lval lv1 lv2 && CompareAST.eq_exp exp1 exp2
  | Call (Some lv1, f1, args1, _l1), Call (Some lv2, f2, args2, _l2) -> CompareAST.eq_lval lv1 lv2 && CompareAST.eq_exp f1 f2 && CompareAST.eq_list CompareAST.eq_exp args1 args2
  | Call (None, f1, args1, _l1), Call (None, f2, args2, _l2) -> CompareAST.eq_exp f1 f2 && CompareAST.eq_list CompareAST.eq_exp args1 args2
  | Asm (attr1, tmp1, ci1, dj1, rk1, l1), Asm (attr2, tmp2, ci2, dj2, rk2, l2) -> 
      CompareAST.eq_list String.equal tmp1 tmp2 && CompareAST.eq_list(fun (x1,y1,z1) (x2,y2,z2)-> x1 = x2 && y1 = y2 
      && CompareAST.eq_lval z1 z2) ci1 ci2 && CompareAST.eq_list(fun (x1,y1,z1) (x2,y2,z2)-> x1 = x2 && y1 = y2 
      && CompareAST.eq_exp z1 z2) dj1 dj2 && CompareAST.eq_list String.equal rk1 rk2(* ignore attributes and locations *)
  | VarDecl (v1, _l1), VarDecl (v2, _l2) -> eq_varinfo' v1 v2
  | _, _ -> false

(* in contrast to the similar method eq_stmtkind in CompareAST, 
this method does not compare the inner body, that is sub blocks,
of if and switch statements *)
let eq_stmtkind' ((a, af): stmtkind * fundec) ((b, bf): stmtkind * fundec) =
  let eq_block' = fun x y -> CompareAST.eq_block (x, af) (y, bf) in
  match a, b with
  | Instr is1, Instr is2 -> CompareAST.eq_list eq_instr' is1 is2
  | Return (Some exp1, _l1), Return (Some exp2, _l2) -> CompareAST.eq_exp exp1 exp2
  | Return (None, _l1), Return (None, _l2) -> true
  | Return _, Return _ -> false
  | Goto (st1, _l1), Goto (st2, _l2) -> CompareAST.eq_stmt_with_location (!st1, af) (!st2, bf)
  | Break _, Break _ -> true
  | Continue _, Continue _ -> true
  | If (exp1, then1, else1, _l1), If (exp2, then2, else2, _l2) -> 
      CompareAST.eq_exp exp1 exp2 (* && eq_block' then1 then2 && eq_block' else1 else2 *)
  | Switch (exp1, block1, stmts1, _l1), Switch (exp2, block2, stmts2, _l2) -> 
      CompareAST.eq_exp exp1 exp2 (* && eq_block' block1 block2 && CompareAST.eq_list (fun a b -> eq_stmt (a,af) (b,bf)) stmts1 stmts2 *)
  | Loop (block1, _l1, _con1, _br1), Loop (block2, _l2, _con2, _br2) -> true (* eq_block' block1 block2 *)
  | Block block1, Block block2 -> eq_block' block1 block2
  | TryFinally (tryBlock1, finallyBlock1, _l1), TryFinally (tryBlock2, finallyBlock2, _l2) -> assert false
      (* eq_block' tryBlock1 tryBlock2 && eq_block' finallyBlock1 finallyBlock2 *)
  | TryExcept (tryBlock1, exn1, exceptBlock1, _l1), TryExcept (tryBlock2, exn2, exceptBlock2, _l2) -> assert false
      (* eq_block' tryBlock1 tryBlock2 && eq_block' exceptBlock1 exceptBlock2 *)
  | _, _ -> false

let eq_stmt' ((a, af): stmt * fundec) ((b, bf): stmt * fundec) =
  (* catch Invalid Argument exception which is thrown by List.combine
  if the label lists are of different length *)
  try List.for_all (fun (x,y) -> CompareAST.eq_label x y) (List.combine a.labels b.labels) 
    && eq_stmtkind' (a.skind, af) (b.skind, bf)
  with Invalid_argument _ -> false

let eq_node (x, fun1) (y, fun2) =
  match x,y with
  | Statement s1, Statement s2 -> eq_stmt' (s1, fun1) (s2, fun2)
  | Function f1, Function f2 -> eq_varinfo' f1 f2
  | FunctionEntry f1, FunctionEntry f2 -> eq_varinfo' f1 f2
  | _ -> false

(*
* consider whether precise comparisons are necessary for
* Assign, Proc, Entry, Ret, VDecl
* -> yes, because with exp.mincfg many nodes are "merged" and then exclusively represented in edges
* is varinfo comparison for fundecs enough?
* -> varinfo is a unique representation for each global or local variable, but in eq_varinfo' it is only considered partly
* -> all relevant components are being compare
*)
let eq_edge x y = match x, y with
  | Assign (lv1, rv1), Assign (lv2, rv2) -> CompareAST.eq_lval lv1 lv2 && CompareAST.eq_exp rv1 rv2
  | Proc (None,f1,ars1), Proc (None,f2,ars2) -> CompareAST.eq_exp f1 f2 && CompareAST.eq_list CompareAST.eq_exp ars1 ars2
  | Proc (Some r1,f1,ars1), Proc (Some r2,f2,ars2) -> 
      CompareAST.eq_lval r1 r2 && CompareAST.eq_exp f1 f2 && CompareAST.eq_list CompareAST.eq_exp ars1 ars2
  | Entry f1, Entry f2 -> eq_varinfo' f1.svar f2.svar
  | Ret (None,fd1), Ret (None,fd2) -> eq_varinfo' fd1.svar fd2.svar
  | Ret (Some r1,fd1), Ret (Some r2,fd2) -> CompareAST.eq_exp r1 r2 && eq_varinfo' fd1.svar fd2.svar
  | Test (p1,b1), Test (p2,b2) -> CompareAST.eq_exp p1 p2 && b1 = b2
  | ASM _, ASM _ -> false
  | Skip, Skip -> true
  | VDecl v1, VDecl v2 -> eq_varinfo' v1 v2
  | SelfLoop, SelfLoop -> true
  | _ -> false

(* The order of the edges in the list is relevant. Therefor compare 
them one to one without sorting first*)
let eq_edge_list xs ys = CompareAST.eq_list eq_edge xs ys

let to_edge_list ls = List.map (fun (loc, edge) -> edge) ls

let print_min_cfg_coloring (module Cfg : CfgForward) funs edgeColoring nodeColoring fileName =
  let out = open_out fileName in

  let dotDataForFun entryNode =
    let rec dfs fromNode (vis, acc) =
      if List.mem fromNode vis then (vis, acc) 
      else
        let nodeLabel = node_to_id_string fromNode ^ ": " ^ node_to_string fromNode in
        let edgeLabel edgeList = List.fold_right (fun (loc, e) a -> edge_to_string e ^ a) edgeList "" in 
        let print_edge edgeList toNode = node_to_id_string fromNode ^ " -> " ^ node_to_id_string toNode
          ^ " [ label = \"" ^ edgeLabel edgeList ^ "\", color = \"" ^ edgeColoring entryNode fromNode (to_edge_list edgeList) toNode ^ "\" ];\n"
          ^ node_to_id_string fromNode ^ " [ label=\"" ^ nodeLabel ^ "\", color = \"" ^ nodeColoring entryNode fromNode ^ "\" ];\n" in
        let succNodes = List.map (fun (e,n) -> n) (Cfg.next fromNode) in
        let ext_acc = List.fold_right (fun (e,n) a -> a ^ (print_edge e n)) (Cfg.next fromNode) acc in
        List.fold_right dfs succNodes (fromNode :: vis, ext_acc) in
    let _, dotEdges = dfs entryNode ([],"") in
    dotEdges in
  
  let dotContent = List.fold_right (fun f a -> dotDataForFun f ^ a) funs "" in
  Printf.fprintf out "%s" ("digraph cfg {\n" ^ dotContent ^ "}");
  flush out;
  close_out_noerr out

let print_min_cfg_diff_2 (module Cfg : CfgForward) funDiff = 
  let edgeColoring f fromNode edgeList toNode =
    let stdSet, diffSet = FunDiffMap.find f funDiff in 
    let compStdSetEntry2 ((_, fn2), (_, el2), (_,tn2)) = Node.equal fn2 fromNode && Node.equal tn2 toNode && CompareAST.eq_list eq_edge edgeList el2 in
    let inStd = StdS.exists compStdSetEntry2 stdSet in 
    let compDiffSetEntry2 ((_, fn2), el2, tn2) = Node.equal fn2 fromNode && Node.equal tn2 toNode && CompareAST.eq_list eq_edge edgeList el2 in
    let inDiff = DiffS.exists compDiffSetEntry2 diffSet in  
    if inStd && inDiff then "blue"
    else if inStd then "green" 
    else if inDiff then "red" else "black" in
  let nodeColoring f node = "black" in
  let funs = FunDiffMap.fold (fun n e acc -> n :: acc) funDiff [] in
print_min_cfg_coloring (module Cfg) funs edgeColoring nodeColoring "cfg_2_diff.dot"

let print_min_cfg_diff_1 (module Cfg : CfgForward) funDiff =
  let edgeColoring f fromNode edgeList toNode =
    let stdSet, diffSet = FunDiffMap.find f funDiff in 
    let compStdSetEntry1 ((fn1,_), (el1,_), (tn1,_)) = Node.equal fn1 fromNode && Node.equal tn1 toNode && CompareAST.eq_list eq_edge edgeList el1 in
    let inStd = StdS.exists compStdSetEntry1 stdSet in 
    if inStd then "green" else "black" in
  let nodeColoring f node = "black" in
  let funs = FunDiffMap.fold (fun n e acc -> n :: acc) funDiff [] in
print_min_cfg_coloring (module Cfg) funs edgeColoring nodeColoring "cfg_1_diff.dot"

let print_rect_cfg (module Cfg : CfgForward) rectFunDiff =
  let edgeColoring f fromNode edgeList toNode = "black" in
  let nodeColoring f node =
    let sameRect, diffRect = FunDiffMap.find f rectFunDiff in
    if NodeSet.mem node sameRect then "green" 
    else if NodeSet.mem node diffRect then "red" else "black" in
  let funs = FunDiffMap.fold (fun n e acc -> n :: acc) rectFunDiff [] in
  print_min_cfg_coloring (module Cfg) funs edgeColoring nodeColoring "cfg_2_rect.dot"

let compareCfgs (module Cfg1 : CfgForward) (module Cfg2 : CfgForward) fun1 fun2 =
    let rec compareNext (stdSet, diffSet) =
      (*printf "\ncompare next in waiting list\n";
      print_queue waitingList;
      print_std_set stdSet;
      print_diff_set diffSet;*)

      if Queue.is_empty waitingList then (stdSet, diffSet) 
      else
        let (fromNode1, fromNode2) = Queue.take waitingList in
        (* printf "\n";
        printf "\nfromNode2: %s\n" (node_to_string fromNode2); *)
        let outList1 = Cfg1.next fromNode1 in
        let outList2 = Cfg2.next fromNode2 in
               
        let findEquiv (edgeList2, toNode2) ls1 stdSet diffSet = 
          let rec aux ls1 stdSet diffSet =
            match ls1 with
            | [] -> let diffSet' = DiffS.add ((fromNode1, fromNode2), edgeList2, toNode2) diffSet in (stdSet, diffSet')
            | (locEdgeList1, toNode1) :: ls1' ->
              (* printf "%s -> %s, %s -> %s\n" (node_to_id_string fromNode1) (node_to_id_string toNode1) (node_to_id_string fromNode2) (node_to_id_string toNode2); *)
              let edgeList1 = to_edge_list locEdgeList1 in
              if eq_node (toNode1, fun1) (toNode2, fun2) && eq_edge_list edgeList1 edgeList2 then
                (* printf "match\n"; *)
                ((let notIn = StdS.for_all 
                    (fun (fromNodes', edges, (toNode1', toNode2')) -> not (Node.equal toNode1 toNode1' && Node.equal toNode2 toNode2')) stdSet in
                  if notIn then (* printf "add to waitingList, "; *) Queue.add (toNode1, toNode2) waitingList);
                  let stdSet' = StdS.add ((fromNode1, fromNode2), (edgeList1, edgeList2), (toNode1, toNode2)) stdSet
                in (* printf "add to stdSet\n"; *) (stdSet', diffSet))
              else (* (printf "no match\n"; *)
              aux ls1' stdSet diffSet in
          aux ls1 stdSet diffSet in
        
        let rec iterOuts ls2 stdSet diffSet = 
          match ls2 with
          | [] -> (stdSet, diffSet)
          | (locEdgeList2, toNode2) :: ls2' ->
              let edgeList2 = to_edge_list locEdgeList2 in
              (* TODO: can exp be evaluated to also recognize Test (0,true) for example, is this neccessary? *)
              let isActualEdge = match List.hd edgeList2 with
                | Test (p,b) -> not (p = Cil.one && b = false)
                | _ -> true in
              let (stdSet', diffSet') = if isActualEdge then findEquiv (edgeList2, toNode2) outList1 stdSet diffSet else (stdSet, diffSet) in
            iterOuts ls2' stdSet' diffSet' in
      compareNext (iterOuts outList2 stdSet diffSet) in
    
    let initSets = (StdS.empty, DiffS.empty) in
    let entryNode1, entryNode2 = (FunctionEntry fun1.svar, FunctionEntry fun2.svar) in
  Queue.push (entryNode1,entryNode2) waitingList; (compareNext initSets)

let reexamine f stdSet diffSet (module Cfg2 : CfgForward) =
  let diffNodes = DiffS.fold (fun (_, _, n) acc -> NodeSet.add n acc) diffSet NodeSet.empty in
  let sameNodes = let fromStdSet = StdS.fold (fun (_, _, (_, n)) acc -> NodeSet.add n acc) stdSet NodeSet.empty in
    let notInDiff = NodeSet.diff fromStdSet diffNodes in
    NodeSet.add (FunctionEntry f.svar) notInDiff in
  let rec dfs node (vis, sameNodes, diffNodes) =
    let classify k (vis, same, diff) = if NodeSet.mem k vis then (vis, same, diff)
      else let ext_vis = NodeSet.add k vis in if NodeSet.mem k diff then (ext_vis, same, diff)
      else if NodeSet.mem k same then (ext_vis, NodeSet.remove k same, NodeSet.add k diff)
      else dfs k (ext_vis, same, diff) in
    let succ = List.map (fun (_, n) -> n) (Cfg2.next node) in
    List.fold_right classify succ (vis, sameNodes, diffNodes) in

  let (_, rectSame, rectDiff) = NodeSet.fold dfs diffNodes (NodeSet.empty, sameNodes, diffNodes) in
  rectSame, rectDiff

let compare_all_funs file1 file2 =
  let cfgF1, _ = MyCFG.getCFG file1
  and cfgF2, _ = MyCFG.getCFG file2 in

  let module Cfg1: CfgForward = struct let next = cfgF1 end in
  let module Cfg2: CfgForward = struct let next = cfgF2 end in

  let funs1, funs2 =
    let get_funs file = Cil.foldGlobals file (fun acc glob ->
            match glob with
            | GFun (fd,loc) -> fd :: acc
            | _ -> acc
          ) []
    in (get_funs file1, get_funs file2)
    (*printf "functions to be compared: %s %s\n" (List.hd x).svar.vname (List.hd y).svar.vname; *)
  in

  let (funDiff, funDiffRect) =
    let sort = List.sort (fun f g -> String.compare f.svar.vname g.svar.vname) in
    let rec aux funs1 funs2 (acc, accRect) =
      match funs1, funs2 with
      | [], [] -> (acc, accRect)
      | f1::funs1', f2::funs2' -> 
          assert (f1.svar.vname = f2.svar.vname);
          let (stdSet, diffSet) = compareCfgs (module Cfg1) (module Cfg2) f1 f2 in
          let (rectSame, rectDiff) = reexamine f2 stdSet diffSet (module Cfg2) in
          let entryNode2 = FunctionEntry f2.svar in
          aux funs1' funs2' (FunDiffMap.add entryNode2 (stdSet, diffSet) acc, FunDiffMap.add entryNode2 (rectSame, rectDiff) accRect)
      | _, _ -> raise (Invalid_argument "Function to be compared not in both files") in
    aux (sort funs1) (sort funs2) (FunDiffMap.empty, FunDiffMap.empty) in
  
  assert (List.length funs1 = List.length funs2);
  print_min_cfg_diff_2 (module Cfg2) funDiff;
  print_min_cfg_diff_1 (module Cfg1) funDiff;
  print_rect_cfg (module Cfg2) funDiffRect;
  funDiff
