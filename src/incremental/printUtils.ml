open Format
open Cil
open MyCFG
open CompareCFG

let print_instr i = match i with
  | Set (lval, exp, loc) -> printf "Set (loc %d,%s,%d)" loc.line loc.file loc.byte
  | Call _ -> printf "Call"
  | Asm _ -> printf "Asm"
  | VarDecl _ -> printf "VarDecl"

let print_stmtkind k = match k with
  | Instr i -> printf "Statement kind: Instr: "; List.iter print_instr i; printf "\n"
  | Return _ -> printf "Statement kind: Return\n"
  | Goto _ -> printf "Statement kind: Goto\n"
  | Break _ -> printf "Statement kind: Break\n"
  | Continue _ -> printf "Statement kind: Continue\n"
  | If _ -> printf "Statement kind: If\n"
  | Switch _ -> printf "Statement kind: Switch\n" 
  | Loop _ -> printf "Statement kind: Loop\n"
  | Block _ -> printf "Statement kind: Block\n"
  | TryFinally _ -> printf "Statement kind: TryFinally\n"
  | TryExcept _ -> printf "Statement kind: TryExcept\n"
  | ComputedGoto _ -> printf "Computed Goto\n"

let label_to_string l = Pretty.sprint 200 (d_label () l)

let node_to_string n = Pretty.sprint 200 (pretty_node () n)
let edge_to_string e = Pretty.sprint 200 (pretty_edge () e)
let node_to_id_string n = 
  let id = match n with
    | Statement s -> s.sid
    | FunctionEntry f -> f.vid
    | Function f -> f.vid
    in string_of_int id

let print_queue q = 
  let f (n1, n2) = Format.printf "(%s,%s)\n" (Pretty.sprint 200 (pretty_node () n1)) (Pretty.sprint 200 (pretty_node () n2)) in 
Format.printf "queue: "; if Queue.is_empty q then Format.printf "empty\n" else Queue.iter f q

(* To print a tex compatible dot file representing the cfgs for the given functions *)
let print_min_cfg_coloring (module Cfg : CfgForward) funs edgeColoring nodeColoring fileName =
  let out = open_out fileName in

  let dotDataForFun entryNode =
    let node_to_unique_id_string n = match n with FunctionEntry f -> "fun" ^ string_of_int f.vid | Function f -> "ret" ^ string_of_int f.vid | Statement s -> string_of_int s.sid in
    let nodeLabel n = String.escaped (node_to_id_string n ^ ": " ^ node_to_string n) in
    let print_node n = node_to_unique_id_string n ^ " [ label=\"" ^ nodeLabel n ^ "\", color = \"" ^ nodeColoring entryNode n ^ "\" ];\n" in
    let rec dfs fromNode (vis, acc) =
      if List.mem fromNode vis then (vis, acc)
      else
        let edgeLabel edgeList = String.escaped (List.fold_right (fun (loc, e) a -> edge_to_string e ^ a) edgeList "") in
        let print_edge edgeList toNode = node_to_unique_id_string fromNode ^ " -> " ^ node_to_unique_id_string toNode
          ^ " [ label = \" " ^ edgeLabel edgeList ^ "\", color = \"" ^ edgeColoring entryNode fromNode (to_edge_list edgeList) toNode ^ "\" ];\n"
          ^ print_node toNode in
        let succNodes = List.map (fun (e,n) -> n) (Cfg.next fromNode) in
        let ext_acc = List.fold_right (fun (e,n) a -> a ^ (print_edge e n)) (Cfg.next fromNode) acc in
        List.fold_right dfs succNodes (fromNode :: vis, ext_acc) in
    let _, dotEdges = dfs entryNode ([],"") in
    print_node entryNode ^ dotEdges in

  let content = List.fold_right (fun f a -> dotDataForFun f ^ a) funs "" in
  print_endline "print cfg dot file";
  Printf.fprintf out "%s" ("\digraph{cfg}{\n" ^ content ^ "}");
  flush out;
  close_out_noerr out
