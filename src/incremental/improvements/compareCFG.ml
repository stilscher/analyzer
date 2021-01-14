open MyCFG
open Queue
open Defaults
open Cil
open Format

let dirname = "/home/sarah/Studium/WS_20-21/MA/Goblint/analyzer/src/incremental/improvements"
let filename1 = "test_prog_1.c" 
let filename2 = "test_prog_2.c"

let file1, file2 =
  let create_file filename = 
    Cilfacade.init ();
      let nname =  Filename.concat dirname (Filename.basename filename) in
      let fileAST = Cilfacade.getAST nname in
      let ast = Cilfacade.callConstructors fileAST in
    Cilfacade.createCFG ast;
    ast
  in (create_file filename1, create_file filename2)

let cfgF1, cfgB1 = MyCFG.getCFG file1
let cfgF2, _ = MyCFG.getCFG file2

let fun1, fun2 =
  let get_fun file = 
      let fds = Cil.foldGlobals file (fun acc glob -> 
          match glob with
          | GFun (fd,loc) -> fd :: acc
          | _ -> acc
        ) []
    in List.hd fds
  in (get_fun file1, get_fun file2)

let entryNode1, entryNode2 = (FunctionEntry fun1.svar, FunctionEntry fun2.svar)

module Cfg1: CfgForward =
  struct
    let next = cfgF1
  end

module Cfg2: CfgForward =
  struct
    let next = cfgF2
  end

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

let waitingList : (node * node) t = Queue.create ()

let print_queue q = 
    let f (n1, n2) = printf "(%s,%s)\n" (Pretty.sprint 200 (pretty_node () n1)) (Pretty.sprint 200 (pretty_node () n2)) in 
  printf "queue: "; if Queue.is_empty q then printf "empty\n" else Queue.iter f q

let node_to_string n = Pretty.sprint 200 (pretty_node () n)

let print_std_set s = 
  let print_elem ((fromNode1, fromNode2), (edgeList1, edgeList2), (toNode1, toNode2)) = 
    printf "(%s, %s)\n" (node_to_string fromNode2) (node_to_string toNode2)
    (* printf "((%s, %s), (%s, %s))\n" (node_to_string fromNode1) (node_to_string fromNode2) 
      (node_to_string toNode1) (node_to_string toNode2) *) in 
  printf "std set: "; if StdS.is_empty s then printf "empty\n" else StdS.iter print_elem s

let print_diff_set s =
  let print_elem ((fromNode1, fromNode2), edgeList2, toNode2) = 
    printf "((%s, %s), %s)\n" (node_to_string fromNode1) (node_to_string fromNode2) (node_to_string toNode2) in 
  printf "diff set: "; if DiffS.is_empty s then printf "empty\n" else DiffS.iter print_elem s

let eq_node x y =
  match x,y with
  | Statement s1, Statement s2 -> CompareAST.eq_stmt (s1, fun1) (s2, fun2)
  | Function f1, Function f2 -> CompareAST.eq_varinfo f1 f2
  | FunctionEntry f1, FunctionEntry f2 -> CompareAST.eq_varinfo f1 f2
  | _ -> false

let to_edge_list ls = List.map (fun (loc, edge) -> edge) ls

(* TODO
* consider whether precise comparisons are necessary for
* Assign, Proc, Entry, Ret, VDecl
*)
let eq_edge x y = match x, y with
  | Assign (lv1, rv1), Assign (lv2, rv2) -> CompareAST.eq_lval lv1 lv2 && CompareAST.eq_exp rv1 rv2
  | Proc (None,f1,ars1), Proc (None,f2,ars2) -> true
  | Proc (Some r1,f1,ars1), Proc (Some r2,f2,ars2) -> true
  | Entry f1, Entry f2 -> true
  | Ret (Some r1,fd1), Ret (Some r2,fd2) -> true
  | Test (p1,b1), Test (p2,b2) -> CompareAST.eq_exp p1 p2 && b1 = b2
  | ASM _, ASM _ -> false
  | Skip, Skip -> true
  | VDecl v1, VDecl v2 -> CompareAST.eq_varinfo v1 v2
  | SelfLoop, SelfLoop -> true
  | _ -> false

let eq_edge_list xs ys = CompareAST.eq_list eq_edge xs ys

let compare =
    let rec compareNext (stdSet, diffSet) =
      (*printf "\ncompare next in waiting list\n";
      print_queue waitingList;
      print_std_set stdSet;
      print_diff_set diffSet;*)

      if Queue.is_empty waitingList then (stdSet, diffSet) 
      else
        let (fromNode1, fromNode2) = Queue.take waitingList in
        let outList1 = Cfg1.next fromNode1 in
        let outList2 = Cfg2.next fromNode2 in
               
        let findEquiv (edgeList2, toNode2) ls1 stdSet diffSet = 
          (* printf "look for equiv edge in graph 1 by iterating over them, %d more to go\n" (List.length ls1); *)
          let rec aux ls1 stdSet diffSet =
            match ls1 with
            | [] -> let diffSet' = DiffS.add ((fromNode1, fromNode2), edgeList2, toNode2) diffSet in (stdSet, diffSet')
            | (locEdgeList1, toNode1) :: ls1' ->
              let edgeList1 = to_edge_list locEdgeList1 in
              if eq_node toNode1 toNode2 && eq_edge_list edgeList1 edgeList2 then
                ((let notIn = StdS.for_all 
                    (fun (fromNodes', edges, (toNode1', toNode2')) -> not (Node.equal toNode1 toNode1') || not (Node.equal toNode2 toNode2')) stdSet in
                    (* printf "%b\n" notIn; *)
                  if notIn then Queue.add (toNode1, toNode2) waitingList);
                  let stdSet' = StdS.add ((fromNode1, fromNode2), (edgeList1, edgeList2), (toNode1, toNode2)) stdSet
                in (stdSet', diffSet))
              else aux ls1' stdSet diffSet in
          ( (* printf "size of outList1 %d\n" (List.length ls1); *) aux ls1 stdSet diffSet) in
        
        let rec iterOuts ls2 stdSet diffSet = 
          (* printf "iterate over outgoing edges of graph 2, %d more to go\n" (List.length ls2); *)
          match ls2 with
          | [] -> (stdSet, diffSet)
          | (locEdgeList2, toNode2) :: ls2' ->
              let edgeList2 = to_edge_list locEdgeList2 in
              let (stdSet', (diffSet' : DiffS.t)) = findEquiv (edgeList2, toNode2) outList1 stdSet diffSet in
            iterOuts ls2' stdSet' diffSet' in
      (* printf "size of outList2 %d\n" (List.length outList2); *)
      compareNext (iterOuts outList2 stdSet diffSet) in
    
    let initSets = (StdS.empty, DiffS.empty) in
  Queue.push (entryNode1,entryNode2) waitingList; (compareNext initSets)

let () = let (stdSet', diffSet') = compare in
  print_std_set stdSet';
  print_diff_set diffSet';
  print_queue waitingList
