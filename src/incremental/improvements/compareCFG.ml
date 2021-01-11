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

let en1, en2 =
  let get_entry_node file = 
      let fds = Cil.foldGlobals file (fun acc glob -> 
          match glob with
          | GFun (fd,loc) -> fd :: acc
          | _ -> acc
        ) []
    in FunctionEntry (List.hd fds).svar
  in (get_entry_node file1, get_entry_node file2)  


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
    type t = (node * node) * (* edge * *) (node * node)
  end
)

module DiffS = Set.Make (
  struct
    let compare = compare
    type t = (node * node) * (* edge * *) node 
  end  
)

let waitingList : (node * node) t = Queue.create ()

let print_queue q = 
    let f (n1, n2) = printf "(%s,%s)\n" (Pretty.sprint 200 (pretty_node () n1)) (Pretty.sprint 200 (pretty_node () n2)) in 
  printf "queue: "; if Queue.is_empty q then printf "empty\n" else Queue.iter f q

let node_to_string n = Pretty.sprint 200 (pretty_node () n)

let print_std_set s = 
  let print_elem ((fromNode1, fromNode2), (toNode1, toNode2)) = 
    printf "((%s, %s), (%s, %s))\n" (node_to_string fromNode1) (node_to_string fromNode2) (node_to_string toNode1) (node_to_string toNode2) in 
  printf "std set: "; if StdS.is_empty s then printf "empty\n" else StdS.iter print_elem s

let print_diff_set s =
  let print_elem ((fromNode1, fromNode2), toNode2) = 
    printf "((%s, %s), %s)\n" (node_to_string fromNode1) (node_to_string fromNode2) (node_to_string toNode2) in 
  printf "diff set: "; if DiffS.is_empty s then printf "empty\n" else DiffS.iter print_elem s

let print_instr i = match i with
  | Set (lval, exp, loc) -> printf "Set (loc %d,%s,%d)" loc.line loc.file loc.byte
  | Call _ -> printf "Call"
  | Asm _ -> printf "Asm"
  | VarDecl _ -> printf "VarDecl"

let print_stmtkind k = match k with
  | Instr i -> printf "Instr: "; List.iter print_instr i; printf "\n"
  | Return _ -> printf "Return\n"
  | Goto _ -> printf "Goto\n"
  | Break _ -> printf "Break\n"
  | Continue _ -> printf "Continue\n"
  | If _ -> printf "If\n"
  | Switch _ -> printf "Switch\n" 
  | Loop _ -> printf "Loop\n"
  | Block _ -> printf "Statement kind: Block\n"
  | TryFinally _ -> printf "Statement kind: TryFinally\n"
  | TryExcept _ -> printf "Statement kind: TryExcept\n"
  | ComputedGoto _ -> printf "Computed Goto\n"

let stmtkindEquiv x y = 
  match x, y with
  | Instr i1, Instr i2 -> true
  | Return (r1, l1), Return (r2, l2) -> true
  | Goto (g1, l1), Goto (g2, l2) -> true
  | Break b1, Break b2 -> true
  | Continue c1, Continue c2 -> true
  | If _, If _ -> true
  | Switch _, Switch _ -> true
  | Loop _, Loop _ -> true
  | Block b1, Block b2 -> true
  | TryFinally _, TryFinally _ -> true
  | TryExcept _, TryExcept _ -> true
  | _, _ -> false

let eq_node x y =
  match x,y with
  | Statement s1, Statement s2 -> stmtkindEquiv s1.skind s2.skind
  | Function f1, Function f2 -> f1.vname = f2.vname 
                                && f1.vtype = f2.vtype 
                                (* && f1.vattr = f2.vattr 
                                && f1.vglob = f2.vglob
                                && f1.vinline = f2.vinline
                                && f1.vaddrof = f2.vaddrof *)
  | FunctionEntry f1, FunctionEntry f2 -> f1.vname = f2.vname 
                                && f1.vtype = f2.vtype 
                                (* && f1.vattr = f2.vattr 
                                && f1.vglob = f2.vglob
                                && f1.vinline = f2.vinline
                                && f1.vaddrof = f2.vaddrof *)
  | _ -> false

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
            | [] -> let diffSet' = DiffS.add ((fromNode1, fromNode2), toNode2) diffSet in (stdSet, diffSet')
            | (edgeList1, toNode1) :: ls1' -> 
              if eq_node toNode1 toNode2 then
                ((let notIn = StdS.for_all 
                    (fun (fromNodes', (toNode1', toNode2')) -> not (Node.equal toNode1 toNode1') || not (Node.equal toNode2 toNode2')) stdSet in
                    (* printf "%b\n" notIn; *)
                  if notIn then Queue.add (toNode1, toNode2) waitingList);
                  let stdSet' = StdS.add ((fromNode1, fromNode2), (toNode1, toNode2)) stdSet
                in (stdSet', diffSet))
              else aux ls1' stdSet diffSet in
          ( (* printf "size of outList1 %d\n" (List.length ls1); *) aux ls1 stdSet diffSet) in
        
        let rec iterOuts ls2 stdSet diffSet = 
          (* printf "iterate over outgoing edges of graph 2, %d more to go\n" (List.length ls2); *)
          match ls2 with
          | [] -> (stdSet, diffSet)
          | (edgeList2, toNode2) :: ls2' -> 
              let (stdSet', (diffSet' : DiffS.t)) = findEquiv (edgeList2, toNode2) outList1 stdSet diffSet in
            iterOuts ls2' stdSet' diffSet' in
      (* printf "size of outList2 %d\n" (List.length outList2); *)
      compareNext (iterOuts outList2 stdSet diffSet) in
    
    let initSets = (StdS.empty, DiffS.empty) in
  Queue.push (en1,en2) waitingList; (compareNext initSets)

let () = let (stdSet', diffSet') = compare in
  print_std_set stdSet';
  print_diff_set diffSet';
  print_queue waitingList
  
  (*
    let _, cfg = MyCFG.createCFG file1 in 
    let [([(l1, e1)], nd1)] = Cfg1.next en1 in
    let [([(l2, e2)], nd2)] = Cfg1.next nd1 in
    let [([(l31, e31)], nd31); ([(l32, e32)], nd32); ([(l33, e33)], nd33)] = Cfg1.next nd2 in
    let [([(l4, e4)], nd4)] = Cfg1.next nd31 in
    let [([(l5, e5)], nd5)] = Cfg1.next nd32 in
    let [([(l6, e6)], nd6)] = Cfg1.next nd33 in
    let [([(l7, e7)], nd7)] = Cfg1.next nd5 in
  printf "%s\n" (Pretty.sprint 100 (pretty_edge () e7));
  *)
  (*
  printf "%s\n" entry_node1;
  print cfgF1
  *)
  (*
  Cilfacade.print_to_file "src/incremental/improvements/test_cfg_1.txt" file1;
  Cilfacade.print_to_file "src/incremental/improvements/test_cfg_2.txt" file2
  *)  
  (* Queue.add (4,5) waitingList; let (a,b) = Queue.take waitingList in printf "%d, %d\n" a b *)
  (*printf "Hello World!\n"*)
