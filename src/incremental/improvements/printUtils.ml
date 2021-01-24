open Format
open Cil

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
