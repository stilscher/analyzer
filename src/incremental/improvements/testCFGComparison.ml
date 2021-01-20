open CompareCFG

(*
let dirname = "/home/sarah/Studium/WS_20-21/MA/Goblint/analyzer/src/incremental/improvements"
let filename1 = "instr_list_prog_1.c" 
let filename2 = "instr_list_prog_2.c"
*)

let dirname = "/home/sarah/Studium/WS_20-21/MA/Goblint/analyzer/tests/regression/01-cpa"
let filename1 = "04-functions.c" 
let filename2 = "04-functions'.c"

let file1, file2 =
    let create_file filename dirname = 
      Cilfacade.init ();
        let nname = Filename.concat dirname (Filename.basename filename) in
        let fileAST = Cilfacade.getAST nname in
        let ast = Cilfacade.callConstructors fileAST in
      Cilfacade.createCFG ast;
      ast
  in (create_file filename1 dirname, create_file filename2 dirname)

let () =
  let r = compare_all_funs file1 file2 in
  let rec print_res ls = match ls with
    | [] -> ()
    | (stdSet', diffSet')::ls' -> print_std_set stdSet'; print_diff_set diffSet'; print_queue waitingList; print_res ls'
  in print_res r
  (*
  let _, cfg = MyCFG.createCFG file1 in
  printf "cfg created\n";
  print cfg *)
