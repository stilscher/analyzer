open MyCFG
open Queue
open Defaults
open Cil
open Format

type nodes_diff = {
  unchangedNodes: (node * node) list;
  primChangedNodes: node list;
  changedNodes: node list;
}

type changed_global = {
  old: global;
  current: global;
  diff: nodes_diff option
}

type change_info = {
  mutable changed: changed_global list;
  mutable unchanged: global list;
  mutable removed: global list;
  mutable added: global list
}

let empty_change_info () : change_info = {added = []; removed = []; changed = []; unchanged = []}

type global_type = Fun | Decl | Var | Other

type global_identifier = {name: string ; global_t: global_type}

let identifier_of_global glob =
  match glob with
  | GFun (fundec, l) -> {name = fundec.svar.vname; global_t = Fun}
  | GVar (var, init, l) -> {name = var.vname; global_t = Var}
  | GVarDecl (var, l) -> {name = var.vname; global_t = Decl}
  | _ -> raise (Failure "No variable or function")

let any_changed (c: change_info) =
  not @@ List.for_all (fun l -> l = 0) [List.length c.changed; List.length c.removed; List.length c.added]

(* Check whether any changes to function definitions or types of globals were detected *)
let check_any_changed (c: change_info) =
  if GobConfig.get_string "exp.incremental.mode" = "incremental" then
    print_endline @@ "Function definitions " ^ (if any_changed c then "or types of globals changed." else "and types of globals did not change.")

(* Print whether the analyzed intermediate code changed *)
let check_file_changed (old_commit_dir: string) (current_commit_dir: string) =
  let old = Filename.concat old_commit_dir "cil.c" in
  let current = Filename.concat current_commit_dir "cil.c" in
  let old_file = BatFile.with_file_in old BatIO.read_all in
  let current_file = BatFile.with_file_in current BatIO.read_all in
  print_endline @@ "CIL-file " ^ (if old_file = current_file then "did not change." else "changed.")

module GlobalMap = Map.Make(struct
    type t = global_identifier
    let compare a b =
      let c = compare a.name b.name in
      if c <> 0
      then c
      else compare a.global_t b.global_t
  end)

let eq_list eq xs ys =
  try
    List.for_all (fun (a,b) -> eq a b) (List.combine xs ys)
  with Invalid_argument _ -> false

let eqB (a: Cil.block) (b: Cil.block) =
  a.Cil.battrs = b.Cil.battrs && a.bstmts = b.bstmts

let eqS (a: Cil.stmt) (b: Cil.stmt) =
  a.Cil.skind = b.Cil.skind

let print (a: Pretty.doc)  =
  print_endline @@ Pretty.sprint 100 a

(* hack: CIL generates new type names for anonymous types - we want to ignore these *)
let compare_name a b =
  let anon_struct = "__anonstruct_" in
  let anon_union = "__anonunion_" in
  if a = b then true else BatString.(starts_with a anon_struct && starts_with b anon_struct || starts_with a anon_union && starts_with b anon_union)

let rec eq_constant (a: constant) (b: constant) = match a, b with
    CInt64 (val1, kind1, str1), CInt64 (val2, kind2, str2) -> val1 = val2 && kind1 = kind2 (* Ignore string representation, i.e. 0x2 == 2 *)
  | CEnum (exp1, str1, enuminfo1), CEnum (exp2, str2, enuminfo2) -> eq_exp exp1 exp2 (* Ignore name and enuminfo  *)
  | a, b -> a = b

and eq_exp (a: exp) (b: exp) = match a,b with
  | Const c1, Const c2 -> eq_constant c1 c2
  | Lval lv1, Lval lv2 -> eq_lval lv1 lv2
  | SizeOf typ1, SizeOf typ2 -> eq_typ typ1 typ2
  | SizeOfE exp1, SizeOfE exp2 -> eq_exp exp1 exp2
  | SizeOfStr str1, SizeOfStr str2 -> str1 = str2 (* possibly, having the same length would suffice *)
  | AlignOf typ1, AlignOf typ2 -> eq_typ typ1 typ2
  | AlignOfE exp1, AlignOfE exp2 -> eq_exp exp1 exp2
  | UnOp (op1, exp1, typ1), UnOp (op2, exp2, typ2) -> op1 == op2 && eq_exp exp1 exp2 && eq_typ typ1 typ2
  | BinOp (op1, left1, right1, typ1), BinOp (op2, left2, right2, typ2) ->  op1 = op2 && eq_exp left1 left2 && eq_exp right1 right2 && eq_typ typ1 typ2
  | CastE (typ1, exp1), CastE (typ2, exp2) -> eq_typ typ1 typ2 &&  eq_exp exp1 exp2
  | AddrOf lv1, AddrOf lv2 -> eq_lval lv1 lv2
  | StartOf lv1, StartOf lv2 -> eq_lval lv1 lv2
  | _, _ -> false

and eq_lhost (a: lhost) (b: lhost) = match a, b with
    Var v1, Var v2 -> eq_varinfo v1 v2
  | Mem exp1, Mem exp2 -> eq_exp exp1 exp2
  | _, _ -> false

and eq_typ_acc (a: typ) (b: typ) (acc: (typ * typ) list) =
  if( List.exists (fun x-> match x with (x,y)-> a==x && b == y) acc)
  then true
  else (let acc = List.cons (a,b) acc in
        match a, b with
        | TPtr (typ1, attr1), TPtr (typ2, attr2) -> eq_typ_acc typ1 typ2 acc && eq_list eq_attribute attr1 attr2
        | TArray (typ1, (Some lenExp1), attr1), TArray (typ2, (Some lenExp2), attr2) -> eq_typ_acc typ1 typ2 acc && eq_exp lenExp1 lenExp2 &&  eq_list eq_attribute attr1 attr2
        | TArray (typ1, None, attr1), TArray (typ2, None, attr2) -> eq_typ_acc typ1 typ2 acc && eq_list eq_attribute attr1 attr2
        | TFun (typ1, (Some list1), varArg1, attr1), TFun (typ2, (Some list2), varArg2, attr2)
          ->  eq_typ_acc typ1 typ2 acc && eq_list eq_args list1 list2 && varArg1 = varArg2 &&
              eq_list eq_attribute attr1 attr2
        | TFun (typ1, None, varArg1, attr1), TFun (typ2, None, varArg2, attr2)
          ->  eq_typ_acc typ1 typ2 acc && varArg1 = varArg2 &&
              eq_list eq_attribute attr1 attr2
        | TNamed (typinfo1, attr1), TNamed (typeinfo2, attr2) -> eq_typ_acc typinfo1.ttype typeinfo2.ttype acc && eq_list eq_attribute attr1 attr2 (* Ignore tname, treferenced *)
        | TNamed (tinf, attr), b -> eq_typ_acc tinf.ttype b acc (* Ignore tname, treferenced. TODO: dismiss attributes, or not? *)
        | a, TNamed (tinf, attr) -> eq_typ_acc a tinf.ttype acc (* Ignore tname, treferenced . TODO: dismiss attributes, or not? *)
        (* The following two lines are a hack to ensure that anonymous types get the same name and thus, the same typsig *)
        | TComp (compinfo1, attr1), TComp (compinfo2, attr2) -> let res = eq_compinfo compinfo1 compinfo2 acc &&  eq_list eq_attribute attr1 attr2 in (if res && compinfo1.cname <> compinfo2.cname then compinfo2.cname <- compinfo1.cname); res
        | TEnum (enuminfo1, attr1), TEnum (enuminfo2, attr2) -> let res = eq_enuminfo enuminfo1 enuminfo2 && eq_list eq_attribute attr1 attr2 in (if res && enuminfo1.ename <> enuminfo2.ename then enuminfo2.ename <- enuminfo1.ename); res
        | TBuiltin_va_list attr1, TBuiltin_va_list attr2 -> eq_list eq_attribute attr1 attr2
        | _, _ -> a = b)

and eq_typ (a: typ) (b: typ) = eq_typ_acc a b []

and eq_eitems (a: string * exp * location) (b: string * exp * location) = match a, b with
    (name1, exp1, _l1), (name2, exp2, _l2) -> name1 = name2 && eq_exp exp1 exp2
(* Ignore location *)

and eq_enuminfo (a: enuminfo) (b: enuminfo) =
  compare_name a.ename b.ename &&
  eq_list eq_attribute a.eattr b.eattr &&
  eq_list eq_eitems a.eitems b.eitems
(* Ignore ereferenced *)

and eq_args (a: string * typ * attributes) (b: string * typ * attributes) = match a, b with
    (name1, typ1, attr1), (name2, typ2, attr2) -> name1 = name2 && eq_typ typ1 typ2 && eq_list eq_attribute attr1 attr2

and eq_typsig (a: typsig) (b: typsig) =
  match a, b with
  | TSArray (ts1, i1, attr1), TSArray (ts2, i2, attr2) -> eq_typsig ts1 ts2 && i1 = i2 && eq_list eq_attribute attr1 attr2
  | TSPtr (ts1, attr1), TSPtr (ts2, attr2) -> eq_typsig ts1 ts2 && eq_list eq_attribute attr1 attr2
  | TSComp (b1, str1, attr1), TSComp (b2, str2, attr2) -> b1 = b2 && str1 = str2 && eq_list eq_attribute attr1 attr2
  | TSFun (ts1, Some tsList1, b1, attr1), TSFun (ts2, Some tsList2, b2, attr2) -> eq_typsig ts1 ts2 && eq_list eq_typsig tsList1 tsList2 && b1 = b2 && eq_list eq_attribute attr1 attr2
  | TSFun (ts1, None, b1, attr1), TSFun (ts2, None, b2, attr2) -> eq_typsig ts1 ts2 && b1 = b2 && eq_list eq_attribute attr1 attr2
  | TSEnum (str1, attr1), TSEnum (str2, attr2) -> str1 = str2 && eq_list eq_attribute attr1 attr2
  | TSBase typ1, TSBase typ2 -> eq_typ_acc typ1 typ2 []
  | _, _ -> false

and eq_attrparam (a: attrparam) (b: attrparam) = match a, b with
  | ACons (str1, attrparams1), ACons (str2, attrparams2) -> str1 = str2 && eq_list eq_attrparam attrparams1 attrparams2
  | ASizeOf typ1, ASizeOf typ2 -> eq_typ typ1 typ2
  | ASizeOfE attrparam1, ASizeOfE attrparam2 -> eq_attrparam attrparam1 attrparam2
  | ASizeOfS typsig1, ASizeOfS typsig2 -> typsig1 = typsig2
  | AAlignOf typ1, AAlignOf typ2 -> eq_typ typ1 typ2
  | AAlignOfE attrparam1, AAlignOfE attrparam2 -> eq_attrparam attrparam1 attrparam2
  | AAlignOfS typsig1, AAlignOfS typsig2 -> typsig1 = typsig2
  | AUnOp (op1, attrparam1), AUnOp (op2, attrparam2) -> op1 = op2 && eq_attrparam attrparam1 attrparam2
  | ABinOp (op1, left1, right1), ABinOp (op2, left2, right2) -> op1 = op2 && eq_attrparam left1 left2 && eq_attrparam right1 right2
  | ADot (attrparam1, str1), ADot (attrparam2, str2) -> eq_attrparam attrparam1 attrparam2 && str1 = str2
  | AStar attrparam1, AStar attrparam2 -> eq_attrparam attrparam1 attrparam2
  | AAddrOf attrparam1, AAddrOf attrparam2 -> eq_attrparam attrparam1 attrparam2
  | AIndex (left1, right1), AIndex (left2, right2) -> eq_attrparam left1 left2 && eq_attrparam right1 right2
  | AQuestion (left1, middle1, right1), AQuestion (left2, middle2, right2) -> eq_attrparam left1 left2 && eq_attrparam middle1 middle2 && eq_attrparam right1 right2
  | a, b -> a = b

and eq_attribute (a: attribute) (b: attribute) = match a, b with
    Attr (name1, params1), Attr (name2, params2) -> name1 = name2 && eq_list eq_attrparam params1 params2

and eq_varinfo (a: varinfo) (b: varinfo) = a.vname = b.vname && eq_typ a.vtype b.vtype && eq_list eq_attribute a.vattr b.vattr &&
                                           a.vstorage = b.vstorage && a.vglob = b.vglob && a.vinline = b.vinline && a.vaddrof = b.vaddrof
(* Ignore the location, vid, vreferenced, vdescr, vdescrpure *)

(* Accumulator is needed because of recursive types: we have to assume that two types we already encountered in a previous step of the recursion are equivalent *)
and eq_compinfo (a: compinfo) (b: compinfo) (acc: (typ * typ) list) =
  a.cstruct = b.cstruct &&
  compare_name a.cname b.cname &&
  eq_list (fun a b-> eq_fieldinfo a b acc) a.cfields b.cfields &&
  eq_list eq_attribute a.cattr b.cattr &&
  a.cdefined = b.cdefined (* Ignore ckey, and ignore creferenced *)

and eq_fieldinfo (a: fieldinfo) (b: fieldinfo) (acc: (typ * typ) list)=
  a.fname = b.fname && eq_typ_acc a.ftype b.ftype acc && a.fbitfield = b.fbitfield &&  eq_list eq_attribute a.fattr b.fattr

and eq_offset (a: offset) (b: offset) = match a, b with
    NoOffset, NoOffset -> true
  | Field (info1, offset1), Field (info2, offset2) -> eq_fieldinfo info1 info2 [] && eq_offset offset1 offset2
  | Index (exp1, offset1), Index (exp2, offset2) -> eq_exp exp1 exp2 && eq_offset offset1 offset2
  | _, _ -> false

and eq_lval (a: lval) (b: lval) = match a, b with
    (host1, off1), (host2, off2) -> eq_lhost host1 host2 && eq_offset off1 off2

let eq_instr (a: instr) (b: instr) = match a, b with
  | Set (lv1, exp1, _l1), Set (lv2, exp2, _l2) -> eq_lval lv1 lv2 && eq_exp exp1 exp2
  | Call (Some lv1, f1, args1, _l1), Call (Some lv2, f2, args2, _l2) -> eq_lval lv1 lv2 && eq_exp f1 f2 && eq_list eq_exp args1 args2
  | Call (None, f1, args1, _l1), Call (None, f2, args2, _l2) -> eq_exp f1 f2 && eq_list eq_exp args1 args2
  | Asm (attr1, tmp1, ci1, dj1, rk1, l1), Asm (attr2, tmp2, ci2, dj2, rk2, l2) -> eq_list String.equal tmp1 tmp2 && eq_list(fun (x1,y1,z1) (x2,y2,z2)-> x1 = x2 && y1 = y2 && eq_lval z1 z2) ci1 ci2 && eq_list(fun (x1,y1,z1) (x2,y2,z2)-> x1 = x2 && y1 = y2 && eq_exp z1 z2) dj1 dj2 && eq_list String.equal rk1 rk2(* ignore attributes and locations *)
  | _, _ -> false

let eq_label (a: label) (b: label) = match a, b with
    Label (lb1, _l1, s1), Label (lb2, _l2, s2) -> lb1 = lb2 && s1 = s2
  |   Case (exp1, _l1), Case (exp2, _l2) -> exp1 = exp2
  | Default _l1, Default l2 -> true
  | _, _ -> false

(* This is needed for checking whether a goto does go to the same semantic location/statement*)
let eq_stmt_with_location ((a, af): stmt * fundec) ((b, bf): stmt * fundec) =
  let offsetA = a.sid - (List.hd af.sallstmts).sid in
  let offsetB = b.sid - (List.hd bf.sallstmts).sid in
  eq_list eq_label a.labels b.labels && offsetA = offsetB

let rec eq_stmtkind ((a, af): stmtkind * fundec) ((b, bf): stmtkind * fundec) =
  let eq_block' = fun x y -> eq_block (x, af) (y, bf) in
  match a, b with
  | Instr is1, Instr is2 -> eq_list eq_instr is1 is2
  | Return (Some exp1, _l1), Return (Some exp2, _l2) -> eq_exp exp1 exp2
  | Return (None, _l1), Return (None, _l2) -> true
  | Return _, Return _ -> false
  | Goto (st1, _l1), Goto (st2, _l2) -> eq_stmt_with_location (!st1, af) (!st2, bf)
  | Break _, Break _ -> true
  | Continue _, Continue _ -> true
  | If (exp1, then1, else1, _l1), If (exp2, then2, else2, _l2) -> eq_exp exp1 exp2 && eq_block' then1 then2 && eq_block' else1 else2
  | Switch (exp1, block1, stmts1, _l1), Switch (exp2, block2, stmts2, _l2) -> eq_exp exp1 exp2 && eq_block' block1 block2 && eq_list (fun a b -> eq_stmt (a,af) (b,bf)) stmts1 stmts2
  | Loop (block1, _l1, _con1, _br1), Loop (block2, _l2, _con2, _br2) -> eq_block' block1 block2
  | Block block1, Block block2 -> eq_block' block1 block2
  | TryFinally (tryBlock1, finallyBlock1, _l1), TryFinally (tryBlock2, finallyBlock2, _l2) -> eq_block' tryBlock1 tryBlock2 && eq_block' finallyBlock1 finallyBlock2
  | TryExcept (tryBlock1, exn1, exceptBlock1, _l1), TryExcept (tryBlock2, exn2, exceptBlock2, _l2) -> eq_block' tryBlock1 tryBlock2 && eq_block' exceptBlock1 exceptBlock2
  | _, _ -> false

and eq_stmt ((a, af): stmt * fundec) ((b, bf): stmt * fundec) =
  List.for_all (fun (x,y) -> eq_label x y) (List.combine a.labels b.labels) &&
  eq_stmtkind (a.skind, af) (b.skind, bf)

and eq_block ((a, af): Cil.block * fundec) ((b, bf): Cil.block * fundec) =
  a.battrs = b.battrs && List.for_all (fun (x,y) -> eq_stmt (x, af) (y, bf)) (List.combine a.bstmts b.bstmts)

let rec eq_init (a: init) (b: init) = match a, b with
  | SingleInit e1, SingleInit e2 -> eq_exp e1 e2
  | CompoundInit (t1, l1), CompoundInit (t2, l2) -> eq_typ t1 t2 && eq_list (fun (o1, i1) (o2, i2) -> eq_offset o1 o2 && eq_init i1 i2) l1 l2
  | _, _ -> false

let eq_initinfo (a: initinfo) (b: initinfo) = match a.init, b.init with
  | (Some init_a), (Some init_b) -> eq_init init_a init_b
  | None, None -> true
  | _, _ -> false


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

module NodeNodeSet = Set.Make (
    struct
      let compare = compare
      type t = node * node
    end  
)

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
let eq_varinfo' (a: varinfo) (b: varinfo) = a.vname = b.vname && eq_typ a.vtype b.vtype && eq_list eq_attribute a.vattr b.vattr &&
                                           a.vstorage = b.vstorage && a.vglob = b.vglob
(* Ignore the location, vid, vreferenced, vdescr, vdescrpure, vinline, vaddrof*)

let eq_instr' (a: instr) (b: instr) = match a, b with
  | Set (lv1, exp1, _l1), Set (lv2, exp2, _l2) -> eq_lval lv1 lv2 && eq_exp exp1 exp2
  | Call (Some lv1, f1, args1, _l1), Call (Some lv2, f2, args2, _l2) -> eq_lval lv1 lv2 && eq_exp f1 f2 && eq_list eq_exp args1 args2
  | Call (None, f1, args1, _l1), Call (None, f2, args2, _l2) -> eq_exp f1 f2 && eq_list eq_exp args1 args2
  | Asm (attr1, tmp1, ci1, dj1, rk1, l1), Asm (attr2, tmp2, ci2, dj2, rk2, l2) -> 
      eq_list String.equal tmp1 tmp2 && eq_list(fun (x1,y1,z1) (x2,y2,z2)-> x1 = x2 && y1 = y2 
      && eq_lval z1 z2) ci1 ci2 && eq_list(fun (x1,y1,z1) (x2,y2,z2)-> x1 = x2 && y1 = y2 
      && eq_exp z1 z2) dj1 dj2 && eq_list String.equal rk1 rk2(* ignore attributes and locations *)
  | VarDecl (v1, _l1), VarDecl (v2, _l2) -> eq_varinfo' v1 v2
  | _, _ -> false

(* in contrast to the similar method eq_stmtkind in CompareAST, 
this method does not compare the inner body, that is sub blocks,
of if and switch statements *)
let eq_stmtkind' ((a, af): stmtkind * fundec) ((b, bf): stmtkind * fundec) =
  let eq_block' = fun x y -> eq_block (x, af) (y, bf) in
  match a, b with
  | Instr is1, Instr is2 -> eq_list eq_instr' is1 is2
  | Return (Some exp1, _l1), Return (Some exp2, _l2) -> eq_exp exp1 exp2
  | Return (None, _l1), Return (None, _l2) -> true
  | Return _, Return _ -> false
  | Goto (st1, _l1), Goto (st2, _l2) -> eq_stmt_with_location (!st1, af) (!st2, bf)
  | Break _, Break _ -> true
  | Continue _, Continue _ -> true
  | If (exp1, then1, else1, _l1), If (exp2, then2, else2, _l2) -> 
      eq_exp exp1 exp2 (* && eq_block' then1 then2 && eq_block' else1 else2 *)
  | Switch (exp1, block1, stmts1, _l1), Switch (exp2, block2, stmts2, _l2) -> 
      eq_exp exp1 exp2 (* && eq_block' block1 block2 && eq_list (fun a b -> eq_stmt (a,af) (b,bf)) stmts1 stmts2 *)
  | Loop (block1, _l1, _con1, _br1), Loop (block2, _l2, _con2, _br2) -> true (* eq_block' block1 block2 *)
  | Block block1, Block block2 -> eq_block' block1 block2 (* Todo: is this needed? *)
  | TryFinally (tryBlock1, finallyBlock1, _l1), TryFinally (tryBlock2, finallyBlock2, _l2) -> assert false
      (* eq_block' tryBlock1 tryBlock2 && eq_block' finallyBlock1 finallyBlock2 *)
  | TryExcept (tryBlock1, exn1, exceptBlock1, _l1), TryExcept (tryBlock2, exn2, exceptBlock2, _l2) -> assert false
      (* eq_block' tryBlock1 tryBlock2 && eq_block' exceptBlock1 exceptBlock2 *)
  | _, _ -> false

let eq_stmt' ((a, af): stmt * fundec) ((b, bf): stmt * fundec) =
  (* catch Invalid Argument exception which is thrown by List.combine
  if the label lists are of different length *)
  try List.for_all (fun (x,y) -> eq_label x y) (List.combine a.labels b.labels) 
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
  | Assign (lv1, rv1), Assign (lv2, rv2) -> eq_lval lv1 lv2 && eq_exp rv1 rv2
  | Proc (None,f1,ars1), Proc (None,f2,ars2) -> eq_exp f1 f2 && eq_list eq_exp ars1 ars2
  | Proc (Some r1,f1,ars1), Proc (Some r2,f2,ars2) -> 
      eq_lval r1 r2 && eq_exp f1 f2 && eq_list eq_exp ars1 ars2
  | Entry f1, Entry f2 -> eq_varinfo' f1.svar f2.svar
  | Ret (None,fd1), Ret (None,fd2) -> eq_varinfo' fd1.svar fd2.svar
  | Ret (Some r1,fd1), Ret (Some r2,fd2) -> eq_exp r1 r2 && eq_varinfo' fd1.svar fd2.svar
  | Test (p1,b1), Test (p2,b2) -> eq_exp p1 p2 && b1 = b2
  | ASM _, ASM _ -> false
  | Skip, Skip -> true
  | VDecl v1, VDecl v2 -> eq_varinfo' v1 v2
  | SelfLoop, SelfLoop -> true
  | _ -> false

(* The order of the edges in the list is relevant. Therefor compare 
them one to one without sorting first*)
let eq_edge_list xs ys = eq_list eq_edge xs ys

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
    let compStdSetEntry2 ((_, fn2), (_, el2), (_,tn2)) = Node.equal fn2 fromNode && Node.equal tn2 toNode && eq_list eq_edge edgeList el2 in
    let inStd = StdS.exists compStdSetEntry2 stdSet in 
    let compDiffSetEntry2 ((_, fn2), el2, tn2) = Node.equal fn2 fromNode && Node.equal tn2 toNode && eq_list eq_edge edgeList el2 in
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
    let compStdSetEntry1 ((fn1,_), (el1,_), (tn1,_)) = Node.equal fn1 fromNode && Node.equal tn1 toNode && eq_list eq_edge edgeList el1 in
    let inStd = StdS.exists compStdSetEntry1 stdSet in 
    if inStd then "green" else "black" in
  let nodeColoring f node = "black" in
  let funs = FunDiffMap.fold (fun n e acc -> n :: acc) funDiff [] in
print_min_cfg_coloring (module Cfg) funs edgeColoring nodeColoring "cfg_1_diff.dot"

let print_rect_cfg (module Cfg : CfgForward) rectFunDiff =
  let edgeColoring f fromNode edgeList toNode = "black" in
  let nodeColoring f node =
    let sameRect, diffRect = FunDiffMap.find f rectFunDiff in
    if NodeNodeSet.exists (fun (_,n) -> Node.equal n node) sameRect then "green" 
    else if NodeSet.mem node diffRect then "red" else "black" in
  let funs = FunDiffMap.fold (fun n e acc -> n :: acc) rectFunDiff [] in
  print_min_cfg_coloring (module Cfg) funs edgeColoring nodeColoring "cfg_2_rect.dot"

let waitingList : (node * node) t = Queue.create ()

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
              (* Differentiate between a possibly duplicate Test(1,false) edge and a single occurence. In the first
              case the edge is directly added to the diff set to avoid undetected ambiguities during the recursive 
              call. *)
              let testFalseEdge edge = match edge with
                | Test (p,b) -> p = Cil.one && b = false
                | _ -> false in
              let posAmbigEdge edgeList = let findTestFalseEdge (ll,_) = testFalseEdge (snd (List.hd ll)) in
                let numDuplicates l = List.length (List.find_all findTestFalseEdge l) in
                testFalseEdge (List.hd edgeList) && (numDuplicates outList2 > 1 || numDuplicates outList1 > 1) in
              let (stdSet', diffSet') = if posAmbigEdge edgeList2 
                then (stdSet, DiffS.add ((fromNode1, fromNode2), edgeList2, toNode2) diffSet) 
                else findEquiv (edgeList2, toNode2) outList1 stdSet diffSet in
            iterOuts ls2' stdSet' diffSet' in
      compareNext (iterOuts outList2 stdSet diffSet) in
    
    let initSets = (StdS.empty, DiffS.empty) in
    let entryNode1, entryNode2 = (FunctionEntry fun1.svar, FunctionEntry fun2.svar) in
  Queue.push (entryNode1,entryNode2) waitingList; (compareNext initSets)

let reexamine f1 f2 stdSet diffSet (module Cfg2 : CfgForward) =
  let diffNodes = DiffS.fold (fun (_, _, n) acc -> NodeSet.add n acc) diffSet NodeSet.empty in
  let sameNodes = let fromStdSet = StdS.fold (fun (_, _, (n1, n2)) acc -> NodeNodeSet.add (n1,n2) acc) stdSet NodeNodeSet.empty in
    let notInDiff = NodeNodeSet.filter (fun (n1,n2) -> not (NodeSet.mem n2 diffNodes)) fromStdSet in
    NodeNodeSet.add (FunctionEntry f1.svar, FunctionEntry f2.svar) notInDiff in
  let rec dfs node (sameNodes, primDiffNodes, diffNodes) =
    let classify k (same, primDiff, diff) = match k with
      | Function d -> (same, primDiff, diff) (* leave out regular back-edge from return statement to function node  *)
      | _ -> if NodeSet.mem k primDiff || NodeSet.mem k diff then (same, primDiff, diff)
        else if NodeNodeSet.exists (fun (_,n) -> Node.equal n k) same then (NodeNodeSet.filter (fun (_,n) -> not (Node.equal n k)) same, NodeSet.add k primDiff, NodeSet.add k diff)
        else dfs k (same, primDiff, NodeSet.add k diff) in
    let succ = List.map (fun (_, n) -> n) (Cfg2.next node) in
    List.fold_right classify succ (sameNodes, primDiffNodes, diffNodes) in
  NodeSet.fold dfs diffNodes (sameNodes, diffNodes, diffNodes)

let compareFun (module Cfg1 : CfgForward) (module Cfg2 : CfgForward) fun1 fun2 =
  let stdSet, diffSet = compareCfgs (module Cfg1) (module Cfg2) fun1 fun2 in
  let matches, primDiff, diff = reexamine fun1 fun2 stdSet diffSet (module Cfg2) in
  let unchanged, primChanged, changed = NodeNodeSet.elements matches, NodeSet.elements primDiff, NodeSet.elements diff in
  (* printf "unchanged: ";
  List.iter (fun (n1,n2) -> printf "(%s,%s), " (node_to_string n1) (node_to_string n2)) unchanged;
  printf "\n";
    printf "primChanged: ";
  List.iter (fun n -> printf "%s, " (node_to_string n)) primChanged;
  printf "\n";
  printf "changed: ";
  List.iter (fun n -> printf "%s, " (node_to_string n)) changed;
  printf "\n"; *)
  unchanged, primChanged, changed

let eqF' (a: Cil.fundec) (module Cfg1 : MyCFG.CfgForward) (b: Cil.fundec) (module Cfg2 : MyCFG.CfgForward) =
  try
    let eq_header = eq_varinfo a.svar b.svar &&
    List.for_all (fun (x, y) -> eq_varinfo x y) (List.combine a.sformals b.sformals) &&
    List.for_all (fun (x, y) -> eq_varinfo x y) (List.combine a.slocals b.slocals) in
    (* eq_block (a.sbody, a) (b.sbody, b) *)
    let matches, primDiff, diff = compareFun (module Cfg1) (module Cfg2) a b in
    if not eq_header then (false, None) else if List.length diff = 0 then (true, None) else (false, Some {unchangedNodes = matches; primChangedNodes = primDiff; changedNodes = diff})
  with Invalid_argument _ -> (* One of the combines failed because the lists have differend length *)
    false, None

let eq_glob' (a: global) (module Cfg1 : MyCFG.CfgForward) (b: global) (module Cfg2 : MyCFG.CfgForward) = match a, b with
| GFun (f,_), GFun (g,_) -> eqF' f (module Cfg1) g (module Cfg2)
| GVar (x, init_x, _), GVar (y, init_y, _) -> eq_varinfo x y, None (* ignore the init_info - a changed init of a global will lead to a different start state *)
| GVarDecl (x, _), GVarDecl (y, _) -> eq_varinfo x y, None
| _ -> print_endline @@ "Not comparable: " ^ (Pretty.sprint ~width:100 (Cil.d_global () a)) ^ " and " ^ (Pretty.sprint ~width:100 (Cil.d_global () a)); false, None


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
          let (rectSame, rectPrimDiff, rectDiff) = reexamine f1 f2 stdSet diffSet (module Cfg2) in
          let entryNode2 = FunctionEntry f2.svar in
          aux funs1' funs2' (FunDiffMap.add entryNode2 (stdSet, diffSet) acc, FunDiffMap.add entryNode2 (rectSame, rectPrimDiff) accRect)
      | _, _ -> raise (Invalid_argument "Function to be compared not in both files") in
    aux (sort funs1) (sort funs2) (FunDiffMap.empty, FunDiffMap.empty) in
  
  assert (List.length funs1 = List.length funs2);
  print_min_cfg_diff_2 (module Cfg2) funDiff;
  print_min_cfg_diff_1 (module Cfg1) funDiff;
  print_rect_cfg (module Cfg2) funDiffRect;
  funDiff

(* Returns a list of changed functions *)
let compareCilFiles (oldAST: file) (newAST: file) oldCfgTbl newCfgTbl =
  let oldCfg, _ = MyCFG.getCFG oldAST in
  let newCfg, _ = MyCFG.getCFG newAST in
  let module OldCfg: MyCFG.CfgForward = struct let next = oldCfg end in
  let module NewCfg: MyCFG.CfgForward = struct let next = newCfg end in

  let addGlobal map global  =
    try
      GlobalMap.add (identifier_of_global global) global map
    with
      e -> map
  in
  let changes = empty_change_info () in
  let checkUnchanged map global =
    try
      let ident = identifier_of_global global in
      (try
         let old_global = GlobalMap.find ident map in
         (* Do a (recursive) equal comparision ignoring location information *)
         let identical, diff = eq_glob' old_global (module OldCfg) global (module NewCfg) in
         if identical
         then changes.unchanged <- global :: changes.unchanged
         else
          changes.changed <- {current = global; old = old_global; diff = diff} :: changes.changed
       with Not_found -> ())
    with e -> () (* Global was no variable or function, it does not belong into the map *)
  in
  let checkExists map global =
    let name = identifier_of_global global in
    GlobalMap.mem name map
  in
  (* Store a map from functionNames in the old file to the function definition*)
  let oldMap = Cil.foldGlobals oldAST addGlobal GlobalMap.empty in
  let newMap = Cil.foldGlobals newAST addGlobal GlobalMap.empty in
  (*  For each function in the new file, check whether a function with the same name
      already existed in the old version, and whether it is the same function. *)
  Cil.iterGlobals newAST
    (fun glob -> checkUnchanged oldMap glob);

  (* We check whether functions have been added or removed *)
  Cil.iterGlobals newAST (fun glob -> try if not (checkExists oldMap glob) then changes.added <- (glob::changes.added) with e -> ());
  Cil.iterGlobals oldAST (fun glob -> try if not (checkExists newMap glob) then changes.removed <- (glob::changes.removed) with e -> ());
  changes