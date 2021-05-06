(** Structures for the querying subsystem. *)

open Deriving.Cil
open Pretty

module GU = Goblintutil
module ID = IntDomain.Flattened
module LS = SetDomain.ToppedSet (Lval.CilLval) (struct let topname = "All" end)
module TS = SetDomain.ToppedSet (Basetype.CilType) (struct let topname = "All" end)
module PS = SetDomain.ToppedSet (Exp.LockingPattern) (struct let topname = "All" end)
module LPS = SetDomain.ToppedSet (Printable.Prod (Lval.CilLval) (Lval.CilLval)) (struct let topname = "All" end)

(* who uses this? hopefully it's not in the domain *)
module ES_r = SetDomain.ToppedSet (Exp.Exp) (struct let topname = "All" end)
module ES =
struct
  include ES_r
  include Printable.Std
  let bot = ES_r.top
  let top = ES_r.bot
  let leq x y = ES_r.leq y x
  let join = ES_r.meet
  let meet x y = ES_r.join x y
end

module VI = Lattice.Flat (Basetype.Variables) (struct
  let top_name = "Unknown line"
  let bot_name = "Unreachable line"
end)

module PartAccessResult = Access.PartAccessResult

type iterprevvar = int -> (MyCFG.node * Obj.t * int) -> MyARG.inline_edge -> unit
let iterprevvar_to_yojson _ = `Null
type itervar = int -> unit
let itervar_to_yojson _ = `Null

module SD = Basetype.Strings

type _ t =
  | EqualSet: exp -> ES.t t
  | MayPointTo: exp -> LS.t t
  | ReachableFrom: exp -> LS.t t
  | ReachableUkTypes: exp -> TS.t t
  | Regions: exp -> LS.t t
  | MayEscape: varinfo -> bool t
  | Priority: string -> ID.t t
  | MayBePublic: {global: varinfo; write: bool} -> bool t (* old behavior with write=false *)
  | MayBePublicWithout: {global: varinfo; write: bool; without_mutex: PreValueDomain.Addr.t} -> bool t
  | MustBeProtectedBy: {mutex: PreValueDomain.Addr.t; global: varinfo; write: bool} -> bool t
  | CurrentLockset: LS.t t
  | MustBeAtomic: bool t
  | MustBeSingleThreaded: bool t
  | MustBeUniqueThread: bool t
  | CurrentThreadId: VI.t t
  | MayBeThreadReturn: bool t
  | EvalFunvar: exp -> LS.t t
  | EvalInt: exp -> ID.t t
  | EvalStr: exp -> SD.t t
  | EvalLength: exp -> ID.t t (* length of an array or string *)
  | BlobSize: exp -> ID.t t (* size of a dynamically allocated `Blob pointed to by exp *)
  | PrintFullState: unit t
  | CondVars: exp -> ES.t t
  | PartAccess: {exp: exp; var_opt: varinfo option; write: bool} -> PartAccessResult.t t
  | IterPrevVars: iterprevvar -> unit t
  | IterVars: itervar -> unit t
  | MustBeEqual: exp * exp -> bool t (* are two expression known to must-equal ? *)
  | MayBeEqual: exp * exp -> bool t (* may two expressions be equal? *)
  | MayBeLess: exp * exp -> bool t (* may exp1 < exp2 ? *)
  | TheAnswerToLifeUniverseAndEverything: unit t (* TODO: unused, remove? *)
  | HeapVar: VI.t t
  | IsHeapVar: varinfo -> bool t
(* [@@deriving to_yojson] *)


type _ result =
  (* | Top: 'a result *)
  | Int: ID.t -> ID.t result
  | Str: SD.t -> SD.t result
  | LvalSet: LS.t -> LS.t result
  | ExprSet: ES.t -> ES.t result
  | ExpTriples: PS.t -> PS.t result
  | TypeSet: TS.t -> TS.t result
  | Varinfo: VI.t -> VI.t result
  | MustBool: bool -> bool result  (* true \leq false *)
  | MayBool: bool -> bool result   (* false \leq true *)
  | PartAccessResult: PartAccessResult.t -> PartAccessResult.t result
  | Unit: unit result
  (* | Bot: 'a result *)
(* [@@deriving to_yojson] *)

type ask = { f: 'a. 'a t -> 'a result }

(* module Result: Lattice.S with type t = result = *)
module Result =
struct
  include Printable.Std
  (* type t = result [@@deriving to_yojson] *)

  let name () = "query result domain"

  let bot (type a) (q: a t): a result =
    match q with
    (* Cannot group these GADTs... *)
    | EqualSet _ -> ExprSet (ES.bot ())
    | CondVars _ -> ExprSet (ES.bot ())
    | MayPointTo _ -> LvalSet (LS.bot ())
    | ReachableFrom _ -> LvalSet (LS.bot ())
    | Regions _ -> LvalSet (LS.bot ())
    | CurrentLockset -> LvalSet (LS.bot ())
    | EvalFunvar _ -> LvalSet (LS.bot ())
    | ReachableUkTypes _ -> TypeSet (TS.bot ())
    | MayEscape _ -> MayBool false
    | MayBePublic _ -> MayBool false
    | MayBePublicWithout _ -> MayBool false
    | MayBeThreadReturn -> MayBool false
    | MayBeEqual _ -> MayBool false
    | MayBeLess _ -> MayBool false
    | IsHeapVar _ -> MayBool false (* TODO: is must? *)
    | MustBeProtectedBy _ -> MustBool true
    | MustBeAtomic -> MustBool true
    | MustBeSingleThreaded -> MustBool true
    | MustBeUniqueThread -> MustBool true
    | MustBeEqual _ -> MustBool true
    | Priority _ -> Int (ID.bot ())
    | EvalInt _ -> Int (ID.bot ())
    | EvalLength _ -> Int (ID.bot ())
    | BlobSize _ -> Int (ID.bot ())
    | CurrentThreadId -> Varinfo (VI.bot ())
    | HeapVar -> Varinfo (VI.bot ())
    | EvalStr _ -> Str (SD.bot ())
    | PrintFullState -> Unit
    | IterPrevVars _ -> Unit
    | IterVars _ -> Unit
    | TheAnswerToLifeUniverseAndEverything -> Unit
    | PartAccess _ -> PartAccessResult (PartAccessResult.bot ())
  (* let is_bot x = x = Bot *)
  let bot_name = "Bottom"
  let top (type a) (q: a t): a result =
    match q with
    (* Cannot group these GADTs... *)
    | EqualSet _ -> ExprSet (ES.top ())
    | CondVars _ -> ExprSet (ES.top ())
    | MayPointTo _ -> LvalSet (LS.top ())
    | ReachableFrom _ -> LvalSet (LS.top ())
    | Regions _ -> LvalSet (LS.top ())
    | CurrentLockset -> LvalSet (LS.top ())
    | EvalFunvar _ -> LvalSet (LS.top ())
    | ReachableUkTypes _ -> TypeSet (TS.top ())
    | MayEscape _ -> MayBool true
    | MayBePublic _ -> MayBool true
    | MayBePublicWithout _ -> MayBool true
    | MayBeThreadReturn -> MayBool true
    | MayBeEqual _ -> MayBool true
    | MayBeLess _ -> MayBool true
    | IsHeapVar _ -> MayBool true (* TODO: is must? *)
    | MustBeProtectedBy _ -> MustBool false
    | MustBeAtomic -> MustBool false
    | MustBeSingleThreaded -> MustBool false
    | MustBeUniqueThread -> MustBool false
    | MustBeEqual _ -> MustBool false
    | Priority _ -> Int (ID.top ())
    | EvalInt _ -> Int (ID.top ())
    | EvalLength _ -> Int (ID.top ())
    | BlobSize _ -> Int (ID.top ())
    | CurrentThreadId -> Varinfo (VI.top ())
    | HeapVar -> Varinfo (VI.top ())
    | EvalStr _ -> Str (SD.top ())
    | PrintFullState -> Unit
    | IterPrevVars _ -> Unit
    | IterVars _ -> Unit
    | TheAnswerToLifeUniverseAndEverything -> Unit
    | PartAccess _ -> PartAccessResult (PartAccessResult.top ())
  (* let is_top x = x = Top *)
  let top_name = "Unknown"

  let equal (type a) (x: a result) (y: a result) =
    match (x, y) with
    (* | (Top, Top) -> true *)
    (* | (Bot, Bot) -> true *)
    | (Int x, Int y) -> ID.equal x y
    | (LvalSet x, LvalSet y) -> LS.equal x y
    | (ExprSet x, ExprSet y) -> ES.equal x y
    | (ExpTriples x, ExpTriples y) -> PS.equal x y
    | (TypeSet x, TypeSet y) -> TS.equal x y
    | (Varinfo x, Varinfo y) -> VI.equal x y
    | (MustBool x, MustBool y) -> Bool.equal x y
    | (MayBool x, MayBool y) -> Bool.equal x y
    | (PartAccessResult x, PartAccessResult y) -> PartAccessResult.equal x y
    | Unit, Unit -> true
    | _ -> false

  let hash (type a) (x: a result) =
    match x with
    | Int n -> ID.hash n
    | LvalSet n -> LS.hash n
    | ExprSet n -> ES.hash n
    | ExpTriples n -> PS.hash n
    | TypeSet n -> TS.hash n
    | Varinfo n -> VI.hash n
    | PartAccessResult n -> PartAccessResult.hash n
    (* MustBool and MayBool should work by the following *)
    | _ -> Hashtbl.hash x

  let compare (type a) (x: a result) (y: a result) =
    let constr_to_int (x: a result) = match x with
      (* | Bot -> 0 *)
      | Int _ -> 1
      | LvalSet _ -> 2
      | ExprSet _ -> 3
      | ExpTriples _ -> 4
      | Str _ -> 5
      (* | `IntSet _ -> 6 *)
      | TypeSet _ -> 7
      | Varinfo _ -> 8
      | MustBool _ -> 9
      | MayBool _ -> 10
      | PartAccessResult _ -> 11
      (* | Top -> 100 *)
      | Unit -> 12
    in match x,y with
    | Int x, Int y -> ID.compare x y
    | LvalSet x, LvalSet y -> LS.compare x y
    | ExprSet x, ExprSet y -> ES.compare x y
    | ExpTriples x, ExpTriples y -> PS.compare x y
    | TypeSet x, TypeSet y -> TS.compare x y
    | Varinfo x, Varinfo y -> VI.compare x y
    | MustBool x, MustBool y -> Bool.compare x y
    | MayBool x, MayBool y -> Bool.compare x y
    | PartAccessResult x, PartAccessResult y -> PartAccessResult.compare x y
    | _ -> Stdlib.compare (constr_to_int x) (constr_to_int y)

  let pretty_f s () (type a) (state: a result) =
    match state with
    | Int n ->  ID.pretty () n
    | Str s ->  SD.pretty () s
    | LvalSet n ->  LS.pretty () n
    | ExprSet n ->  ES.pretty () n
    | ExpTriples n ->  PS.pretty () n
    | TypeSet n -> TS.pretty () n
    | Varinfo n -> VI.pretty () n
    | MustBool n -> text (string_of_bool n)
    | MayBool n -> text (string_of_bool n)
    | PartAccessResult n -> PartAccessResult.pretty () n
    | Unit -> text "()"
    (* | Bot -> text bot_name *)
    (* | Top -> text top_name *)

  let short w (type a) (state: a result) =
    match state with
    | Int n ->  ID.short w n
    | Str s ->  SD.short w s
    | LvalSet n ->  LS.short w n
    | ExprSet n ->  ES.short w n
    | ExpTriples n ->  PS.short w n
    | TypeSet n -> TS.short w n
    | Varinfo n -> VI.short w n
    | MustBool n -> string_of_bool n
    | MayBool n -> string_of_bool n
    | PartAccessResult n -> PartAccessResult.short w n
    | Unit -> "()"
    (* | Bot -> bot_name *)
    (* | Top -> top_name *)

  let isSimple (type a) (x: a result) =
    match x with
    | Int n ->  ID.isSimple n
    | LvalSet n ->  LS.isSimple n
    | ExprSet n ->  ES.isSimple n
    | ExpTriples n ->  PS.isSimple n
    | TypeSet n -> TS.isSimple n
    | Varinfo n -> VI.isSimple n
    | PartAccessResult n -> PartAccessResult.isSimple n
    (* MustBool and MayBool should work by the following *)
    | _ -> true

  let pretty () x = pretty_f short () x
  let pretty_diff () (x,y) = dprintf "%s: %a not leq %a" (name ()) pretty x pretty y

  let leq (type a) (x: a result) (y: a result) =
    match (x,y) with
    (* | (_, Top) -> true *)
    (* | (Top, _) -> false *)
    (* | (Bot, _) -> true *)
    (* | (_, Bot) -> false *)
    | (Int x, Int y) -> ID.leq x y
    | (LvalSet x, LvalSet y) -> LS.leq x y
    | (ExprSet x, ExprSet y) -> ES.leq x y
    | (ExpTriples x, ExpTriples y) -> PS.leq x y
    | (TypeSet x, TypeSet y) -> TS.leq x y
    | (Varinfo x, Varinfo y) -> VI.leq x y
    (* TODO: should these be more like IntDomain.Booleans? *)
    | (MustBool x, MustBool y) -> x == y || x
    | (MayBool x, MayBool y) -> x == y || y
    | (PartAccessResult x, PartAccessResult y) -> PartAccessResult.leq x y
    | Unit, Unit -> true
    | _ -> false

  let join (type a) (x: a result) (y: a result): a result =
    try match (x,y) with
      (* | (Top, _) *)
      (* | (_, Top) -> Top *)
      (* | (Bot, x) *)
      (* | (x, Bot) -> x *)
      | (Int x, Int y) -> Int (ID.join x y)
      | (LvalSet x, LvalSet y) -> LvalSet (LS.join x y)
      | (ExprSet x, ExprSet y) -> ExprSet (ES.join x y)
      | (ExpTriples x, ExpTriples y) -> ExpTriples (PS.join x y)
      | (TypeSet x, TypeSet y) -> TypeSet (TS.join x y)
      | (Varinfo x, Varinfo y) -> Varinfo (VI.join x y)
      | (MustBool x, MustBool y) -> MustBool (x && y)
      | (MayBool x, MayBool y) -> MayBool (x || y)
      | (PartAccessResult x, PartAccessResult y) -> PartAccessResult (PartAccessResult.join x y)
      | Unit, Unit -> Unit
      | _ -> failwith "Result.top"
    with IntDomain.Unknown -> failwith "Result.top"

  let meet (type a) (x: a result) (y: a result): a result =
    try match (x,y) with
      (* | (Bot, _) *)
      (* | (_, Bot) -> Bot *)
      (* | (Top, x) *)
      (* | (x, Top) -> x *)
      | (Int x, Int y) -> Int (ID.meet x y)
      | (LvalSet x, LvalSet y) -> LvalSet (LS.meet x y)
      | (ExprSet x, ExprSet y) -> ExprSet (ES.meet x y)
      | (ExpTriples x, ExpTriples y) -> ExpTriples (PS.meet x y)
      | (TypeSet x, TypeSet y) -> TypeSet (TS.meet x y)
      | (Varinfo x, Varinfo y) -> Varinfo (VI.meet x y)
      | (MustBool x, MustBool y) -> MustBool (x || y)
      | (MayBool x, MayBool y) -> MayBool (x && y)
      | (PartAccessResult x, PartAccessResult y) -> PartAccessResult (PartAccessResult.meet x y)
      | Unit, Unit -> Unit

      | Str x, Str y -> Str (SD.meet x y)
      | MustBool _, MayBool _
      | MayBool _, MustBool _ -> failwith "Result.meet Bool"
      (* ocaml cannot refute these because all sets (although with different type)... *)
      | LvalSet _, TypeSet _
      | TypeSet _, LvalSet _
      | LvalSet _, ExprSet _
      | ExprSet _, LvalSet _
      | LvalSet _, ExpTriples _
      | ExpTriples _, LvalSet _
      | ExprSet _, TypeSet _
      | TypeSet _, ExprSet _
      | ExpTriples _, TypeSet _
      | TypeSet _, ExpTriples _
      | ExprSet _, ExpTriples _
      | ExpTriples _, ExprSet _ -> failwith "Result.meet Set"
      | _, _ -> .
      (* | _ -> failwith "Result.bot" *)
    with IntDomain.Error -> failwith "Result.bot"

  let widen (type a) (x: a result) (y: a result): a result =
    try match (x,y) with
      (* | (Top, _) *)
      (* | (_, Top) -> Top *)
      (* | (Bot, x) *)
      (* | (x, Bot) -> x *)
      | (Int x, Int y) -> Int (ID.widen x y)
      | (LvalSet x, LvalSet y) -> LvalSet (LS.widen x y)
      | (ExprSet x, ExprSet y) -> ExprSet (ES.widen x y)
      | (ExpTriples x, ExpTriples y) -> ExpTriples (PS.widen x y)
      | (TypeSet x, TypeSet y) -> TypeSet (TS.widen x y)
      | (Varinfo x, Varinfo y) -> Varinfo (VI.widen x y)
      | (MustBool x, MustBool y) -> MustBool (x && y)
      | (MayBool x, MayBool y) -> MustBool (x || y)
      | (PartAccessResult x, PartAccessResult y) -> PartAccessResult (PartAccessResult.widen x y)
      | Unit, Unit -> Unit
      | _ -> failwith "Result.top"
    with IntDomain.Unknown -> failwith "Result.top"

  let narrow (type a) (x: a result) (y: a result): a result =
    match (x,y) with
    | (Int x, Int y) -> Int (ID.narrow x y)
    | (LvalSet x, LvalSet y) -> LvalSet (LS.narrow x y)
    | (ExprSet x, ExprSet y) -> ExprSet (ES.narrow x y)
    | (ExpTriples x, ExpTriples y) -> ExpTriples (PS.narrow x y)
    | (TypeSet x, TypeSet y) -> TypeSet (TS.narrow x y)
    | (Varinfo x, Varinfo y) -> Varinfo (VI.narrow x y)
    | (MustBool x, MustBool y) -> MustBool (x || y)
    | (MayBool x, MayBool y) -> MayBool (x && y)
    | (PartAccessResult x, PartAccessResult y) -> PartAccessResult (PartAccessResult.narrow x y)
    | Unit, Unit -> Unit
    | (x,_) -> x

  let printXml f x = BatPrintf.fprintf f "<value>\n<data>%s\n</data>\n</value>\n" (Goblintutil.escape (short 800 x))
end
