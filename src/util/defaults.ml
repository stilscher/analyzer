(** Default values for [GobConfig]-style configuration. *)

open Prelude
open Printf
open List

(* TODO: add consistency checking *)

(** Main categories of configuration variables. *)
type category = Std             (** Parsing input, includes, standard stuff, etc. *)
              | Analyses        (** Analyses                                      *)
              | Semantics       (** Semantics                                     *)
              | Transformations (** Transformations                               *)
              | Experimental    (** Experimental features of analyses             *)
              | Debugging       (** Debugging, tracing, etc.                      *)
              | Warnings        (** Filtering warnings                            *)
              [@@deriving enum]

let all_categories = min_category -- max_category |> of_enum |> map (Option.get % category_of_enum)

(** Description strings for categories. *)
let catDescription = function
  | Std             -> "Standard options for configuring input/output"
  | Analyses        -> "Options for analyses"
  | Semantics       -> "Options for semantics"
  | Transformations -> "Options for transformations"
  | Experimental    -> "Experimental features"
  | Debugging       -> "Debugging options"
  | Warnings        -> "Filtering of warnings"

(** A place to store registered variables *)
let registrar = ref []

(** A function to register a variable *)
let reg (c:category) (n:string) (def:string) (desc:string) =
  registrar := (c,(n,(desc,def))) :: !registrar;
  GobConfig.(build_config := true; set_auto n def; build_config := false)

(** find all associations in the list *)
let rec assoc_all k = function
  | [] -> []
  | (x1,x2)::xs when k=x1 -> x2 :: assoc_all k xs
  | _::xs -> assoc_all k xs

(** Prints out all registered options with descriptions and defaults for one category. *)
let printCategory ch k =
  let print_one (n,(desc,def)) =
    fprintf ch "%-4s%-30s%s\n%-34sDefault value: \"%s\"\n\n" "" n desc "" def
  in
  catDescription k |> fprintf ch "%s:\n";
  assoc_all k !registrar |> rev |> iter print_one

(** Prints out all registered options. *)
let printAllCategories ch =
  iter (printCategory ch) all_categories

(* {4 category [Std]} *)
let _ = ()
      ; reg Std "outfile"         ""             "File to print output to."
      ; reg Std "includes"        "[]"           "List of directories to include."
      ; reg Std "kernel_includes" "[]"           "List of kernel directories to include."
      ; reg Std "custom_includes" "[]"           "List of custom directories to include."
      ; reg Std "custom_incl"     "''"           "Use custom includes"
      ; reg Std "custom_libc"     "false"        "Use goblints custom libc."
      ; reg Std "justcil"         "false"        "Just parse and output the CIL."
      ; reg Std "justcfg"         "false"        "Only output the CFG in cfg.dot ."
      ; reg Std "printstats"      "false"        "Outputs timing information."
      ; reg Std "verify"          "true"         "Verify that the solver reached a post-fixpoint. Beware that disabling this also disables output of warnings since post-processing of the results is done in the verification phase!"
      ; reg Std "mainfun"         "['main']"     "Sets the name of the main functions."
      ; reg Std "exitfun"         "[]"           "Sets the name of the cleanup functions."
      ; reg Std "otherfun"        "[]"           "Sets the name of other functions."
      ; reg Std "allglobs"        "false"        "Prints access information about all globals, not just races."
      ; reg Std "keepcpp"         "false"        "Keep the intermediate output of running the C preprocessor."
      ; reg Std "tempDir"         "''"           "Reuse temporary directory for preprocessed files."
      ; reg Std "cppflags"        "''"           "Pre-processing parameters."
      ; reg Std "kernel"          "false"        "For analyzing Linux Device Drivers."
      ; reg Std "dump_globs"      "false"        "Print out the global invariant."
      ; reg Std "result"          "'none'"       "Result style: none, fast_xml, json, mongo, pretty, json-messages."
      ; reg Std "warnstyle"       "'pretty'"     "Result style: legacy, pretty, or xml."
      ; reg Std "solver"          "'td3'"         "Picks the solver."
      ; reg Std "comparesolver"   "''"           "Picks another solver for comparison."
      ; reg Std "solverdiffs"     "false"        "Print out solver differences."
      ; reg Std "allfuns"         "false"        "Analyzes all the functions (not just beginning from main). This requires exp.earlyglobs!"
      ; reg Std "nonstatic"       "false"        "Analyzes all non-static functions."
      ; reg Std "colors"          "'auto'"       "Colored output (via ANSI escape codes). 'auto': enabled if stdout is a terminal (instead of a pipe); 'always', 'never'."
      ; reg Std "g2html"          "false"        "Run g2html.jar on the generated xml."
      ; reg Std "interact.out"    "'result'"     "The result directory in interactive mode."
      ; reg Std "interact.enabled" "false"       "Is interactive mode enabled."
      ; reg Std "interact.paused" "false"        "Start interactive in pause mode."
      ; reg Std "phases"          "[]"           "List of phases. Per-phase settings overwrite global ones."
      ; reg Std "save_run"        "''"           "Save the result of the solver, the current configuration and meta-data about the run to this directory (if set). The data can then be loaded (without solving again) to do post-processing like generating output in a different format or comparing results."
      ; reg Std "load_run"        "''"           "Load a saved run. See save_run."
      ; reg Std "compare_runs"    "[]"           "Load these saved runs and compare the results. Note that currently only two runs can be compared!"
      ; reg Std "warn_at"         "'post'"       "When to output warnings. Values: 'post' (default): after solving; 'never': no warnings; 'early': for debugging - outputs warnings already while solving (may lead to spurious warnings/asserts that would disappear after narrowing)."
      ; reg Std "gobview"         "false"        "Include additional information for Gobview (e.g., the Goblint warning messages) in the directory specified by 'save_run'."

(* {4 category [Analyses]} *)
let _ = ()
      ; reg Analyses "ana.activated"  "['expRelation','base','threadid','threadflag','threadreturn','escape','mutex','mallocWrapper']"  "Lists of activated analyses in this phase."
      ; reg Analyses "ana.path_sens"  "['OSEK','OSEK2','mutex','malloc_null','uninit']"  "List of path-sensitive analyses"
      (* apron adds itself to ana.path_sens such that there can be one defaults.ml both for the Apron and No-Apron configuration *)
      ; reg Analyses "ana.ctx_insens" "['OSEK2','stack_loc','stack_trace_set']"                      "List of context-insensitive analyses"
      ; reg Analyses "ana.cont.localclass" "false" "Analyzes classes defined in main Class."
      ; reg Analyses "ana.cont.class"      "''"    "Analyzes all the member functions of the class (CXX.json file required)."
      ; reg Analyses "ana.osek.oil"        "''"    "Oil file for the analyzed program"
      ; reg Analyses "ana.osek.defaults"   "true"  "Generate default definitions for TASK and ISR"
      (* ; reg Analyses "ana.osek.tramp"      "''"    "Resource-ID-headers for the analyzed program" *)
      ; reg Analyses "ana.osek.isrprefix"  "'function_of_'"    "Prefix added by the ISR macro"
      ; reg Analyses "ana.osek.taskprefix" "'function_of_'"    "Prefix added by the TASK macro"
      ; reg Analyses "ana.osek.isrsuffix"  "''"    "Suffix added by the ISR macro"
      ; reg Analyses "ana.osek.tasksuffix" "''"    "Suffix added by the TASK macro"
      ; reg Analyses "ana.osek.intrpts"    "false" "Enable constraints for interrupts."
      ; reg Analyses "ana.osek.check"      "false" "Check if (assumed) OSEK conventions are fullfilled."
      ; reg Analyses "ana.osek.names"      "[]"    "OSEK API function (re)names for the analysed program"
      ; reg Analyses "ana.osek.warnfiles"  "false" "Print all warning types to separate file"
      ; reg Analyses "ana.osek.safe_vars"  "[]"    "Suppress warnings on these vars"
      ; reg Analyses "ana.osek.safe_task"  "[]"    "Ignore accesses in these tasks"
      ; reg Analyses "ana.osek.safe_isr"   "[]"    "Ignore accesses in these isr"
      ; reg Analyses "ana.osek.flags"      "[]"    "List of global variables that are flags."
      ; reg Analyses "ana.osek.def_header" "true"  "Generate TASK/ISR macros with default structure"
      ; reg Analyses "ana.int.def_exc"      "true"  "Use IntDomain.DefExc: definite value/exclusion set."
      ; reg Analyses "ana.int.interval"    "false" "Use IntDomain.Interval32: (int64 * int64) option."
      ; reg Analyses "ana.int.enums"       "false" "Use IntDomain.Enums: Inclusion/Exclusion sets. Go to top on arithmetic operations (except for some easy cases, e.g. multiplication with 0). Joins on widen, i.e. precise integers as long as not derived from arithmetic expressions."
      ; reg Analyses "ana.int.congruence"  "false" "Use IntDomain.Congruence: (c, m) option, meaning congruent to c modulo m"
      ; reg Analyses "ana.int.refinement"   "'never'" "Use mutual refinement of integer domains. Either 'never', 'once' or 'fixpoint'"
      ; reg Analyses "ana.file.optimistic" "false" "Assume fopen never fails."
      ; reg Analyses "ana.spec.file"       ""      "Path to the specification file."
      ; reg Analyses "ana.pml.debug"       "true"  "Insert extra assertions into Promela code for debugging."
      ; reg Analyses "ana.arinc.assume_success" "true"    "Assume that all ARINC functions succeed (sets return code to NO_ERROR, otherwise invalidates it)."
      ; reg Analyses "ana.arinc.simplify"    "true" "Simplify the graph by merging functions consisting of the same edges and contracting call chains where functions just consist of another call."
      ; reg Analyses "ana.arinc.validate"    "true" "Validate the graph and output warnings for: call to functions without edges, multi-edge-calls for intermediate contexts, branching on unset return variables."
      ; reg Analyses "ana.arinc.export"    "true" "Generate dot graph and Promela for ARINC calls right after analysis. Result is saved in result/arinc.out either way."
      ; reg Analyses "ana.arinc.merge_globals" "false"  "Merge all global return code variables into one."
      ; reg Analyses "ana.opt.hashcons"        "true"  "Should we try to save memory and speed up equality by hashconsing?"
      ; reg Analyses "ana.opt.equal"       "true"  "First try physical equality (==) before {D,G,C}.equal (only done if hashcons is disabled since it basically does the same via its tags)."
      ; reg Analyses "ana.mutex.disjoint_types" "true" "Do not propagate basic type writes to all struct fields"
      ; reg Analyses "ana.sv-comp.enabled" "false" "SV-COMP mode"
      ; reg Analyses "ana.sv-comp.functions" "false" "Handle SV-COMP __VERIFIER* functions"
      ; reg Analyses "ana.specification"   "" "SV-COMP specification (path or string)"
      ; reg Analyses "ana.wp"              "false" "Weakest precondition feasibility analysis for SV-COMP violations"
      ; reg Analyses "ana.arrayoob"        "false"        "Array out of bounds check"
      ; reg Analyses "ana.apron.no-context" "false" "Ignore entire relation in function contexts."

(* {4 category [Semantics]} *)
let _ = ()
      (* TODO: split unknown_function to undefined_function and unknown_function_ptr *)
      ; reg Semantics "sem.unknown_function.spawn" "true"  "Unknown function call spawns reachable functions"
      ; reg Semantics "sem.unknown_function.invalidate.globals" "true"  "Unknown function call invalidates all globals"
      ; reg Semantics "sem.builtin_unreachable.dead_code" "false"  "__builtin_unreachable is assumed to be dead code"
      ; reg Semantics "sem.int.signed_overflow" "'assume_top'" "How to handle overflows of signed types. Values: 'assume_top' (default): Assume signed overflow results in a top value; 'assume_none': Assume program is free of signed overflows;  'assume_wraparound': Assume signed types wrap-around and two's complement representation of signed integers"


(* {4 category [Transformations]} *)
let _ = ()
      ; reg Transformations "trans.activated" "[]"  "Lists of activated transformations in this phase. Transformations happen after analyses."
      ; reg Transformations "trans.expeval.query_file_name" "''" "Path to the JSON file containing an expression evaluation query."

(* {4 category [Experimental]} *)
let _ = ()
      ; reg Experimental "exp.lower-constants"   "true"  "Use Cil.lowerConstants to simplify some constant? (assumes wrap-around for signed int)"
      (* TODO: priv subobject *)
      ; reg Experimental "exp.privatization"     "'protection-read'" "Which privatization to use? none/protection-old/mutex-oplus/mutex-meet/protection/protection-read/protection-vesal/mine/mine-nothread/mine-W/mine-W-noinit/lock/write/write+lock"
      ; reg Experimental "exp.priv-prec-dump"    "''"    "File to dump privatization precision data to."
      ; reg Experimental "exp.priv-distr-init"   "false"  "Distribute global initializations to all global invariants for more consistent widening dynamics."
      ; reg Experimental "exp.apron.privatization" "'mutex-meet'" "Which apron privatization to use? dummy/protection/protection-path/mutex-meet"
      ; reg Experimental "exp.cfgdot"            "false" "Output CFG to dot files"
      ; reg Experimental "exp.mincfg"            "false" "Try to minimize the number of CFG nodes."
      ; reg Experimental "exp.earlyglobs"        "false" "Side-effecting of globals right after initialization."
      ; reg Experimental "exp.failing-locks"     "false" "Takes the possible failing of locking operations into account."
      ; reg Experimental "exp.region-offsets"    "false" "Considers offsets for region accesses."
      ; reg Experimental "exp.unique"            "[]"    "For types that have only one value."
      ; reg Experimental "exp.forward"           "false" "Use implicit forward propagation instead of the demand driven approach."
      ; reg Experimental "exp.addr-context"      "false" "Ignore non-address values in function contexts."
      ; reg Experimental "exp.no-int-context"    "false" "Ignore all integer values in function contexts."
      ; reg Experimental "exp.no-interval-context" "false" "Ignore integer values of the Interval domain in function contexts."
      ; reg Experimental "exp.malloc.fail"       "false" "Consider the case where malloc or calloc fails."
      ; reg Experimental "exp.malloc.wrappers"   "['kmalloc','__kmalloc','usb_alloc_urb','__builtin_alloca','kzalloc']"  "Loads a list of known malloc wrapper functions." (* When something new that maps to malloc or calloc is added to libraryFunctions.ml, it should also be added here.*)
      ; reg Experimental "exp.volatiles_are_top" "true"  "volatile and extern keywords set variables permanently to top"
      ; reg Experimental "exp.single-threaded"   "false" "Ensures analyses that no threads are created."
      ; reg Experimental "exp.globs_are_top"     "false" "Set globals permanently to top."
      ; reg Experimental "exp.precious_globs"    "[]"    "Global variables that should be handled flow-sensitively when using earlyglobs."
      ; reg Experimental "exp.list-type"         "false" "Use a special abstract value for lists."
      ; reg Experimental "exp.g2html_path"       "'.'"   "Location of the g2html.jar file."
      ; reg Experimental "exp.extraspecials"     "[]"    "List of functions that must be analyzed as unknown extern functions"
      ; reg Experimental "exp.no-narrow"         "false" "Overwrite narrow a b = a"
      ; reg Experimental "exp.basic-blocks"      "false" "Only keep values for basic blocks instead of for every node. Should take longer but need less space."
      ; reg Experimental "exp.widen-context"     "false" "Do widening on contexts. Keeps a map of function to call state; enter will then return the widened local state for recursive calls."
      ; reg Experimental "exp.solver.td3.term"   "true"  "Should the td3 solver use the phased/terminating strategy?"
      ; reg Experimental "exp.solver.td3.side_widen" "'sides'" "When to widen in side. never: never widen, always: always widen, sides: widen if there are multiple side-effects from the same var resulting in a new value, cycle: widen if a called or a start var get destabilized, unstable_called: widen if any called var gets destabilized, unstable_self: widen if side-effected var gets destabilized."
      ; reg Experimental "exp.solver.td3.space"  "false" "Should the td3 solver only keep values at widening points?"
      ; reg Experimental "exp.solver.td3.space_cache" "true" "Should the td3-space solver cache values?"
      ; reg Experimental "exp.solver.td3.space_restore" "true" "Should the td3-space solver restore values for non-widening-points? Not needed for generating warnings, but needed for inspecting output!"
      ; reg Experimental "exp.solver.slr4.restart_count"   "1"     "How many times SLR4 is allowed to switch from restarting iteration to increasing iteration."
      ; reg Experimental "exp.fast_global_inits" "true" "Only generate one 'a[MyCFG.all_array_index_exp] = x' for all assignments a[...] = x for a global array a[n]."
      ; reg Experimental "exp.uninit-ptr-safe"   "false" "Assume that uninitialized stack-allocated pointers may only point to variables not in the program or null."
      ; reg Experimental "exp.ptr-arith-safe"    "false" "Assume that pointer arithmetic only yields safe addresses."
      ; reg Experimental "exp.witness.path" "'witness.graphml'" "Witness output path"
      ; reg Experimental "exp.witness.id" "'node'" "Which witness node IDs to use? node/enumerate"
      ; reg Experimental "exp.witness.invariant.nodes" "'all'" "Which witness nodes to add invariants to? all/loop_heads/none"
      ; reg Experimental "exp.witness.minimize"  "false" "Try to minimize the witness"
      ; reg Experimental "exp.witness.uncil"     "false" "Try to undo CIL control flow transformations in witness"
      ; reg Experimental "exp.witness.stack"     "true" "Construct stacktrace-based witness nodes"
      ; reg Experimental "exp.architecture"      "'64bit'" "Architecture for analysis, currently for witness"
      ; reg Experimental "exp.partition-arrays.enabled" "false" "Employ the partitioning array domain. When this is on, make sure to enable the expRelation analysis as well."
      ; reg Experimental "exp.partition-arrays.keep-expr" "'first'" "When using the partitioning which expression should be used for partitioning ('first', 'last')"
      ; reg Experimental "exp.partition-arrays.partition-by-const-on-return" "false" "When using the partitioning should arrays be considered partitioned according to a constant if a var in the expression used for partitioning goes out of scope?"
      ; reg Experimental "exp.partition-arrays.smart-join" "false" "When using the partitioning should the join of two arrays partitioned according to different expressions be partitioned as well if possible? If keep-expr is 'last' this behavior is enabled regardless of the flag value. Caution: Not always advantageous."
      ; reg Experimental "exp.incremental.mode"   "'off'" "Use incremental analysis in the TD3 solver. Values: off (default), incremental (analyze based on data from a previous commit or fresh if there is none), complete (discard loaded data and start fresh)."
      ; reg Experimental "exp.incremental.stable" "true"  "Reuse the stable set and selectively destabilize it."
      ; reg Experimental "exp.incremental.wpoint" "false" "Reuse the wpoint set."
      ; reg Experimental "exp.gcc_path"           "'/usr/bin/gcc'" "Location of gcc. Used to combine source files with cilly."

(* {4 category [Debugging]} *)
let _ = ()
      ; reg Debugging "dbg.debug"           "false" "Debug mode: for testing the analyzer itself."
      ; reg Debugging "dbg.verbose"         "false" "Prints some status information."
      ; reg Debugging "dbg.trace.context"   "false" "Also print the context of solver variables."
      ; reg Debugging "dbg.showtemps"       "false" "Shows CIL's temporary variables when printing the state."
      ; reg Debugging "dbg.uncalled"        "true" "Display uncalled functions."
      ; reg Debugging "dbg.dump"            ""      "Dumps the results to the given path"
      ; reg Debugging "dbg.cilout"          ""      "Where to dump cil output"
      ; reg Debugging "dbg.timeout"         "'0'"   "Stop solver after this time. 0 means no timeout. Supports optional units h, m, s. E.g. 1m6s = 01m06s = 66; 6h = 6*60*60."
      ; reg Debugging "dbg.solver-stats-interval"   "10" "Interval in seconds to print statistics while solving. Set to 0 to deactivate."
      ; reg Debugging "dbg.solver-signal"   "'sigusr1'" "Signal to print statistics while solving. Possible values: sigint (Ctrl+C), sigtstp (Ctrl+Z), sigquit (Ctrl+\\), sigusr1, sigusr2, sigalrm, sigprof etc. (see signal_of_string in goblintutil.ml)."
      ; reg Debugging "dbg.backtrace-signal" "'sigusr2'" "Signal to print a raw backtrace on stderr. Possible values: sigint (Ctrl+C), sigtstp (Ctrl+Z), sigquit (Ctrl+\\), sigusr1, sigusr2, sigalrm, sigprof etc. (see signal_of_string in goblintutil.ml)."
      ; reg Debugging "dbg.solver-progress" "false" "Used for debugging. Prints out a symbol on solving a rhs."
      ; reg Debugging "dbg.print_wpoints"   "false" "Print the widening points after solving (does not include the removed wpoints during solving by the slr solvers). Currently only implemented in: slr*, td3."
      ; reg Debugging "dbg.print_dead_code" "false" "Print information about dead code"
      ; reg Debugging "dbg.slice.on"        "false" "Turn slicer on or off."
      ; reg Debugging "dbg.slice.n"         "10"    "How deep function stack do we analyze."
      ; reg Debugging "dbg.limit.widen"     "0"     "Limit for number of widenings per node (0 = no limit)."
      ; reg Debugging "dbg.warn_with_context" "false" "Keep warnings for different contexts apart (currently only done for asserts)."
      ; reg Debugging "dbg.regression"      "false" "Only output warnings for assertions that have an unexpected result (no comment, comment FAIL, comment UNKNOWN)"
      ; reg Debugging "dbg.test.domain"     "false" "Test domain properties"
      ; reg Debugging "dbg.cilcfgdot"       "false" "Output dot files for CIL CFGs."
      ; reg Debugging "dbg.cfg.loop-clusters" "false" "Add loop SCC clusters to CFG .dot output."

(* {4 category [Warnings]} *)
let _ = ()
      ; reg Warnings "warn.assert"          "true"  "Assert messages"
      ; reg Warnings "warn.behavior"        "true"  "undefined behavior warnings"
      ; reg Warnings "warn.integer"         "true"  "integer (Overflow, Div_by_zero) warnings"
      ; reg Warnings "warn.cast"            "true"  "Cast (Type_mismatch(bug) warnings"
      ; reg Warnings "warn.race"            "true"  "Race warnings"
      ; reg Warnings "warn.deadcode"        "true"  "Dead code warnings"
      ; reg Warnings "warn.analyzer"        "true"  "Analyzer messages"
      ; reg Warnings "warn.unknown"         "true"  "Unknown (of string) warnings"
      ; reg Warnings "warn.error"           "true"  "Error severity messages"
      ; reg Warnings "warn.warning"         "true"  "Warning severity messages"
      ; reg Warnings "warn.info"            "true"  "Info severity messages"
      ; reg Warnings "warn.debug"           "true"  "Debug severity messages"
      ; reg Warnings "warn.success"         "true"  "Success severity messages"

let default_schema = {schema|
{ "id"              : "root"
, "type"            : "object"
, "required"        : ["outfile", "includes", "kernel_includes", "custom_includes", "custom_incl", "custom_libc", "justcil", "justcfg", "printstats", "verify", "mainfun", "exitfun", "otherfun", "allglobs", "keepcpp", "tempDir", "cppflags", "kernel", "dump_globs", "result", "warnstyle", "solver", "allfuns", "nonstatic", "colors", "g2html"]
, "additionalProps" : false
, "properties" :
  { "ana" :
    { "type"            : "object"
    , "additionalProps" : true
    , "required"        : []
    }
  , "sem"               : {}
  , "trans"             : {}
  , "phases"            : {}
  , "exp" :
    { "type"            : "object"
    , "additionalProps" : true
    , "required"        : []
    }
  , "dbg" :
    { "type"            : "object"
    , "additionalProps" : true
    , "required"        : []
    }
  , "questions" :
    { "file"            : ""
    }
  , "outfile"         : {}
  , "includes"        : {}
  , "kernel_includes" : {}
  , "custom_includes" : {}
  , "custom_incl"     : {}
  , "custom_libc"     : {}
  , "justcil"         : {}
  , "justcfg"         : {}
  , "printstats"      : {}
  , "verify"        : {}
  , "mainfun"         : {}
  , "exitfun"         : {}
  , "otherfun"        : {}
  , "allglobs"        : {}
  , "keepcpp"         : {}
  , "tempDir"         :
    { "type"            : "string"
    }
  , "cppflags"        : {}
  , "kernel"          : {}
  , "dump_globs"      : {}
  , "result"          :
    { "type"            : "string"
    }
  , "warnstyle"          :
    { "type"            : "string"
    }
  , "solver"          : {}
  , "comparesolver"   : {}
  , "solverdiffs"     : {}
  , "allfuns"         : {}
  , "nonstatic"       : {}
  , "colors"          : {}
  , "g2html"          : {}
  , "interact"        : {}
  , "save_run"        : {}
  , "load_run"        : {}
  , "compare_runs"    : {}
  , "warn_at"         : {}
  , "warn"              :
    { "type"            : "object"
    , "additionalProps" : true
    , "required"        : []
    }
  , "gobview"         : {}
  }
}|schema}

let _ =
  let v = Yojson.Safe.from_string default_schema in
  GobConfig.addenum_sch v
