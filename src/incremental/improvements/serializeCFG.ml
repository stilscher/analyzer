open Prelude
open MyCFG

let cfgFileName = "cfg.data"

let marshal obj fileName  =
  let objString = Marshal.to_string obj [] in
  let file = File.open_out fileName in
  Printf.fprintf file "%s" objString;
  flush file;
  close_out file;;

let load_cfg (src_file: string) =
  try
    Some (Serialize.unmarshal src_file)
  with e -> None

let save_cfg (cfg : ((Cil.location * edge) list * node) MyCFG.H.t) = marshal cfg cfgFileName
