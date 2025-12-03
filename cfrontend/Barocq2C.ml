open BinNums
open BinInt
open Ctypes

(** Pretty printing facilities for Barocq-compiled programs *)

type inline_status =
  | No_specifier
  | Inline
  | Always_inline
  
type fun_info = {
  f_inline : inline_status;
  f_static : bool;
}

let decl_fun : (AST.ident, fun_info) Hashtbl.t = Hashtbl.create 103

let fun_is_static a =
  try
    (Hashtbl.find decl_fun a).f_static
  with Not_found ->
    false

let fun_inline a =
  try
    (Hashtbl.find decl_fun a).f_inline
  with Not_found ->
    No_specifier

let fundef_attribs id : string =
  let inline =
    match fun_inline id with
    | No_specifier -> ""
    | Inline -> "inline "
    | Always_inline -> "inline __attribute__((always_inline)) "
  in
  Printf.sprintf "%s%s"
    (if fun_is_static id then "static " else "")
    inline

let fundecl_attribs id : string =
  if fun_is_static id then "static " else ""

(* Table that stores the constructor name of an int value for a given enum type. *)
(* This is a dirty hack for pretty-printing enum constructors without having to define them in the syntax. *)
let enum_constr_names : (AST. ident * coq_Z, AST.ident) Hashtbl.t = Hashtbl.create 10

let rec register_enum_members (eid: AST.ident) (m: members) (acc: coq_Z) : unit =
  match m with
  | [] -> ()
  | Member_plain (mid, Tint (I32, Signed, _)) :: m' ->
      Hashtbl.add enum_constr_names (eid, acc) mid;
      register_enum_members eid m' (Z.add acc (Zpos Coq_xH))
  | _ -> assert false

let rec fill_enum_constr_names (types: composite_definition list) : unit =
  match types with
  | [] -> ()
  | cd :: types' ->
      begin match cd with
      | Composite (id, Enum, m, _) -> register_enum_members id m Z0
      | _ -> ()
      end;
      fill_enum_constr_names types'
