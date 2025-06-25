(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the GNU Lesser General Public License as        *)
(*  published by the Free Software Foundation, either version 2.1 of   *)
(*  the License, or  (at your option) any later version.               *)
(*  This file is also distributed under the terms of the               *)
(*  INRIA Non-Commercial License Agreement.                            *)
(*                                                                     *)
(* *********************************************************************)

(** Pretty-printer for ClightCe *)

open Format
open Camlcoq
open PrintAST
open Ctypes
open Cop
open PrintCsyntax
open Clight
open PrintClight
open ClightCe

let precedence_cexpr = function
  | CE_expr _  -> (16,NA)
  | CE_and(e1,e2) -> (5,LtoR)
  | CE_or(e1,e2)  -> (4,LtoR)
  | CE_not e      -> (15, RtoL)

let rec cexpr p (prec,e) =
  let (prec',assoc) = precedence_cexpr e in
  let (prec1, prec2) =
    if assoc = LtoR
    then (prec', prec' + 1)
    else (prec' + 1, prec') in
  if prec' < prec
  then fprintf p "@[<hov 2>("
  else fprintf p "@[<hov 2>";
  begin match e with
  | CE_expr e -> expr p (0,e)
  | CE_and(e1,e2) -> fprintf p "%a@ && %a" cexpr (prec1,e1) cexpr (prec2,e2)
  | CE_or(e1,e2) -> fprintf p "%a@ || %a" cexpr (prec1,e1) cexpr (prec2,e2)
  | CE_not e1 -> fprintf p "!%a" cexpr (prec',e1) 
  end ;
  if prec' < prec then fprintf p ")@]" else fprintf p "@]"

let print_cexpr p e = cexpr p (0, e)

(* Statements (identical to Clight except for conditional expressions) *)

let rec print_stmt p s =
  match s with
  | Sskip ->
      fprintf p "/*skip*/;"
  | Sassign(e1, e2) ->
      fprintf p "@[<hv 2>%a =@ %a;@]" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "@[<hv 2>%s =@ %a;@]" (temp_name id) print_expr e2
  | Scall(None, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@]);@]"
                expr (15, e1)
                print_expr_list (true, el)
  | Scall(Some id, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@]);@]"
                (temp_name id)
                expr (15, e1)
                print_expr_list (true, el)
  | Sbuiltin(None, ef, tyargs, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@]);@]"
                (name_of_external ef)
                print_expr_list (true, el)
  | Sbuiltin(Some id, ef, tyargs, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]"
                (temp_name id)
                (name_of_external ef)
                print_expr_list (true, el)
  | Ssequence(Sskip, s2) ->
      print_stmt p s2
  | Ssequence(s1, Sskip) ->
      print_stmt p s1
  | Ssequence(s1, s2) ->
      fprintf p "%a@ %a" print_stmt s1 print_stmt s2
  | Sifthenelse(e, s1, Sskip) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>}@]"
              print_cexpr e
              print_stmt s1
  | Sifthenelse(e, Sskip, s2) ->
      fprintf p "@[<v 2>if (! %a) {@ %a@;<0 -2>}@]"
              cexpr (15, e)
              print_stmt s2
  | Sifthenelse(e, s1, s2) ->
      fprintf p "@[<v 2>if (%a) {@ %a@;<0 -2>} else {@ %a@;<0 -2>}@]"
              print_cexpr e
              print_stmt s1
              print_stmt s2
  | Sloop(s1, Sskip) ->
      fprintf p "@[<v 2>while (1) {@ %a@;<0 -2>}@]"
              print_stmt s1
  | Sloop(s1, s2) ->
      fprintf p "@[<v 2>for (@[<hv 0>;@ 1;@ %a) {@]@ %a@;<0 -2>}@]"
              print_stmt_for s2
              print_stmt s1
  | Sbreak ->
      fprintf p "break;"
  | Scontinue ->
      fprintf p "continue;"
  | Sswitch(e, cases) ->
      fprintf p "@[<v 2>switch (%a) {@ %a@;<0 -2>}@]"
              print_expr e
              print_cases cases
  | Sreturn None ->
      fprintf p "return;"
  | Sreturn (Some e) ->
      fprintf p "return %a;" print_expr e
  | Slabel(lbl, s1) ->
      fprintf p "%s:@ %a" (extern_atom lbl) print_stmt s1
  | Sgoto lbl ->
      fprintf p "goto %s;" (extern_atom lbl)

and print_cases p cases =
  match cases with
  | LSnil ->
      ()
  | LScons(lbl, Sskip, rem) ->
      fprintf p "%a:@ %a"
              print_case_label lbl
              print_cases rem
  | LScons(lbl, s, rem) ->
      fprintf p "@[<v 2>%a:@ %a@]@ %a"
              print_case_label lbl
              print_stmt s
              print_cases rem

and print_case_label p = function
  | None -> fprintf p "default"
  | Some lbl -> fprintf p "case %s" (Z.to_string lbl)

and print_stmt_for p s =
  match s with
  | Sskip ->
      fprintf p "(void)0"
  | Sassign(e1, e2) ->
      fprintf p "%a = %a" print_expr e1 print_expr e2
  | Sset(id, e2) ->
      fprintf p "%s = %a" (temp_name id) print_expr e2
  | Ssequence(Sskip, s2) ->
      print_stmt_for p s2
  | Ssequence(s1, s2) ->
      fprintf p "%a, %a" print_stmt_for s1 print_stmt_for s2
  | Scall(None, e1, el) ->
      fprintf p "@[<hv 2>%a@,(@[<hov 0>%a@])@]"
                expr (15, e1)
                print_expr_list (true, el)
  | Scall(Some id, e1, el) ->
      fprintf p "@[<hv 2>%s =@ %a@,(@[<hov 0>%a@])@]"
                (temp_name id)
                expr (15, e1)
                print_expr_list (true, el)
  | Sbuiltin(None, ef, tyargs, el) ->
      fprintf p "@[<hv 2>builtin %s@,(@[<hov 0>%a@]);@]"
                (name_of_external ef)
                print_expr_list (true, el)
  | Sbuiltin(Some id, ef, tyargs, el) ->
      fprintf p "@[<hv 2>%s =@ builtin %s@,(@[<hov 0>%a@]);@]"
                (temp_name id)
                (name_of_external ef)
                print_expr_list (true, el)
  | _ ->
      fprintf p "({ %a })" print_stmt s

(* There are two versions of Clight, Clight1 and Clight2, that differ
   only in the meaning of function parameters:
 - in Clight1, function parameters are variables
 - in Clight2, function parameters are temporaries.
*)

type clight_version = Clight1 | Clight2

let name_param = function Clight1 -> extern_atom | Clight2 -> temp_name

let print_function ver p id f =
  fprintf p "%s@ "
            (name_cdecl (name_function_parameters (name_param ver)
                                 (extern_atom id) f.fn_params f.fn_callconv)
                        f.fn_return);
  fprintf p "@[<v 2>{@ ";
  List.iter
    (fun (id, ty) ->
      fprintf p "%s;@ " (name_cdecl (extern_atom id) ty))
    f.fn_vars;
  List.iter
    (fun (id, ty) ->
      fprintf p "register %s;@ " (name_cdecl (temp_name id) ty))
    f.fn_temps;
  print_stmt p f.fn_body;
  fprintf p "@;<0 -2>}@]@ @ "

let print_fundef ver p id fd =
  match fd with
  | Ctypes.External(_, _, _, _) ->
      ()
  | Internal f ->
      print_function ver p id f

let type_of_function f =
  Tfunction ((type_of_params f.fn_params), f.fn_return, f.fn_callconv)


let print_fundecl p id fd =
  match fd with
  | Ctypes.External((AST.EF_external _ | AST.EF_runtime _ | AST.EF_malloc | AST.EF_free), args, res, cconv) ->
      fprintf p "extern %s;@ "
                (name_cdecl (extern_atom id) (Tfunction(args, res, cconv)))
  | Ctypes.External(_, _, _, _) ->
      ()
  | Internal f ->
      fprintf p "%s;@ "
                (name_cdecl (extern_atom id) (type_of_function f))

let print_globdef var p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundef var p id f
  | AST.Gvar v -> print_globvar p id v  (* from PrintCsyntax *)

let print_globdecl p (id, gd) =
  match gd with
  | AST.Gfun f -> print_fundecl p id f
  | AST.Gvar v -> ()

let print_program ver p prog =
  fprintf p "@[<v 0>";
  List.iter (declare_composite p) prog.prog_types;
  List.iter (define_composite p) prog.prog_types;
  List.iter (print_globdecl p) prog.prog_defs;
  List.iter (print_globdef ver p) prog.prog_defs;
  fprintf p "@]@."

let destination : string option ref = ref None

let print_if_gen ver prog =
  match !destination with
  | None -> ()
  | Some f ->
      let oc = open_out f in
      print_program ver (formatter_of_out_channel oc) prog;
      close_out oc

(* print_if is called from driver/Compiler.v between the SimplExpr
   and SimplLocals passes.  It receives Clight1 syntax. *)
let print_if prog = print_if_gen Clight1 prog


