(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Vernacexpr
open Synterp

let vernac_pperr_endline = CDebug.create ~name:"vernacinterp" ()


let jtmp = ref (`List [])
let taccount = ref 0

(* Timeout *)
let vernac_timeout ~timeout (f : 'a -> 'b) (x : 'a) : 'b =
  match Control.timeout timeout f x with
  | None -> Exninfo.iraise (Exninfo.capture CErrors.Timeout)
  | Some x -> x

(* Fail *)

(* Restoring the state is the caller's responsibility *)
let with_fail f : (Loc.t option * Pp.t, unit) result =
  try
    let _ = f () in
    Error ()
  with
  (* Fail Timeout is a common pattern so we need to support it. *)
  | e ->
    (* The error has to be printed in the failing state *)
    let _, info as exn = Exninfo.capture e in
    if CErrors.is_anomaly e && e != CErrors.Timeout then Exninfo.iraise exn;
    Ok (Loc.get_loc info, CErrors.iprint exn)

let real_error_loc ~cmdloc ~eloc =
  if Loc.finer eloc cmdloc then eloc
  else cmdloc

(* We restore the state always *)
let with_fail ~loc ~st f =
  let res = with_fail f in
  Vernacstate.Interp.invalidate_cache ();
  Vernacstate.unfreeze_full_state st;
  match res with
  | Error () ->
    CErrors.user_err (Pp.str "The command has not failed!")
  | Ok (eloc, msg) ->
    let loc = if !Synterp.test_mode then real_error_loc ~cmdloc:loc ~eloc else None in
    if not !Flags.quiet || !Synterp.test_mode
    then Feedback.msg_notice ?loc Pp.(str "The command has indeed failed with message:" ++ fnl () ++ msg)

let with_succeed ~st f =
  let () = ignore (f ()) in
  Vernacstate.Interp.invalidate_cache ();
  Vernacstate.unfreeze_full_state st;
  if not !Flags.quiet
  then Feedback.msg_notice Pp.(str "The command has succeeded and its effects have been reverted.")

let locate_if_not_already ?loc (e, info) =
  (e, Option.cata (Loc.add_loc info) info (real_error_loc ~cmdloc:loc ~eloc:(Loc.get_loc info)))

let interp_control_entry ~loc (f : control_entry) ~st
    (fn : st:Vernacstate.t -> Vernacstate.LemmaStack.t option * Declare.OblState.t NeList.t) =
  match f with
  | ControlFail { st = synterp_st } ->
    with_fail ~loc ~st (fun () -> Vernacstate.Synterp.unfreeze synterp_st; fn ~st);
    st.Vernacstate.interp.lemmas, st.Vernacstate.interp.program
  | ControlSucceed { st = synterp_st } ->
    with_succeed ~st (fun () -> Vernacstate.Synterp.unfreeze synterp_st; fn ~st);
    st.Vernacstate.interp.lemmas, st.Vernacstate.interp.program
  | ControlTimeout { remaining } ->
    vernac_timeout ~timeout:remaining (fun () -> fn ~st) ()
  | ControlTime { synterp_duration } ->
    let result = System.measure_duration (fun () -> fn ~st) () in
    let result = Result.map (fun (v,d) -> v, System.duration_add d synterp_duration) result in
    Feedback.msg_notice @@ System.fmt_transaction_result result;
    begin match result with
    | Ok (v,_) -> v
    | Error (exn, _) -> Exninfo.iraise exn
    end
  | ControlInstructions { synterp_instructions } ->
    let result = System.count_instructions (fun () -> fn ~st) () in
    let result = Result.map (fun (v,d) -> v, System.instruction_count_add d synterp_instructions) result in
    Feedback.msg_notice @@ System.fmt_instructions_result result;
    begin match result with
    | Ok (v,_) -> v
    | Error (exn, _) -> Exninfo.iraise exn
    end
  | ControlRedirect s ->
    Topfmt.with_output_to_file s (fun () -> fn ~st) ()

let module_include = ref ""

let get_id_from_module_entry mod_entry =
  let (_, mod_path, _, _) = mod_entry in
  Names.ModPath.to_string mod_path

let get_vernacexpr_kind expr =
  match expr with
  | VernacSynterp x ->
    let fl, k =
      match x with
      | EVernacBeginSection id -> true, "EVernacBeginSection"
      | EVernacEndSegment id -> true, "EVernacEndSegment"

      (* | EVernacDeclareModule (_, id, _,_ ) ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          localstack := ids :: !localstack *)
      | EVernacDefineModule (_, id, _, _, mod_sig, enl) ->
        let fl, k =
          let enln = List.length enl in
            if enln <> 0 then
              let onehd = List.hd enl in
              let incname = get_id_from_module_entry onehd in
              (* let incname = match mod_sig with
              | Enforce (_, mod_path, _, _) ->
                Names.ModPath.to_string mod_path
              | Check _ -> "" in  *)
              module_include := incname;
              true, "EVernacDefineModule_Include"
            else
              true, "EVernacDefineModule" in
        fl,k

      | EVernacDeclareModuleType (id, _, _,_,_) ->true, "EVernacDeclareModuleType"
      (* | EVernacExtend _ -> taccount := !taccount + 1; true, "EVernacExtend" *)

      | _ -> true, "" in fl, k

  | VernacSynPure pure_expr ->
      (* print_endline (get_synpure_vernac_expr pure_expr); *)

      match pure_expr with
      | VernacStartTheoremProof _ -> taccount := 0; Tacticals.tacinfo := (`List []); true, "VernacStartTheoremProof"
      | VernacInductive _ -> true, "VernacInductive"
      | VernacFixpoint _ -> true, "VernacFixpoint"
      | VernacDefinition _ -> true, "VernacDefinition"
      | VernacSyntacticDefinition _ -> true , "VernacSyntacticDefinition"
      | VernacAbort -> true , "VernacAbort"
      | VernacEndProof _ -> true, "VernacEndProof"
      (* | VernacProof _ -> true
      | VernacBullet _ -> true *)
      | _ -> false, ""


let get_idname_vernac_expr_gen expr =
  match expr with
  | VernacSynterp x ->
    let ids =
      match x with
      | EVernacBeginSection id ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          ids
      | EVernacEndSegment id ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          ids

      (* | EVernacDeclareModule (_, id, _,_ ) ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          localstack := ids :: !localstack *)
      | EVernacDefineModule (_, id, _, _, _, enl) ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          ids
      | EVernacDeclareModuleType (id, _, _,_,_) ->
        let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
        ids
      | _ -> "" in ids

  | VernacSynPure pure_expr ->
      match pure_expr with
      | VernacStartTheoremProof (k, proof_exprl) ->
        let ress =
          try
            let ((id, _), _) = List.hd proof_exprl in
            Pputils.pr_lident id |> Pp.string_of_ppcmds
          with _ -> "" in
          ress

      | VernacInductive (k, indl) ->
        let ress =
        try
          let (inductive_expr, notation_dl) = List.hd indl in
          let ((_, cumul_ind_decl), _, _, _) = inductive_expr in
          let namel = fst cumul_ind_decl in
          Pputils.pr_lident namel |> Pp.string_of_ppcmds
        with _ -> "" in
        ress
      | VernacFixpoint (d, fixl) ->
          let ress =
            try
              let x =  List.hd fixl in
              Pputils.pr_lident x.fname |> Pp.string_of_ppcmds
            with _ -> ""
          in ress

      | VernacDefinition (d, (namel, u), expr) ->
        Pputils.pr_lname namel |> Pp.string_of_ppcmds
      | _ -> ""

let localstack = ref []
let sectionstack = ref []
let sectionflag = ref false



let get_location_info expr =
  match expr with
  | VernacSynterp x ->
    let _ =
      match x with
      | EVernacBeginSection id ->
          sectionflag := true;
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          sectionstack := ids :: !sectionstack
      | EVernacEndSegment id ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          if !sectionflag then
            if List.hd !sectionstack = ids then
              let _ = sectionstack := List.tl !sectionstack in
              if List.length !sectionstack = 0 then sectionflag := false else ()
            else
              localstack := List.tl !localstack
          else
            localstack := List.tl !localstack

      (* | EVernacDeclareModule (_, id, _,_ ) ->
          let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
          localstack := ids :: !localstack *)
      | EVernacDefineModule (_, id, _, _, _, enl) ->
          let enln = List.length enl in
          if enln <> 0 then
            ()
          else
            let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
            localstack := ids :: !localstack
      | EVernacDeclareModuleType (id, _, _,_,_) ->
        let ids = Pputils.pr_lident id |> Pp.string_of_ppcmds in
        localstack := ids :: !localstack
      | _ -> () in ()
  | VernacSynPure _ -> ()

(* "locality" is the prefix "Local" attribute, while the "local" component
 * is the outdated/deprecated "Local" attribute of some vernacular commands
 * still parsed as the obsolete_locality grammar entry for retrocompatibility.
 * loc is the Loc.t of the vernacular command being interpreted. *)
let rec interp_expr ?loc ~atts ~st c =
  match c with

  (* The STM should handle that, but LOAD bypasses the STM... *)
  | VernacSynPure VernacAbortAll    -> CErrors.user_err (Pp.str "AbortAll cannot be used through the Load command")
  | VernacSynPure VernacRestart     -> CErrors.user_err (Pp.str "Restart cannot be used through the Load command")
  | VernacSynPure VernacUndo _      -> CErrors.user_err (Pp.str "Undo cannot be used through the Load command")
  | VernacSynPure VernacUndoTo _    -> CErrors.user_err (Pp.str "UndoTo cannot be used through the Load command")

  (* Resetting *)
  | VernacSynPure VernacResetName _  -> CErrors.anomaly (Pp.str "VernacResetName not handled by Stm.")
  | VernacSynPure VernacResetInitial -> CErrors.anomaly (Pp.str "VernacResetInitial not handled by Stm.")
  | VernacSynPure VernacBack _       -> CErrors.anomaly (Pp.str "VernacBack not handled by Stm.")

  | VernacSynterp EVernacLoad (verbosely, fname) ->
    Attributes.unsupported_attributes atts;
    vernac_load ~verbosely fname

  | v ->
    let fv = Vernacentries.translate_vernac ?loc ~atts v in
    let stack = st.Vernacstate.interp.lemmas in
    let program = st.Vernacstate.interp.program in
    let {Vernactypes.prog; proof; opaque_access=(); }, () = Vernactypes.run fv {
        prog=program;
        proof=stack;
        opaque_access=();
      }
    in
    proof, prog

and vernac_load ~verbosely entries =
  (* Note that no proof should be open here, so the state here is just token for now *)
  let st = Vernacstate.freeze_full_state () in
  let v_mod = if verbosely then Flags.verbosely else Flags.silently in
  let interp_entry (stack, pm) (CAst.{ loc; v = cmd }, synterp_st) =
    Vernacstate.Synterp.unfreeze synterp_st;
    let st = Vernacstate.{ synterp = synterp_st; interp = { st.interp with Interp.lemmas = stack; program = pm }} in
    v_mod (interp_control ~st) (CAst.make ?loc cmd)
  in
  let pm = st.Vernacstate.interp.program in
  let stack = st.Vernacstate.interp.lemmas in
  let stack, pm =
    Dumpglob.with_glob_output Dumpglob.NoGlob
    (fun () -> List.fold_left interp_entry (stack, pm) entries) ()
  in
  (* If Load left a proof open, we fail too. *)
  if Option.has_some stack then
    CErrors.user_err Pp.(str "Files processed by Load cannot leave open proofs.");
  stack, pm

and interp_control ~st ({ CAst.v = cmd; loc }) =

  let linenum = match loc with | None -> 0 | Some t -> t.line_nb in
  let _ = get_location_info cmd.expr in
  let _, kind = get_vernacexpr_kind cmd.expr in
  let _ = if kind <> "" then
    let idname = get_idname_vernac_expr_gen cmd.expr in
    let tmp_vernac_expr:(vernac_expr option) = match cmd.expr with
      | VernacSynPure pure_expr -> Some (VernacSynPure pure_expr)
      | _ -> None
    in

    let content =
      if kind = "EVernacDefineModule_Include" then
        !module_include
      else
        match tmp_vernac_expr with
        | Some x -> Ppvernac.pr_vernac_expr x |> Pp.string_of_ppcmds
        | None -> ""
    in
    let mpath = List.fold_left (fun acc x -> acc ^ x ^ ".") "" (List.rev !localstack) in

    let (resj:Yojson.Basic.t) = `Assoc [("idname", `String idname); ("scope", `String mpath) ;("kind", `String kind); ("line", `Int linenum); ("content", `String content); ("tactics_num", `Int !taccount)] in

    let _ = match !jtmp with
    | `List fields ->
        let newjson = fields @ [resj] in
         jtmp := (`List newjson);
    | _ -> ()
    in
    (* print_endline (Yojson.Basic.to_string !jtmp); *)
    (* save_info resj; *)
    ()
    else () in
  List.fold_right (fun flag fn -> interp_control_entry ~loc flag fn)
    cmd.control
    (fun ~st ->
       let before_univs = Global.universes () in
       let pstack, pm = with_generic_atts ~check:false cmd.attrs (fun ~atts ->
           interp_expr ?loc ~atts ~st cmd.expr)
       in
       let after_univs = Global.universes () in
       if before_univs == after_univs then pstack, pm
       else
         let f = Declare.Proof.update_sigma_univs after_univs in
         Option.map (Vernacstate.LemmaStack.map ~f) pstack, pm)
    ~st

(* XXX: This won't properly set the proof mode, as of today, it is
   controlled by the STM. Thus, we would need access information from
   the classifier. The proper fix is to move it to the STM, however,
   the way the proof mode is set there makes the task non trivial
   without a considerable amount of refactoring.
*)

(* Interpreting a possibly delayed proof *)
let interp_qed_delayed ~proof ~st pe =
  let stack = st.Vernacstate.interp.lemmas in
  let pm = st.Vernacstate.interp.program in
  let stack = Option.cata (fun stack -> snd @@ Vernacstate.LemmaStack.pop stack) None stack in
  let pm = NeList.map_head (fun pm -> match pe with
      | Admitted ->
        Declare.Proof.save_lemma_admitted_delayed ~pm ~proof
      | Proved (_,idopt) ->
        let pm = Declare.Proof.save_lemma_proved_delayed ~pm ~proof ~idopt in
        pm)
      pm
  in
  stack, pm

let interp_qed_delayed_control ~proof ~st ~control { CAst.loc; v=pe } =
  List.fold_right (fun flag fn -> interp_control_entry ~loc flag fn)
    control
    (fun ~st -> interp_qed_delayed ~proof ~st pe)
    ~st

(* General interp with management of state *)

(* Be careful with the cache here in case of an exception. *)
let interp_gen ~verbosely ~st ~interp_fn cmd =
  try
    let v_mod = if verbosely then Flags.verbosely else Flags.silently in
    let ontop = v_mod (interp_fn ~st) cmd in
    Vernacstate.Declare.set ontop [@ocaml.warning "-3"];
    Vernacstate.Interp.freeze_interp_state ()
  with exn ->
    let exn = Exninfo.capture exn in
    let exn = locate_if_not_already ?loc:cmd.CAst.loc exn in
    Vernacstate.Interp.invalidate_cache ();
    Exninfo.iraise exn

(* Regular interp *)
let interp ~intern ?(verbosely=true) ~st cmd =
  Vernacstate.unfreeze_full_state st;
  vernac_pperr_endline Pp.(fun () -> str "interpreting: " ++ Ppvernac.pr_vernac_expr cmd.CAst.v.expr);
  let entry = NewProfile.profile "synterp" (fun () -> Synterp.synterp_control ~intern cmd) () in
  let interp = NewProfile.profile "interp" (fun () -> interp_gen ~verbosely ~st ~interp_fn:interp_control entry) () in
  Vernacstate.{ synterp = Vernacstate.Synterp.freeze (); interp }

let interp_entry ?(verbosely=true) ~st entry =
  Vernacstate.unfreeze_full_state st;
  interp_gen ~verbosely ~st ~interp_fn:interp_control entry

module Intern = struct

  let fs_intern dp =
    match Loadpath.locate_absolute_library dp with
    | Ok file ->
      Feedback.feedback @@ Feedback.FileDependency (Some file, Names.DirPath.to_string dp);
      let res, provenance = Library.intern_from_file file in
      Result.iter (fun _ ->
          Feedback.feedback @@ Feedback.FileLoaded (Names.DirPath.to_string dp, file)) res;
      res, provenance
    | Error e ->
      Loadpath.Error.raise dp e
end

let fs_intern = Intern.fs_intern

let interp_qed_delayed_proof ~proof ~st ~control (CAst.{loc; v = pe } as e) : Vernacstate.Interp.t =
  (* Synterp duplication of control handling bites us here... *)
  let control = Synterp.add_default_timeout control in
  let control = List.map Synterp.synpure_control control in
  NewProfile.profile "interp-delayed-qed" (fun () ->
      interp_gen ~verbosely:false ~st
        ~interp_fn:(interp_qed_delayed_control ~proof ~control) e)
    ()
