(** Compute various information, including:
    - can a function fail (by having `Fail` in its body, or transitively calling
      a function which can fail - this is false for globals)
    - can a function diverge (by being recursive, containing a loop or
      transitively calling a function which can diverge)
    - does a function perform stateful operations (i.e., do we need a state to
      translate it) *)

open LlbcAst
open LlbcAstUtils
open ExpressionsUtils
open Charon.GAstUtils
open Errors

let log = Logging.funs_analysis_log

(** Various information about a function.

    Note that not all this information is used yet to adjust the extraction yet.
*)
type fun_info = {
  can_fail : bool;
      (* Not used yet: all the extracted functions use an error monad *)
  stateful : bool;
  can_diverge : bool;
  (* The function can diverge if:
     - it is recursive
     - it contains a loop
     - it calls a functions which can diverge
  *)
  is_rec : bool;
      (* [true] if the function is recursive (or in a mutually recursive group) *)
}
[@@deriving show]

(** Various information about a module's functions and trait methods. *)
type modules_funs_info = { infos : fun_info FunOrMethodId.Map.t }
[@@deriving show]

let lookup_fun_info (infos : modules_funs_info) (id : FunOrMethodId.id) :
    fun_info option =
  FunOrMethodId.Map.find_opt id infos.infos

let fun_or_method_id_of_fn_ptr (kind : fn_ptr_kind) : FunOrMethodId.id option =
  match kind with
  | Fun id -> Some (FunOrMethodId.Fun id)
  | TraitMethod (trait_ref, method_id) ->
      Some (FunOrMethodId.of_trait_method trait_ref method_id)

let lookup_fun_decl_info (infos : modules_funs_info) (id : FunDeclId.id) :
    fun_info option =
  lookup_fun_info infos (FunOrMethodId.Fun id)

let lookup_fn_ptr_info (infos : modules_funs_info) (kind : fn_ptr_kind) :
    fun_info option =
  Option.bind (fun_or_method_id_of_fn_ptr kind) (lookup_fun_info infos)

type fun_group_state = {
  funs : fun_decl list;
  mutable group_info : fun_info;
  is_global_decl_body : bool;
  group_has_builtin_info : bool;
  group_has_builtin : bool;
  direct_fun_deps : FunDeclId.id list;
  direct_trait_deps : (TraitDeclId.id * Types.TraitMethodId.id) list;
}

let analyze_module (m : crate) (funs_map : fun_decl FunDeclId.Map.t) :
    modules_funs_info =
  let fmt_env = Charon.Print.crate_to_fmt_env m in
  let name_matcher_ctx : Charon.NameMatcher.ctx =
    Charon.NameMatcher.ctx_from_crate m
  in
  let effectful_patterns : (string * Charon.NameMatcher.pattern * bool ref) list
      =
    List.map
      (fun pat -> (pat, Charon.NameMatcher.parse_pattern pat, ref false))
      !Config.effectful_patterns
  in
  let matches_effectful (name : Types.name) : bool =
    let matched = ref false in
    List.iter
      (fun (_pat_str, pat, used) ->
        if
          Charon.NameMatcher.match_name name_matcher_ctx
            ExtractName.default_match_config pat name
        then (
          used := true;
          matched := true))
      effectful_patterns;
    !matched
  in
  let fn_ptr_uses : (Meta.span * FunOrMethodId.id) list ref = ref [] in
  let dyn_trait_uses : (Meta.span * TraitDeclId.id) list ref = ref [] in
  let direct_effectful_error_funs : FunDeclId.TreeSet.t ref =
    ref FunDeclId.TreeSet.empty
  in
  let fun_groups : fun_group_state list ref = ref [] in
  let infos = ref { infos = FunOrMethodId.Map.empty } in
  let register_info (id : FunOrMethodId.id) (info : fun_info) : unit =
    assert (not (FunOrMethodId.Map.mem id !infos.infos));
    infos := { infos = FunOrMethodId.Map.add id info !infos.infos }
  in
  let set_info (id : FunOrMethodId.id) (info : fun_info) : unit =
    infos := { infos = FunOrMethodId.Map.add id info !infos.infos }
  in
  let register_fun_decl_info (id : FunDeclId.id) (info : fun_info) : unit =
    register_info (FunOrMethodId.Fun id) info
  in
  let register_trait_method_info (trait_decl_id : TraitDeclId.id)
      (method_id : Types.TraitMethodId.id) (stateful : bool) : unit =
    register_info
      (FunOrMethodId.Method (trait_decl_id, method_id))
      { can_fail = true; stateful; can_diverge = false; is_rec = false }
  in

  TraitDeclId.Map.iter
    (fun trait_decl_id (trait_decl : trait_decl) ->
      Types.TraitMethodId.Map.iter
        (fun method_id (bound_method : trait_method Types.binder) ->
          let stateful =
            effectful_patterns <> []
            && matches_effectful bound_method.binder_value.item_meta.name
          in
          register_trait_method_info trait_decl_id method_id stateful)
        trait_decl.methods)
    m.trait_decls;

  (* Analyze a group of mutually recursive functions.
   * As the functions can call each other, we compute the same information
   * for all of them (if one of the functions can fail, then all of them
   * can fail, etc.).
   *
   * We simply check whether the functions contains panic statements, loop statements,
   * recursive calls, etc. We use the previously computed information in case
   * of function calls.
   *)
  let analyze_fun_decls (fun_ids : FunDeclId.TreeSet.t) (d : fun_decl list) :
      fun_group_state =
    let can_fail = ref false in
    let stateful = ref false in
    let can_diverge = ref false in
    let is_rec = ref false in
    let group_has_builtin_info = ref false in
    let group_has_builtin = ref false in
    let direct_fun_deps : FunDeclId.id list ref = ref [] in
    let direct_trait_deps : (TraitDeclId.id * Types.TraitMethodId.id) list ref =
      ref []
    in

    (* We have some specialized knowledge of some library functions; we don't
       have any more custom treatment than this, and these functions can be modeled
       suitably in the backend libraries, rather than special-casing for them all the
       way. *)
    let get_builtin_info (f : fun_decl) : ExtractBuiltin.effect_info option =
      let open ExtractBuiltin in
      NameMatcherMap.find_opt name_matcher_ctx f.item_meta.name
        (builtin_fun_effects_map ())
    in

    let dyn_ty_visitor =
      object
        inherit [_] iter_statement as super

        method! visit_TDynTrait env ({ Types.binder } as dp) =
          List.iter
            (fun (c : Types.trait_param) ->
              dyn_trait_uses :=
                (env, c.trait.binder_value.id) :: !dyn_trait_uses)
            binder.binder_params.trait_clauses;
          super#visit_TDynTrait env dp

        method! visit_trait_ref env (tr : Types.trait_ref) =
          (match tr.kind with
          | Dyn ->
              dyn_trait_uses := (env, tr.trait_decl_ref.id) :: !dyn_trait_uses
          | _ -> ());
          super#visit_trait_ref env tr
      end
    in

    (* JP: Why not use a reduce visitor here with a tuple of the values to be
       computed? *)
    let visit_fun (f : fun_decl) : unit =
      [%ltrace
        "Analyzing fun:\n"
        ^ Charon.Print.name_to_string fmt_env f.item_meta.name];
      let obj =
        object (self)
          inherit [_] iter_statement as super
          method may_fail b = can_fail := !can_fail || b
          method maybe_stateful b = stateful := !stateful || b
          method! visit_statement _ st = super#visit_statement st.span st

          (* Custom function called by hand, this isn't visit_fun_decl_id! *)
          method visit_fid span id =
            if FunDeclId.TreeSet.mem id fun_ids then (
              can_diverge := true;
              is_rec := true)
            else (
              direct_fun_deps := id :: !direct_fun_deps;
              let info = lookup_fun_decl_info !infos id in
              let info =
                [%unwrap_opt_span] (Some span) info
                  "The function called here is missing from the crate \
                   (probably because of a previous error, or because of the \
                   use of --exclude)"
              in
              self#may_fail info.can_fail;
              stateful := !stateful || info.stateful;
              can_diverge := !can_diverge || info.can_diverge)

          method! visit_TDynTrait env ({ Types.binder } as dp) =
            if effectful_patterns <> [] then
              List.iter
                (fun (c : Types.trait_param) ->
                  dyn_trait_uses :=
                    (env, c.trait.binder_value.id) :: !dyn_trait_uses)
                binder.binder_params.trait_clauses;
            super#visit_TDynTrait env dp

          method! visit_trait_ref env (tr : Types.trait_ref) =
            (if effectful_patterns <> [] then
               match tr.kind with
               | Dyn ->
                   dyn_trait_uses :=
                     (env, tr.trait_decl_ref.id) :: !dyn_trait_uses
               | _ -> ());
            super#visit_trait_ref env tr

          method! visit_constant_expr_kind env ck =
            (if effectful_patterns <> [] then
               match ck with
               | CFnDef (ptr : Types.fn_ptr) ->
                   let id =
                     match ptr.Types.kind with
                     | Fun id -> FunOrMethodId.Fun id
                     | TraitMethod (trait_ref, method_id) ->
                         FunOrMethodId.of_trait_method trait_ref method_id
                   in
                   fn_ptr_uses := (env, id) :: !fn_ptr_uses
               | _ -> ());
            super#visit_constant_expr_kind env ck

          method! visit_Assert env a =
            self#may_fail true;
            super#visit_Assert env a

          method! visit_rvalue env rv =
            (match rv with
            | Use (Constant { kind = CTraitConst _; _ }, _) ->
                (* We consider that trait constants can fail, similarly to
                   trait methods. *)
                self#may_fail true
            | Use _
            | RvRef ({ kind = PlaceLocal _ | PlaceProjection _; _ }, _, _)
            | Discriminant _ | Aggregate _ | NullaryOp _ | RawPtr _ | Repeat _
              -> ()
            | RvRef ({ kind = PlaceGlobal gref; _ }, _, _) -> (
                (* A reference to a global: propagate can_fail.

                   Check the builtin globals map first (for opaque builtins like
                   [u32::MAX]), then fall back to the initializer function's info. *)
                let global = GlobalDeclId.Map.find gref.id m.global_decls in
                let open ExtractBuiltin in
                let builtin_info =
                  NameMatcherMap.find_opt name_matcher_ctx global.item_meta.name
                    (builtin_globals_map ())
                in
                match builtin_info with
                | Some info -> self#may_fail info.can_fail
                | None -> (
                    (* Globals without initializers are constants *)
                    match init_fun_id_of_global global with
                    | Some fid -> self#visit_fid env fid
                    | None -> ()))
            | UnaryOp (uop, _) -> can_fail := unop_can_fail uop || !can_fail
            | BinaryOp (bop, _, _) ->
                can_fail := binop_can_fail bop || !can_fail);
            super#visit_rvalue env rv

          method! visit_Call env call dest on_unwind =
            (match call.func with
            | FnOpDynamic _ ->
                (* Ignoring this: we lookup the called function upon creating
                   the closure / function pointer *)
                ()
            | FnOpRegular func -> (
                match func.kind with
                | Fun id -> self#visit_fid env id
                | TraitMethod (trait_ref, method_id) ->
                    direct_trait_deps :=
                      (trait_ref.trait_decl_ref.id, method_id)
                      :: !direct_trait_deps;
                    (if effectful_patterns <> [] then
                       match
                         lookup_fun_info !infos
                           (FunOrMethodId.of_trait_method trait_ref method_id)
                       with
                       | Some info -> stateful := !stateful || info.stateful
                       | None -> ());
                    (* We consider trait functions can fail and cannot diverge.
                       TODO: this may cause issues if we use a fuel parameter.
                    *)
                    can_fail := true));
            super#visit_Call env call dest on_unwind

          method! visit_Panic env =
            self#may_fail true;
            super#visit_Panic env

          method! visit_Loop env loop =
            can_diverge := true;
            super#visit_Loop env loop
        end
      in
      let builtin_info = get_builtin_info f in
      let has_builtin_info = builtin_info <> None in
      let is_builtin =
        has_builtin_info
        || ExtractBuiltin.NameMatcherMap.mem name_matcher_ctx f.item_meta.name
             (ExtractBuiltin.builtin_funs_map ())
      in
      group_has_builtin_info := !group_has_builtin_info || has_builtin_info;
      group_has_builtin := !group_has_builtin || is_builtin;
      if effectful_patterns <> [] then (
        dyn_ty_visitor#visit_generic_params f.item_meta.span f.generics;
        List.iter (dyn_ty_visitor#visit_ty f.item_meta.span) f.signature.inputs;
        dyn_ty_visitor#visit_ty f.item_meta.span f.signature.output;
        if matches_effectful f.item_meta.name then (
          let name_str = Charon.Print.name_to_string fmt_env f.item_meta.name in
          if is_builtin then (
            direct_effectful_error_funs :=
              FunDeclId.TreeSet.add f.def_id !direct_effectful_error_funs;
            [%save_error] f.item_meta.span
              ("Builtin function '" ^ name_str
             ^ "' cannot be marked `-effectful`"));
          if fun_decl_is_global_initializer f then (
            direct_effectful_error_funs :=
              FunDeclId.TreeSet.add f.def_id !direct_effectful_error_funs;
            [%save_error] f.item_meta.span
              ("Global initializer '" ^ name_str
             ^ "' cannot be marked `-effectful`"));
          obj#maybe_stateful true));
      match f.body with
      | StructuredBody body -> obj#visit_block body.body.span body.body
      | TargetDispatchBody targets ->
          (* get_target can fail, and so can each target function *)
          obj#may_fail true;
          (* Also propagate effects from the target implementations *)
          List.iter
            (fun ((_target_name : string), (fdr : Types.fun_decl_ref)) ->
              obj#visit_fid f.item_meta.span fdr.id)
            targets
      | _ ->
          let info_can_fail =
            match builtin_info with
            | None -> true
            | Some { can_fail } -> can_fail
          in
          obj#may_fail info_can_fail
    in
    List.iter visit_fun d;
    (* We need to know if the declaration group contains a global - note that
     * groups containing globals contain exactly one declaration *)
    let is_global_decl_body = List.exists fun_decl_is_global_initializer d in
    [%cassert] (List.hd d).item_meta.span
      ((not is_global_decl_body) || List.length d = 1)
      "This global definition is in a group of mutually recursive definitions";
    [%cassert] (List.hd d).item_meta.span
      ((not !group_has_builtin_info) || List.length d = 1)
      "This builtin function belongs to a group of mutually recursive \
       definitions";
    (* We ignore on purpose functions that cannot fail and consider they *can*
     * fail: the result of the analysis is not used yet to adjust the translation
     * so that the functions which syntactically can't fail don't use an error monad.
     * However, we do keep the result of the analysis for global bodies and for
     * builtin functions which are marked as non-fallible.
     *)
    can_fail :=
      if is_global_decl_body then !can_fail
      else if !group_has_builtin_info then !can_fail || !stateful
      else true;
    let group_info =
      {
        can_fail = !can_fail;
        stateful = !stateful;
        can_diverge = !can_diverge;
        is_rec = !is_rec;
      }
    in
    {
      funs = d;
      group_info;
      is_global_decl_body;
      group_has_builtin_info = !group_has_builtin_info;
      group_has_builtin = !group_has_builtin;
      direct_fun_deps = !direct_fun_deps;
      direct_trait_deps = !direct_trait_deps;
    }
  in

  let analyze_fun_decl_group (funs : fun_decl_id list) : unit =
    (* Retrieve the function declarations *)
    let funs =
      List.map
        (fun id ->
          [%silent_unwrap_opt_span] None (FunDeclId.Map.find_opt id funs_map))
        funs
    in
    let fun_ids = List.map (fun (d : fun_decl) -> d.def_id) funs in
    let fun_ids = FunDeclId.TreeSet.of_list fun_ids in
    let group = analyze_fun_decls fun_ids funs in
    if effectful_patterns <> [] then fun_groups := group :: !fun_groups;
    List.iter
      (fun (f : fun_decl) -> register_fun_decl_info f.def_id group.group_info)
      funs
  in

  let rec analyze_decl_groups (decls : declaration_group list) : unit =
    match decls with
    | [] -> ()
    | (TypeGroup _ | TraitDeclGroup _ | TraitImplGroup _ | GlobalGroup _)
      :: decls' -> analyze_decl_groups decls'
    | FunGroup decl :: decls' ->
        (try analyze_fun_decl_group (g_declaration_group_to_list decl)
         with CFailure error ->
           let decls = Charon.GAstUtils.g_declaration_group_to_list decl in
           let decl_id_to_string (id : FunDeclId.id) : string =
             match FunDeclId.Map.find_opt id m.fun_decls with
             | None -> show_fun_decl_id id
             | Some d ->
                 Charon.Print.name_to_string fmt_env d.item_meta.name
                 ^ " ("
                 ^ span_to_string d.item_meta.span
                 ^ ")"
           in
           let decls = List.map decl_id_to_string decls in
           let decls = String.concat "\n" decls in
           [%save_error_opt_span] error.span
             ("Encountered an error when analyzing the following function \
               declaration group:\n" ^ decls ^ "\n\nInitial error:\n"
            ^ error.msg));
        analyze_decl_groups decls'
    | MixedGroup ids :: _ ->
        [%save_error_opt_span] None
          ("Mixed declaration groups (which contain both type and function \
            declarations or functions and traits, for instance) are not \
            supported yet: ["
          ^ String.concat ", "
              (List.map Charon.Print.item_id_to_string
                 (Charon.GAstUtils.g_declaration_group_to_list ids))
          ^ "]")
  in

  analyze_decl_groups (Option.get m.declarations);

  if effectful_patterns <> [] then (
    let fun_groups = List.rev !fun_groups in
    let fun_group_by_id =
      List.fold_left
        (fun acc (g : fun_group_state) ->
          List.fold_left
            (fun acc (f : fun_decl) -> FunDeclId.TreeMap.add f.def_id g acc)
            acc g.funs)
        FunDeclId.TreeMap.empty fun_groups
    in
    let is_fun_stateful (id : FunDeclId.id) : bool =
      match lookup_fun_decl_info !infos id with
      | Some info -> info.stateful
      | None -> false
    in
    let is_trait_method_stateful (td_id : TraitDeclId.id)
        (mid : Types.TraitMethodId.id) : bool =
      match lookup_fun_info !infos (FunOrMethodId.Method (td_id, mid)) with
      | Some info -> info.stateful
      | None -> false
    in
    let mark_group_stateful (g : fun_group_state) : bool =
      if g.group_info.stateful then false
      else
        let can_fail =
          if g.is_global_decl_body then g.group_info.can_fail
          else if g.group_has_builtin_info then true
          else g.group_info.can_fail
        in
        let info = { g.group_info with stateful = true; can_fail } in
        g.group_info <- info;
        List.iter
          (fun (f : fun_decl) -> set_info (FunOrMethodId.Fun f.def_id) info)
          g.funs;
        true
    in
    let mark_fun_id_stateful (fid : FunDeclId.id) : bool =
      match FunDeclId.TreeMap.find_opt fid fun_group_by_id with
      | Some g -> mark_group_stateful g
      | None -> false
    in
    let mark_trait_method_stateful (td_id : TraitDeclId.id)
        (mid : Types.TraitMethodId.id) : bool =
      let key = FunOrMethodId.Method (td_id, mid) in
      match lookup_fun_info !infos key with
      | Some info when info.stateful -> false
      | Some info ->
          set_info key { info with stateful = true };
          true
      | None ->
          set_info key
            {
              can_fail = true;
              stateful = true;
              can_diverge = false;
              is_rec = false;
            };
          true
    in

    (* Iterate statefulness propagation to a fixed point across functions,
       trait declarations (default methods), and trait implementations. *)
    let changed = ref true in
    while !changed do
      changed := false;
      List.iter
        (fun (g : fun_group_state) ->
          if
            (not g.group_info.stateful)
            && (List.exists is_fun_stateful g.direct_fun_deps
               || List.exists
                    (fun (td_id, mid) -> is_trait_method_stateful td_id mid)
                    g.direct_trait_deps)
          then if mark_group_stateful g then changed := true)
        fun_groups;
      TraitDeclId.Map.iter
        (fun td_id (trait_decl : trait_decl) ->
          Types.TraitMethodId.Map.iter
            (fun mid (bound_method : trait_method Types.binder) ->
              match bound_method.binder_value.default with
              | Some fref ->
                  if is_fun_stateful fref.id then
                    if mark_trait_method_stateful td_id mid then changed := true;
                  if is_trait_method_stateful td_id mid then
                    if mark_fun_id_stateful fref.id then changed := true
              | None -> ())
            trait_decl.methods)
        m.trait_decls;
      TraitImplId.Map.iter
        (fun _ (trait_impl : trait_impl) ->
          let td_id = trait_impl.impl_trait.id in
          Types.TraitMethodId.Map.iter
            (fun mid (fref_binder : Types.fun_decl_ref Types.binder) ->
              let fid = fref_binder.binder_value.id in
              if is_fun_stateful fid then
                if mark_trait_method_stateful td_id mid then changed := true;
              if is_trait_method_stateful td_id mid then
                if mark_fun_id_stateful fid then changed := true)
            trait_impl.methods)
        m.trait_impls
    done;

    (* Warn on `-effectful` patterns that matched no function or trait method *)
    List.iter
      (fun (pat_str, _pat, used) ->
        if not !used then
          [%warn_opt_span] None
            ("`-effectful` pattern `" ^ pat_str
           ^ "` did not match any function or trait method declaration"))
      effectful_patterns;

    (* Check that no global initializer or builtin function became stateful *)
    List.iter
      (fun (g : fun_group_state) ->
        if g.group_info.stateful then (
          if g.is_global_decl_body then
            List.iter
              (fun (f : fun_decl) ->
                if
                  fun_decl_is_global_initializer f
                  && not
                       (FunDeclId.TreeSet.mem f.def_id
                          !direct_effectful_error_funs)
                then
                  [%save_error] f.item_meta.span
                    "Global definition containing a stateful call in its body")
              g.funs;
          if g.group_has_builtin then
            List.iter
              (fun (f : fun_decl) ->
                if
                  not
                    (FunDeclId.TreeSet.mem f.def_id
                       !direct_effectful_error_funs)
                then
                  let name_str =
                    Charon.Print.name_to_string fmt_env f.item_meta.name
                  in
                  [%save_error] f.item_meta.span
                    ("Builtin function '" ^ name_str ^ "' cannot be stateful"))
              g.funs))
      fun_groups;

    (* Index a representative local trait impl span per trait decl to give clear
       user-facing spans when a builtin or external trait (e.g. a closure) becomes
       stateful. *)
    let stateful_impl_spans : Meta.span TraitDeclId.TreeMap.t ref =
      ref TraitDeclId.TreeMap.empty
    in
    TraitImplId.Map.iter
      (fun _ (trait_impl : trait_impl) ->
        let td_id = trait_impl.impl_trait.id in
        if
          trait_impl.item_meta.is_local
          && (not (TraitDeclId.TreeMap.mem td_id !stateful_impl_spans))
          && Types.TraitMethodId.Map.exists
               (fun mid _ -> is_trait_method_stateful td_id mid)
               trait_impl.methods
        then
          stateful_impl_spans :=
            TraitDeclId.TreeMap.add td_id trait_impl.item_meta.span
              !stateful_impl_spans)
      m.trait_impls;

    (* Check that no builtin or external trait has a stateful method *)
    FunOrMethodId.Map.iter
      (fun id (info : fun_info) ->
        match id with
        | FunOrMethodId.Method (td_id, mid) when info.stateful -> (
            let impl_span =
              TraitDeclId.TreeMap.find_opt td_id !stateful_impl_spans
            in
            let method_name = Charon.GAstUtils.get_method_name m td_id mid in
            match TraitDeclId.Map.find_opt td_id m.trait_decls with
            | None ->
                [%save_error_opt_span] impl_span
                  ("External trait method '" ^ method_name
                 ^ "' cannot be effectful")
            | Some td ->
                let is_builtin_trait =
                  ExtractBuiltin.NameMatcherMap.mem name_matcher_ctx
                    td.item_meta.name
                    (ExtractBuiltin.builtin_trait_decls_map ())
                in
                if is_builtin_trait || not td.item_meta.is_local then
                  let kind_str =
                    if is_builtin_trait then "Builtin" else "External"
                  in
                  let span =
                    match impl_span with
                    | Some s -> s
                    | None -> td.item_meta.span
                  in
                  [%save_error] span
                    (kind_str ^ " trait method '" ^ method_name ^ "' of trait '"
                    ^ Charon.Print.name_to_string fmt_env td.item_meta.name
                    ^ "' cannot be effectful"))
        | _ -> ())
      !infos.infos;

    (* Check function pointers: stateful functions or trait methods cannot be taken as function pointers *)
    List.iter
      (fun (span, (id : FunOrMethodId.id)) ->
        let is_stateful =
          match lookup_fun_info !infos id with
          | Some info -> info.stateful
          | None -> false
        in
        if is_stateful then
          let item_name =
            match id with
            | FunOrMethodId.Fun fid -> (
                match FunDeclId.Map.find_opt fid m.fun_decls with
                | Some d -> Charon.Print.name_to_string fmt_env d.item_meta.name
                | None -> FunDeclId.to_string fid)
            | FunOrMethodId.Method (td_id, mid) ->
                Charon.GAstUtils.get_method_name m td_id mid
          in
          [%save_error] span
            ("Effectful function or trait method '" ^ item_name
           ^ "' cannot be used as a function pointer"))
      !fn_ptr_uses;

    (* Check trait objects: traits with any stateful method cannot be used with `dyn` *)
    let rec trait_has_stateful_method (visited : TraitDeclId.TreeSet.t)
        (td_id : TraitDeclId.id) : bool =
      if TraitDeclId.TreeSet.mem td_id visited then false
      else
        let visited = TraitDeclId.TreeSet.add td_id visited in
        match TraitDeclId.Map.find_opt td_id m.trait_decls with
        | None -> false
        | Some td ->
            Types.TraitMethodId.Map.exists
              (fun mid _ -> is_trait_method_stateful td_id mid)
              td.methods
            || List.exists
                 (fun (c : Types.trait_param) ->
                   trait_has_stateful_method visited c.trait.binder_value.id)
                 td.implied_clauses
    in
    List.iter
      (fun (span, td_id) ->
        if trait_has_stateful_method TraitDeclId.TreeSet.empty td_id then
          let trait_name =
            match TraitDeclId.Map.find_opt td_id m.trait_decls with
            | Some td -> Charon.Print.name_to_string fmt_env td.item_meta.name
            | None -> TraitDeclId.to_string td_id
          in
          [%save_error] span
            ("Trait '" ^ trait_name
           ^ "' has effectful methods and cannot be used as a `dyn` trait \
              object"))
      !dyn_trait_uses);

  !infos
