(** Deep printing mode for the Lean backend (CLI option [-deep]).

    For every transparent function declaration [f], we print:
    - a term [f.deep : Aeneas.Deep.Expr [input types] output_ty] which
      constructs the AST of the body of [f] (the AST is defined in
      [backends/lean/Aeneas/Deep/Basic.lean]);
    - a theorem [f.deep_eq] stating that the denotation of [f.deep] is [f].

    The deep AST is "deep structure, shallow leaves": binders, applications,
    conditionals, monadic binds and loops are first-order constructors, while
    the leaves (literals, function calls, constructors, projectors,
    operators...) are shallow Lean terms. We print the leaves with the regular
    (shallow) printer, eta-expanded over their arguments: a call [f x y] is
    printed as
    {[
      (.app (.app (.leaf (.fn "f") (fun (x : T1) (y : T2) => (f x y : T))) x') y')
    ]}
    where [x'] and [y'] are the deep terms of the arguments. This guarantees
    that the denotation of the deep term reduces (by beta) to exactly the term
    produced by the shallow printer, which is what makes the theorem provable by
    reflexivity (the [deep_rfl] tactic).

    Constructs which are not supported yet (matches, non-tuple patterns, etc.)
    are printed through the [Expr.shallow] escape hatch: the whole
    sub-expression is printed shallowly, as a function of the environment. The
    coverage is thus total from the start, and the precision of the deep terms
    can be improved incrementally. *)

open Pure
open PureUtils
open Extract
module F = Format

(** The deep printing environment: the free variables bound in the current
    scope, most recently bound first. The position of a variable in the list is
    its de Bruijn index. *)
type denv = fvar_id list

let deep_prefix = "Aeneas.Deep."

let denv_index (span : Meta.span) (env : denv) (id : fvar_id) : int =
  let rec find i env =
    match env with
    | [] ->
        [%craise] span
          ("Unbound variable in the deep term: " ^ FVarId.to_string id)
    | id' :: env -> if id' = id then i else find (i + 1) env
  in
  find 0 env

(** Print a de Bruijn variable: [(.var (.succ (.succ .zero)))] *)
let extract_deep_var (fmt : F.formatter) (i : int) : unit =
  F.pp_print_string fmt "(.var ";
  for _ = 1 to i do
    F.pp_print_string fmt "(.succ "
  done;
  F.pp_print_string fmt ".zero";
  for _ = 1 to i do
    F.pp_print_string fmt ")"
  done;
  F.pp_print_string fmt ")"

(** Escape a string so that it can be printed between double quotes *)
let lean_string_literal (s : string) : string = "\"" ^ String.escaped s ^ "\""

(** Is this a type we extract as a tuple (a tuple or a tuple struct)? *)
let type_is_tuple_like (ctx : extraction_ctx) (ty : ty) : bool =
  match ty with
  | TAdt (id, _) ->
      type_decl_from_type_id_is_tuple_struct ctx.trans_ctx.type_ctx.type_infos
        id
  | _ -> false

(** Translate a pattern to a deep pattern, if supported.

    Returns the list of the variables bound by the pattern, in binding order
    (which is the order of the environment extension), together with a printer
    for the deep pattern. *)
let rec deep_pat (span : Meta.span) (ctx : extraction_ctx) (p : tpat) :
    (fvar list * (F.formatter -> unit)) option =
  match p.pat with
  | POpen (v, _) -> Some ([ v ], fun fmt -> F.pp_print_string fmt ".var")
  | PIgnored -> Some ([], fun fmt -> F.pp_print_string fmt ".ignore")
  | PAdt { variant_id = None; fields } when type_is_tuple_like ctx p.ty ->
      deep_tuple_pat span ctx fields
  | PConstant _ | PBound _ | PAdt _ -> None

(** Tuples are right-nested pairs in Lean: [(a, b, c)] is [(a, (b, c))] *)
and deep_tuple_pat (span : Meta.span) (ctx : extraction_ctx)
    (fields : tpat list) : (fvar list * (F.formatter -> unit)) option =
  match fields with
  | [] -> Some ([], fun fmt -> F.pp_print_string fmt ".ignore")
  | [ f ] -> deep_pat span ctx f
  | f :: fields -> (
      match (deep_pat span ctx f, deep_tuple_pat span ctx fields) with
      | Some (vs0, p0), Some (vs1, p1) ->
          Some
            ( vs0 @ vs1,
              fun fmt ->
                F.pp_print_string fmt "(.pair ";
                p0 fmt;
                F.pp_print_space fmt ();
                p1 fmt;
                F.pp_print_string fmt ")" )
      | _ -> None)

(** Bind the variables of a pattern: add them to the extraction context (to
    generate their names) and to the deep environment. *)
let bind_vars (span : Meta.span) (ctx : extraction_ctx) (env : denv)
    (vs : fvar list) : extraction_ctx * denv =
  let ctx, _ = ctx_add_vars span vs ctx in
  (ctx, List.map (fun (v : fvar) -> v.id) vs @ env)

(** Print a shallow expression with a type annotation: [(e : ty)] *)
let extract_annotated_shallow (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (e : texpr) : unit =
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "(";
  extract_texpr span ctx fmt ~inside:false ~inside_do:false e;
  F.pp_print_space fmt ();
  F.pp_print_string fmt ":";
  F.pp_print_space fmt ();
  extract_ty span ctx fmt TypeDeclId.TreeSet.empty ~inside:false e.ty;
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(** The tag of a leaf standing for a qualifier *)
let qualif_tag (ctx : extraction_ctx) (q : qualif) : string =
  let quoted (s : string) = lean_string_literal s in
  match q.id with
  | FunOrOp (Fun fid) ->
      "(.fn " ^ quoted (fun_or_op_id_to_string ctx (Fun fid)) ^ ")"
  | FunOrOp (Unop unop) ->
      "(.unop " ^ quoted (fun_or_op_id_to_string ctx (Unop unop)) ^ ")"
  | FunOrOp (Binop binop) ->
      "(.binop " ^ quoted (binop_to_string ctx binop) ^ ")"
  | Global gid -> "(.global " ^ quoted (global_decl_id_to_string ctx gid) ^ ")"
  | AdtCons cons ->
      let name =
        match cons.variant_id with
        | Some _ -> adt_variant_to_string None ctx cons.adt_id cons.variant_id
        | None -> type_id_to_string ctx cons.adt_id
      in
      "(.ctor " ^ quoted name ^ ")"
  | Proj proj ->
      "(.proj "
      ^ quoted (adt_field_to_string None ctx proj.adt_id proj.field_id)
      ^ ")"
  | ScalarValProj _ -> "(.proj \"val\")"
  | TraitConst _ -> "(.other \"trait_const\")"
  | MkDynTrait _ -> "(.other \"dyn\")"
  | LoopOp -> "(.other \"loop\")"

(** Print the escape hatch: the whole expression is printed shallowly, as a
    function of the environment:
    {[
      (.shallow (fun | x ::ₕ y ::ₕ .nil => SHALLOW))
    ]} *)
let extract_deep_escape (span : Meta.span) (ctx : extraction_ctx) (env : denv)
    (fmt : F.formatter) (e : texpr) : unit =
  (* The right-hand side of the alternative must start at a column greater than
     or equal to the column of the [|]: we use vertical boxes to control the
     layout precisely:
     {[
       (.shallow (fun
         | x ::ₕ y ::ₕ .nil =>
           (BODY)))
     ]} *)
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt "(.shallow (fun";
  F.pp_print_cut fmt ();
  F.pp_open_vbox fmt ctx.indent_incr;
  let vars = List.map (fun id -> ctx_get_var span id ctx ^ " ::ₕ ") env in
  F.pp_print_string fmt ("| " ^ String.concat "" vars ^ ".nil =>");
  F.pp_print_cut fmt ();
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "(";
  extract_texpr span ctx fmt ~inside:false ~inside_do:false e;
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ();
  F.pp_close_box fmt ();
  F.pp_print_string fmt "))";
  F.pp_close_box fmt ()

(** Is the expression the [Result.ok] constructor (as a qualifier or as a pure
    builtin)? *)
let is_result_ok (app : texpr) : bool =
  match app.e with
  | Qualif { id = FunOrOp (Fun (Pure Return)); _ } -> true
  | Qualif
      { id = AdtCons { adt_id = TBuiltin TResult; variant_id = Some vid }; _ }
    -> vid = result_ok_id
  | _ -> false

(** Is the expression the [Result.fail] constructor? *)
let is_result_fail (app : texpr) : bool =
  match app.e with
  | Qualif { id = FunOrOp (Fun (Pure Fail)); _ } -> true
  | Qualif
      { id = AdtCons { adt_id = TBuiltin TResult; variant_id = Some vid }; _ }
    -> vid = result_fail_id
  | _ -> false

(** Information about an ADT we can match on with a deep eliminator *)
type deep_adt_info = {
  elim_name : string;  (** The name of the deep eliminator *)
  decl : type_decl;
  generics : generic_args;
}

(** The builtin types for which the Lean library provides a deep eliminator
    ([Aeneas.Deep.<Name>.deepElim]), identified by their extraction name. *)
let builtin_deep_elims = [ "Option" ]

(** Do we generate a deep eliminator for this type declaration?

    We do so for the types we extract as inductive definitions: transparent,
    non-builtin, and not extracted as tuples. *)
let type_decl_has_deep_elim (ctx : extraction_ctx) (def : type_decl) : bool =
  def.builtin_info = None
  && (match def.kind with
    | Struct _ | Enum _ -> true
    | Opaque -> false)
  && not
       (type_decl_from_type_id_is_tuple_struct ctx.trans_ctx.type_ctx.type_infos
          (TAdtId def.def_id))

(** Lookup the deep eliminator for an ADT type, if there is one *)
let deep_adt_info (span : Meta.span) (ctx : extraction_ctx) (ty : ty) :
    deep_adt_info option =
  match ty with
  | TAdt (TAdtId id, generics) -> (
      match TypeDeclId.Map.find_opt id ctx.trans_types with
      | None -> None
      | Some decl ->
          if type_decl_has_deep_elim ctx decl then
            Some
              {
                elim_name = ctx_get_local_type span id ctx ^ ".deepElim";
                decl;
                generics;
              }
          else
            let name = ctx_get_type (Some span) (TAdtId id) ctx in
            if decl.builtin_info <> None && List.mem name builtin_deep_elims
            then
              Some
                { elim_name = deep_prefix ^ name ^ ".deepElim"; decl; generics }
            else None)
  | _ -> None

let type_decl_num_variants (decl : type_decl) : int =
  match decl.kind with
  | Enum variants -> List.length variants
  | Struct _ -> 1
  | Opaque -> 0

(** Plan a deep match: check that all the branches are supported, and compute,
    for every variant of the scrutinee's type, the variables bound by the branch
    and its body.

    Returns [None] if the match can't be printed with a deep eliminator (we then
    use the escape hatch). This is the case for:
    - matches on types which have no deep eliminator
    - matches with a default branch ([_ => ...]): Lean compiles those to an
      auxiliary definition which is not definitionally equal to a [casesOn]
    - matches on literals, nested patterns *)
let plan_deep_match (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (scrut : texpr) (branches : match_branch list) :
    (deep_adt_info * (fvar list * texpr) list) option =
  match deep_adt_info span ctx scrut.ty with
  | None -> None
  | Some info ->
      let num_variants = type_decl_num_variants info.decl in
      let brs = Array.make num_variants None in
      let supported = ref true in
      List.iter
        (fun (br : match_branch) ->
          match br.pat.pat with
          | PAdt { variant_id; fields } ->
              let vid =
                match variant_id with
                | Some vid -> VariantId.to_int vid
                | None -> 0
              in
              let fields =
                List.map (tpat_replace_ignored_vars_with_free_vars fresh) fields
              in
              if
                vid < num_variants
                && List.for_all is_pat_open fields
                && Option.is_none brs.(vid)
              then
                brs.(vid) <-
                  Some
                    ( List.map
                        (fun f -> fst ([%add_loc] as_pat_open span f))
                        fields,
                      br.branch )
              else supported := false
          | PConstant _ | PBound _ | POpen _ | PIgnored -> supported := false)
        branches;
      if !supported && Array.for_all Option.is_some brs then
        Some (info, List.map Option.get (Array.to_list brs))
      else None

(** Plan a struct pattern (a single-variant ADT pattern binding the fields of a
    structure): returns the eliminator and the variables bound by the fields. *)
let plan_deep_struct_pat (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (pat : tpat) : (deep_adt_info * fvar list) option
    =
  match pat.pat with
  | PAdt { variant_id = None; fields } when not (type_is_tuple_like ctx pat.ty)
    -> (
      match deep_adt_info span ctx pat.ty with
      | Some info when type_decl_num_variants info.decl = 1 ->
          let fields =
            List.map (tpat_replace_ignored_vars_with_free_vars fresh) fields
          in
          if List.for_all is_pat_open fields then
            Some
              ( info,
                List.map (fun f -> fst ([%add_loc] as_pat_open span f)) fields
              )
          else None
      | _ -> None)
  | _ -> None

(** Print a deep expression.

    - [fresh]: generator of fresh variable ids, shared with the one used to open
      the binders of the function body.
    - [env]: the deep environment (see {!denv}). The extraction context [ctx]
      must contain names for all the variables of [env]. *)
let rec extract_deep_texpr (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (env : denv) (fmt : F.formatter)
    ?(expected : ty option) (e : texpr) : unit =
  match e.e with
  | FVar id -> extract_deep_var fmt (denv_index span env id)
  | BVar _ -> [%internal_error] span
  | CVar _ | Const _ ->
      F.pp_print_string fmt "(.lit ";
      extract_texpr span ctx fmt ~inside:true ~inside_do:false e;
      F.pp_print_string fmt ")"
  | Meta (_, e) -> extract_deep_texpr span ctx fresh env fmt ?expected e
  | Lambda _ ->
      let xl, body = raw_destruct_lambdas e in
      extract_deep_lambdas span ctx fresh env fmt ?expected e xl body
  | Let (monadic, pat, bound, next) -> (
      (* A non-monadic let-binding of a comparison binds a proposition in the
         shallow code (Lean doesn't insert a coercion to [Bool] without an
         expected type): we don't support this yet. *)
      let binds_comparison =
        (not monadic)
        &&
        match (destruct_apps bound |> fst).e with
        | Qualif { id = FunOrOp (Binop (Eq _ | Lt _ | Le _ | Gt _ | Ge _)); _ }
          -> true
        | _ -> false
      in
      let bound_ty = if monadic then mk_result_ty pat.ty else pat.ty in
      match if binds_comparison then None else deep_pat span ctx pat with
      | None -> (
          (* Structure patterns: [let ⟨ a, b ⟩ := e] is a match with a single
             branch *)
          match
            if binds_comparison then None
            else plan_deep_struct_pat span ctx fresh pat
          with
          | None -> extract_deep_escape span ctx env fmt e
          | Some (info, vs) ->
              if monadic then (
                (* [let ⟨ a, b ⟩ ← e; k] is elaborated to
                   [bind e (fun x => S.casesOn x (fun a b => k))] *)
                let x = { id = fresh (); basename = None; ty = pat.ty } in
                F.pp_open_hvbox fmt 0;
                F.pp_open_hovbox fmt ctx.indent_incr;
                F.pp_print_string fmt "(.bind";
                F.pp_print_space fmt ();
                extract_deep_texpr span ctx fresh env fmt ~expected:bound_ty
                  bound;
                F.pp_print_space fmt ();
                F.pp_print_string fmt ".var";
                F.pp_close_box fmt ();
                F.pp_print_space fmt ();
                let ctx, env = bind_vars span ctx env [ x ] in
                extract_deep_match span ctx fresh env fmt ?expected
                  (mk_texpr_from_fvar x) (Some pat.ty) info.elim_name
                  [ (vs, next) ];
                F.pp_print_string fmt ")";
                F.pp_close_box fmt ())
              else
                extract_deep_match span ctx fresh env fmt ?expected bound
                  (Some pat.ty) info.elim_name
                  [ (vs, next) ])
      | Some (vs, ppat) ->
          F.pp_open_hvbox fmt 0;
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt (if monadic then "(.bind" else "(.let_");
          F.pp_print_space fmt ();
          (* The type of the bound expression is given by the pattern *)
          extract_deep_texpr span ctx fresh env fmt ~expected:bound_ty bound;
          F.pp_print_space fmt ();
          ppat fmt;
          F.pp_close_box fmt ();
          F.pp_print_space fmt ();
          let ctx, env = bind_vars span ctx env vs in
          extract_deep_texpr span ctx fresh env fmt ?expected next;
          F.pp_print_string fmt ")";
          F.pp_close_box fmt ())
  | Switch (scrut, If (e_then, e_else)) ->
      F.pp_open_hvbox fmt 0;
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.ite";
      F.pp_print_space fmt ();
      extract_deep_cond span ctx fresh env fmt scrut;
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx fresh env fmt ?expected e_then;
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx fresh env fmt ?expected e_else;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Switch (scrut, Match branches) -> (
      match plan_deep_match span ctx fresh scrut branches with
      | Some (info, brs) ->
          extract_deep_match span ctx fresh env fmt ?expected scrut None
            info.elim_name brs
      | None -> extract_deep_escape span ctx env fmt e)
  | App _ | Qualif _ -> extract_deep_app span ctx fresh env fmt ?expected e
  | StructUpdate supd ->
      (* We eta-expand the structure update over the initial value (if there is
         one) and the field values *)
      let args =
        Option.to_list supd.init @ List.map (fun (_, v) -> v) supd.updates
      in
      let mk_shallow (args : texpr list) : texpr =
        let init, values =
          match supd.init with
          | None -> (None, args)
          | Some _ -> (
              match args with
              | init :: values -> (Some init, values)
              | [] -> [%internal_error] span)
        in
        let updates =
          List.map2 (fun (fid, _) v -> (fid, v)) supd.updates values
        in
        { e with e = StructUpdate { supd with init; updates } }
      in
      let tag =
        "(.ctor "
        ^ lean_string_literal (type_id_to_string ctx supd.struct_id)
        ^ ")"
      in
      extract_deep_eta_leaf span ctx fresh env fmt tag mk_shallow args
        (Some (Option.value expected ~default:e.ty))
  | Loop _ ->
      (* The loop nodes should have been eliminated in {!PureMicroPasses} *)
      [%admit_raise] span "Unreachable" fmt
  | EError _ -> F.pp_print_string fmt "sorry"

(** Print a match with a deep eliminator:
    {[
      (.match_ SCRUT ELIM
       (.cons BRANCH_0
       (.cons BRANCH_1
       .nil)))
    ]}
    [brs]: for every variant, in order, the variables bound by the branch (the
    fields of the variant) and the body of the branch. *)
and extract_deep_match (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (env : denv) (fmt : F.formatter)
    ?(expected : ty option) (scrut : texpr) (scrut_expected : ty option)
    (elim_name : string) (brs : (fvar list * texpr) list) : unit =
  F.pp_open_vbox fmt 0;
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "(.match_";
  F.pp_print_space fmt ();
  extract_deep_texpr span ctx fresh env fmt ?expected:scrut_expected scrut;
  F.pp_print_space fmt ();
  F.pp_print_string fmt elim_name;
  F.pp_close_box fmt ();
  F.pp_print_cut fmt ();
  F.pp_open_vbox fmt 0;
  List.iter
    (fun (vs, body) ->
      F.pp_print_string fmt "(.cons ";
      let ctx, env = bind_vars span ctx env vs in
      F.pp_open_hovbox fmt ctx.indent_incr;
      extract_deep_texpr span ctx fresh env fmt ?expected body;
      F.pp_close_box fmt ();
      F.pp_print_cut fmt ())
    brs;
  F.pp_print_string fmt ".nil";
  List.iter (fun _ -> F.pp_print_string fmt ")") brs;
  F.pp_close_box fmt ();
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(** Print nested lambdas: [(.lam p1 (.lam p2 body))] *)
and extract_deep_lambdas (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (env : denv) (fmt : F.formatter)
    ?(expected : ty option) (e : texpr) (xl : tpat list) (body : texpr) : unit =
  (* All the patterns must be supported, otherwise we print the whole lambda
     through the escape hatch *)
  let pats = List.map (deep_pat span ctx) xl in
  if List.exists Option.is_none pats then extract_deep_escape span ctx env fmt e
  else
    let pats = List.map Option.get pats in
    F.pp_open_hovbox fmt ctx.indent_incr;
    let ctx, env =
      List.fold_left
        (fun (ctx, env) (vs, ppat) ->
          F.pp_print_string fmt "(.lam ";
          ppat fmt;
          F.pp_print_space fmt ();
          bind_vars span ctx env vs)
        (ctx, env) pats
    in
    (* The expected type of the body: we peel one arrow per binder *)
    let body_expected =
      List.fold_left
        (fun (expected : ty option) _ ->
          match expected with
          | Some (TArrow (_, ty)) -> Some ty
          | _ -> None)
        expected pats
    in
    extract_deep_texpr span ctx fresh env fmt ?expected:body_expected body;
    List.iter (fun _ -> F.pp_print_string fmt ")") pats;
    F.pp_close_box fmt ()

(** Print an [if] condition.

    The comparisons [=], [<], [<=], [>], [>=] are printed by the shallow printer
    with the infix notations, which Lean elaborates to propositions: we use the
    dedicated constructors of [Cond]. All the other conditions are boolean
    expressions, which the shallow [if] turns into [b = true]: we use
    [Cond.bool]. *)
and extract_deep_cond (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (env : denv) (fmt : F.formatter) (scrut : texpr) :
    unit =
  let app, args = destruct_apps scrut in
  let cons =
    match (app.e, args) with
    | ( Qualif
          { id = FunOrOp (Binop ((Eq _ | Lt _ | Le _ | Gt _ | Ge _) as op)); _ },
        [ _; _ ] ) ->
        Some
          (match op with
          | Eq _ -> ".eq"
          | Lt _ -> ".lt"
          | Le _ -> ".le"
          | Gt _ -> ".gt"
          | Ge _ -> ".ge"
          | _ -> [%internal_error] span)
    | _ -> None
  in
  F.pp_open_hovbox fmt ctx.indent_incr;
  (match cons with
  | Some cons ->
      F.pp_print_string fmt ("(" ^ cons);
      List.iter
        (fun arg ->
          F.pp_print_space fmt ();
          extract_deep_texpr span ctx fresh env fmt arg)
        args;
      F.pp_print_string fmt ")"
  | None ->
      F.pp_print_string fmt "(.bool";
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx fresh env fmt scrut;
      F.pp_print_string fmt ")");
  F.pp_close_box fmt ()

(** Print an application (or a top-level qualifier). *)
and extract_deep_app (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (env : denv) (fmt : F.formatter)
    ?(expected : ty option) (e : texpr) : unit =
  let app, args = destruct_apps e in
  let print_simple (cons : string) (args : texpr list) : unit =
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt ("(" ^ cons);
    List.iter
      (fun arg ->
        F.pp_print_space fmt ();
        extract_deep_texpr span ctx fresh env fmt arg)
      args;
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ()
  in
  match (app.e, args) with
  | Qualif { id = LoopOp; _ }, [ _; _ ] -> print_simple ".loop" args
  | ( Qualif { id = FunOrOp (Binop (Eq _ | Lt _ | Le _ | Gt _ | Ge _)); _ },
      [ _; _ ] ) ->
      (* The comparisons are printed with infix notations which Lean elaborates
         to propositions: in a boolean context, the shallow code coerces them
         with [decide]. *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.decide";
      F.pp_print_space fmt ();
      extract_deep_cond span ctx fresh env fmt e;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Qualif { id = FunOrOp (Fun (Pure Assert)); _ }, [ cond ] ->
      (* [massert] takes a proposition: the condition is handled like the
         condition of an [if] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.assert";
      F.pp_print_space fmt ();
      extract_deep_cond span ctx fresh env fmt cond;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Qualif _, [ arg ] when is_result_ok app ->
      let expected =
        match expected with
        | Some (TAdt (TBuiltin TResult, { types = [ ty ]; _ })) -> Some ty
        | _ -> None
      in
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.ok";
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx fresh env fmt ?expected arg;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Qualif _, [ ({ e = Qualif _; _ } as err) ] when is_result_fail app ->
      (* The error is a closed term: we print it shallowly *)
      F.pp_print_string fmt "(.fail ";
      extract_texpr span ctx fmt ~inside:true ~inside_do:false err;
      F.pp_print_string fmt ")"
  | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ }, _ -> (
      (* Tuples are right-nested pairs *)
      match args with
      | [] -> F.pp_print_string fmt "(.lit ())"
      | [ arg ] -> extract_deep_texpr span ctx fresh env fmt arg
      | _ ->
          let rec print_tuple (args : texpr list) : unit =
            match args with
            | [] -> [%internal_error] span
            | [ arg ] -> extract_deep_texpr span ctx fresh env fmt arg
            | arg :: args ->
                F.pp_open_hovbox fmt ctx.indent_incr;
                F.pp_print_string fmt "(.pair";
                F.pp_print_space fmt ();
                extract_deep_texpr span ctx fresh env fmt arg;
                F.pp_print_space fmt ();
                print_tuple args;
                F.pp_print_string fmt ")";
                F.pp_close_box fmt ()
          in
          print_tuple args)
  | Qualif q, _ ->
      let mk_shallow (args : texpr list) : texpr =
        [%add_loc] mk_apps span app args
      in
      extract_deep_eta_leaf span ctx fresh env fmt (qualif_tag ctx q) mk_shallow
        args expected
  | _, [] -> extract_deep_texpr span ctx fresh env fmt app
  | _, _ ->
      (* Regular application: [(.app (.app f a) b)] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      List.iter (fun _ -> F.pp_print_string fmt "(.app ") args;
      extract_deep_texpr span ctx fresh env fmt app;
      List.iter
        (fun arg ->
          F.pp_print_space fmt ();
          extract_deep_texpr span ctx fresh env fmt arg;
          F.pp_print_string fmt ")")
        args;
      F.pp_close_box fmt ()

(** Print a leaf eta-expanded over its arguments, applied to the deep arguments:
    {[
      (.app (.app (.leaf TAG (fun (x : T1) (y : T2) => (SHALLOW : T))) x') y')
    ]}
    [mk_shallow] builds the shallow expression from the (fresh) variables
    standing for the arguments. [out_ty] is the type of the whole application.
*)
and extract_deep_eta_leaf (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (env : denv) (fmt : F.formatter) (tag : string)
    (mk_shallow : texpr list -> texpr) (args : texpr list)
    (expected : ty option) : unit =
  (* Fresh variables for the arguments *)
  let vars =
    List.map
      (fun (a : texpr) -> { id = fresh (); basename = None; ty = a.ty })
      args
  in
  let ctx', names = ctx_add_vars span vars ctx in
  (* Remark: for the type annotation, we use the expected type when we know
     it (from the enclosing binder, or from the signature of the function),
     and otherwise the type computed by [mk_shallow] (which, for applications,
     derives it from the type of the head): the type annotations of the
     application nodes are not always reliable after the micro-passes. *)
  let shallow = mk_shallow (List.map mk_texpr_from_fvar vars) in
  let shallow =
    match expected with
    | Some ty -> { shallow with ty }
    | None -> shallow
  in
  F.pp_open_hovbox fmt ctx.indent_incr;
  List.iter (fun _ -> F.pp_print_string fmt "(.app ") args;
  (* The leaf *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt ("(.leaf " ^ tag);
  F.pp_print_space fmt ();
  if args <> [] then (
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt "(fun";
    List.iter2
      (fun name (v : fvar) ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt ("(" ^ name ^ " : ");
        extract_ty span ctx' fmt TypeDeclId.TreeSet.empty ~inside:false v.ty;
        F.pp_print_string fmt ")")
      names vars;
    F.pp_print_space fmt ();
    F.pp_print_string fmt "=>";
    F.pp_close_box fmt ();
    F.pp_print_space fmt ());
  extract_annotated_shallow span ctx' fmt shallow;
  if args <> [] then F.pp_print_string fmt ")";
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ();
  (* The arguments *)
  List.iter
    (fun arg ->
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx fresh env fmt arg;
      F.pp_print_string fmt ")")
    args;
  F.pp_close_box fmt ()

(** Print the explicit generic parameters of a function, as computed by
    {!Extract.extract_fun_parameters}. *)
let extract_explicit_params (fmt : F.formatter)
    (all_params : (explicit * string) list) : unit =
  List.iter
    (fun (e, name) ->
      if e = Explicit then (
        F.pp_print_space fmt ();
        F.pp_print_string fmt name))
    all_params

(** Print the deep term and the denotation theorem for a declaration (a function
    or a global) with a body.

    - [def_name]: the name of the (shallow) declaration
    - [unfold]: if [true], the proof of the theorem starts by unfolding the
      declaration (recursive definitions, globals)
    - [comment]: prints the comment which links the deep term to the Rust
      declaration *)
let extract_decl_deep (ctx : extraction_ctx) (fmt : F.formatter) ~(id : id)
    ~(def_name : string) ~(unfold : bool) ~(comment : unit -> unit)
    (def : fun_decl) : unit =
  let span = def.item_meta.span in
  match def.body with
  | None -> ()
  | Some body ->
      [%ltrace "Extracting the deep term of: " ^ def_name];
      (* The names of the deep term and of the theorem were registered in the
         names map (see [ctx_add_deep_names]) *)
      let deep_name = ctx_get_deep_term span id ctx in
      let deep_eq_name = ctx_get_deep_eq span id ctx in
      (* Open the binders *)
      let _, fresh = FVarId.fresh_stateful_generator () in
      let _, body = open_all_fun_body fresh span body in
      (* Replace the ignored input patterns by variables: we need to name all
         the inputs in the theorem *)
      let body =
        {
          body with
          inputs =
            List.map
              (tpat_replace_ignored_vars_with_free_vars fresh)
              body.inputs;
        }
      in
      let def = { def with body = Some body } in
      let input_vars =
        List.map (fun p -> fst ([%add_loc] as_pat_open span p)) body.inputs
      in
      (*
       * The deep term
       *)
      F.pp_print_break fmt 0 0;
      comment ();
      F.pp_print_space fmt ();
      (* Open a vbox so that every line after the first one gets indented *)
      F.pp_open_vbox fmt ctx.indent_incr;
      (* The header: [def NAME.deep GENERICS : Aeneas.Deep.Expr [T1, ..., Tn] T :=] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt ("def " ^ deep_name);
      F.pp_print_space fmt ();
      let ctx_g, type_params, cg_params, trait_clauses =
        ctx_add_generic_params span def.item_meta.name Item
          def.signature.llbc_generics def.signature.generics ctx
      in
      let space = ref true in
      (let space = Some space in
       extract_generic_params span ctx_g fmt TypeDeclId.TreeSet.empty ~space
         Item def.signature.generics (Some def.signature.explicit_info)
         type_params cg_params trait_clauses);
      insert_req_space fmt space;
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt (deep_prefix ^ "Expr [");
      Collections.List.iter_link
        (fun () ->
          F.pp_print_string fmt ",";
          F.pp_print_space fmt ())
        (fun (ty : ty) ->
          extract_ty span ctx_g fmt TypeDeclId.TreeSet.empty ~inside:false ty)
        def.signature.inputs;
      F.pp_print_string fmt "]";
      F.pp_print_space fmt ();
      extract_ty span ctx_g fmt TypeDeclId.TreeSet.empty ~inside:true
        def.signature.output;
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":=";
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      (* The body: the inputs are the initial environment *)
      let ctx_b, env = bind_vars span ctx_g [] input_vars in
      F.pp_open_hovbox fmt ctx.indent_incr;
      extract_deep_texpr span ctx_b fresh env fmt ~expected:def.signature.output
        body.body;
      F.pp_close_box fmt ();
      (* Close the vbox *)
      F.pp_close_box fmt ();
      F.pp_print_break fmt 0 0;
      (*
       * The theorem
       *)
      F.pp_print_break fmt 0 0;
      F.pp_open_vbox fmt ctx.indent_incr;
      (* The header: [theorem NAME.deep_eq GENERICS (x : T) ... :] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt ("theorem " ^ deep_eq_name);
      F.pp_print_space fmt ();
      let space = ref true in
      let _, ctx_body, all_params = extract_fun_parameters space ctx fmt def in
      insert_req_space fmt space;
      F.pp_print_string fmt ":";
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      (* The statement:
         [f G x y = Aeneas.Deep.Expr.denote (f.deep G) (x ::ₕ y ::ₕ Aeneas.Deep.HList.nil)] *)
      let input_names =
        List.map (fun (v : fvar) -> ctx_get_var span v.id ctx_body) input_vars
      in
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt def_name;
      extract_explicit_params fmt all_params;
      List.iter
        (fun name ->
          F.pp_print_space fmt ();
          F.pp_print_string fmt name)
        input_names;
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      F.pp_print_string fmt "=";
      F.pp_print_space fmt ();
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt (deep_prefix ^ "Expr.denote");
      F.pp_print_space fmt ();
      F.pp_print_string fmt ("(" ^ deep_name);
      extract_explicit_params fmt all_params;
      F.pp_print_string fmt ")";
      F.pp_print_space fmt ();
      F.pp_print_string fmt "(";
      List.iter (fun name -> F.pp_print_string fmt (name ^ " ::ₕ ")) input_names;
      F.pp_print_string fmt (deep_prefix ^ "HList.nil)");
      F.pp_close_box fmt ();
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      (* The proof: recursive definitions need to be unfolded once *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt ":= by";
      F.pp_print_space fmt ();
      if unfold then F.pp_print_string fmt ("unfold " ^ def_name ^ "; ");
      F.pp_print_string fmt "deep_rfl";
      F.pp_close_box fmt ();
      (* Close the vbox *)
      F.pp_close_box fmt ();
      F.pp_print_break fmt 0 0

(** Print the deep eliminator of a type declaration:
    {[
      @[reducible] def NAME.deepElim {T : Type _} :
        Aeneas.Deep.Elim (NAME T) [[T1, T2], [], ...] :=
        fun x alts => NAME.casesOn x alts.1 alts.2.1 ...
    ]}
    We don't print anything for the types which are not extracted as inductive
    definitions (see {!type_decl_has_deep_elim}). *)
let extract_type_decl_deep (ctx : extraction_ctx) (fmt : F.formatter)
    (def : type_decl) : unit =
  if type_decl_has_deep_elim ctx def then (
    let span = def.item_meta.span in
    let name = ctx_get_local_type span def.def_id ctx in
    let variants_fields : field list list =
      match def.kind with
      | Struct fields -> [ fields ]
      | Enum variants -> List.map (fun (v : variant) -> v.fields) variants
      | Opaque -> []
    in
    F.pp_print_break fmt 0 0;
    extract_comment_with_span ctx fmt
      [ "Deep eliminator for [" ^ name_to_string ctx def.item_meta.name ^ "]" ]
      None span;
    F.pp_print_space fmt ();
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt ("@[reducible] def " ^ name ^ ".deepElim");
    F.pp_print_space fmt ();
    let ctx, type_params, cg_params, trait_clauses =
      ctx_add_generic_params span def.item_meta.name Item def.llbc_generics
        def.generics ctx
    in
    let space = ref true in
    (let space = Some space in
     extract_generic_params span ctx fmt TypeDeclId.TreeSet.empty
       ~as_implicits:true ~space Item def.generics None type_params cg_params
       trait_clauses);
    insert_req_space fmt space;
    F.pp_print_string fmt ":";
    F.pp_print_space fmt ();
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt (deep_prefix ^ "Elim");
    F.pp_print_space fmt ();
    extract_ty span ctx fmt TypeDeclId.TreeSet.empty ~inside:true
      (TAdt (TAdtId def.def_id, generic_args_of_params def.generics));
    F.pp_print_space fmt ();
    F.pp_print_string fmt "[";
    Collections.List.iter_link
      (fun () ->
        F.pp_print_string fmt ",";
        F.pp_print_space fmt ())
      (fun (fields : field list) ->
        F.pp_print_string fmt "[";
        Collections.List.iter_link
          (fun () ->
            F.pp_print_string fmt ",";
            F.pp_print_space fmt ())
          (fun (f : field) ->
            extract_ty span ctx fmt TypeDeclId.TreeSet.empty ~inside:false
              f.field_ty)
          fields;
        F.pp_print_string fmt "]")
      variants_fields;
    F.pp_print_string fmt "]";
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    F.pp_print_string fmt ":=";
    F.pp_close_box fmt ();
    F.pp_print_space fmt ();
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt ("fun x alts => " ^ name ^ ".casesOn x");
    List.iteri
      (fun i _ ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt
          ("alts" ^ String.concat "" (List.init i (fun _ -> ".2")) ^ ".1"))
      variants_fields;
    F.pp_close_box fmt ();
    F.pp_close_box fmt ();
    F.pp_print_break fmt 0 0)

(** Print the deep term and the denotation theorem for a (transparent) function
    declaration. *)
let extract_fun_decl_deep (ctx : extraction_ctx) (fmt : F.formatter)
    (kind : decl_kind) (def : fun_decl) : unit =
  let span = def.item_meta.span in
  [%sanity_check] span (not def.is_global_decl_body);
  let def_name = ctx_get_local_function span def.def_id def.loop_id ctx in
  let id = FunId (FromLlbc (Pure.FunId def.def_id, def.loop_id)) in
  (* Recursive definitions are not definitionally equal to their bodies: the
     proof unfolds them once *)
  extract_decl_deep ctx fmt ~id ~def_name
    ~unfold:(decl_is_from_rec_group kind)
    ~comment:(fun () -> extract_fun_comment ctx fmt def)
    def

(** Print the deep term and the denotation theorem for a (transparent) global
    declaration. [body] is the translation of the initializer of the global. *)
let extract_global_decl_deep (ctx : extraction_ctx) (fmt : F.formatter)
    (global : global_decl) (body : fun_decl) : unit =
  let span = global.span in
  let def_name = ctx_get_global span global.def_id ctx in
  let comment () =
    let name =
      if !Config.extract_external_name_patterns && not global.item_meta.is_local
      then Some global.item_meta.name
      else None
    in
    extract_comment_with_span ctx fmt
      [ "[" ^ name_to_string ctx global.item_meta.name ^ "]" ]
      name ~public:global.item_meta.attr_info.public global.span
  in
  (* Globals are extracted as irreducible definitions: the proof unfolds them *)
  extract_decl_deep ctx fmt ~id:(GlobalId global.def_id) ~def_name ~unfold:true
    ~comment body
