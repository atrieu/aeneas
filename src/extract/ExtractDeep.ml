(** Deep printing mode for the Lean backend (CLI option [-deep]).

    For every transparent function declaration [f], we print:
    - a term
      [f.deep : Aeneas.Deep.Expr TypeName FunName GlobalName σ [input types]
       output_ty] which constructs the AST of the body of [f] (the AST is
      defined in [backends/lean/Aeneas/Deep/Basic.lean]);
    - a theorem [f.deep_eq] stating that the denotation of [f.deep] is [f].

    The deep AST is "deep structure, shallow leaves": binders, applications,
    conditionals, monadic binds, loops, the primitive operations and the
    constructors, projections and matches of the ADTs of the crate are
    first-order constructors, while the remaining leaves (function calls,
    globals, ...) are shallow Lean terms. We print those leaves with the regular
    (shallow) printer, eta-expanded over their arguments: a call [f x y] is
    printed as
    {[
      (.app (.app (.leaf (.fn "f") TY (fun (x : T1) (y : T2) => (f x y : T))) x') y')
    ]}
    where [x'] and [y'] are the deep terms of the arguments and [TY] the
    descriptor of the type of [f]. This guarantees that the denotation of the
    deep term reduces (by beta) to exactly the term produced by the shallow
    printer, which is what makes the theorem provable by reflexivity (the
    [deep_rfl] tactic).

    Types are printed as descriptors ([Aeneas.Deep.Ty TypeName]) over a
    crate-level enumeration [TypeName] of the type declarations, which we
    generate at the beginning of the deep section together with the instances
    describing the types (Lean type, variants, constructors, projectors,
    eliminators): see {!extract_type_names}. The types which the descriptors can
    not express (trait-associated types, raw pointers, types with trait clauses,
    ...) are turned into type variables of the deep term: the type environment
    of a deep term lists the type parameters of the definition, followed by
    those extra types (see {!deep_tyenv}).

    Constructs which are not supported (matches with a default branch, literal
    patterns, etc.) are printed through the [Expr.shallow] escape hatch: the
    whole sub-expression is printed shallowly, as a function of the environment.
    The coverage is thus total from the start, and the precision of the deep
    terms can be improved incrementally. *)

open Pure
open PureUtils
open Extract
module F = Format

(** The deep printing environment: the free variables bound in the current
    scope, most recently bound first. The position of a variable in the list is
    its de Bruijn index. *)
type denv = fvar_id list

let deep_prefix = "Aeneas.Deep."

(** The name of the generated enumeration of the type names of the crate *)
let type_name_enum = "TypeName"

let denv_index (span : Meta.span) (env : denv) (id : fvar_id) : int =
  let rec find i env =
    match env with
    | [] ->
        [%craise] span
          ("Unbound variable in the deep term: " ^ FVarId.to_string id)
    | id' :: env -> if id' = id then i else find (i + 1) env
  in
  find 0 env

(** Print a de Bruijn index: [.zero], [(.succ (.succ .zero))], ... *)
let extract_var_index (fmt : F.formatter) (i : int) : unit =
  for _ = 1 to i do
    F.pp_print_string fmt "(.succ "
  done;
  F.pp_print_string fmt ".zero";
  for _ = 1 to i do
    F.pp_print_string fmt ")"
  done

(** Print a de Bruijn variable: [(.var (.succ (.succ .zero)))] *)
let extract_deep_var (fmt : F.formatter) (i : int) : unit =
  F.pp_print_string fmt "(.var ";
  extract_var_index fmt i;
  F.pp_print_string fmt ")"

(** Escape a string so that it can be printed between double quotes *)
let lean_string_literal (s : string) : string = "\"" ^ String.escaped s ^ "\""

(** Is this a type we extract as a tuple (a tuple or a tuple struct)? The
    builtin types are never tuples, whatever their Rust declaration (e.g.
    [alloc::alloc::Global] is a unit struct, but its Lean model is a named
    type). *)
let type_is_tuple_like (ctx : extraction_ctx) (ty : ty) : bool =
  match ty with
  | TAdt (TTuple, _) -> true
  | TAdt ((TAdtId decl_id as id), _) ->
      (match TypeDeclId.Map.find_opt decl_id ctx.trans_types with
        | Some { builtin_info = Some _; _ } -> false
        | _ -> true)
      && type_decl_from_type_id_is_tuple_struct
           ctx.trans_ctx.type_ctx.type_infos id
  | _ -> false

(** The index of the first element of a list satisfying a predicate *)
let list_index (f : 'a -> bool) (l : 'a list) : int option =
  let rec go i l =
    match l with
    | [] -> None
    | x :: l -> if f x then Some i else go (i + 1) l
  in
  go 0 l

(** [Some (List.map f l)] if [f] succeeds on all the elements, [None] otherwise
*)
let list_map_opt (f : 'a -> 'b option) (l : 'a list) : 'b list option =
  let l = List.map f l in
  if List.for_all Option.is_some l then Some (List.map Option.get l) else None

(** The deep scalar type of an integer type: [(.u .U32)], [(.i .I32)], ... *)
let scalar_ty_str (ty : integer_type) : string =
  if Scalars.integer_type_is_signed ty then "(.i ." ^ int_name ty ^ ")"
  else "(.u ." ^ int_name ty ^ ")"

(** {1 The closed world of types} *)

(** A type declaration of the closed world (a constructor of [TypeName]) *)
type closed_type_info = {
  ctor_name : string;  (** The constructor of [TypeName] (crate types) *)
  ref : string;
      (** The type as an [Aeneas.Deep.TypeRef]: [(.crate TypeName.X)] or
          [(.builtin .option)] *)
  is_builtin : bool;
      (** Is it one of the builtin types the library describes (see
          {!builtin_type_refs})? Those are not in [TypeName] and their instances
          come from the library. *)
  decl : type_decl;
  mutable has_variants : bool;
      (** Do we describe the variants of the type and generate its
          constructor/projector/eliminator instances? False for the opaque types
          and for the types whose fields have types we can't describe. *)
  keep_types : bool list option;
      (** The filter on the type arguments (builtin types may drop some of their
          parameters, for instance the allocator of [Vec]) *)
}

(** The closed world of the crate being extracted, computed by
    {!extract_type_names} at the beginning of the deep section (the printer is
    not reentrant, like the shallow printer's global configuration). *)
let closed_world : closed_type_info TypeDeclId.Map.t ref =
  ref (TypeDeclId.Map.of_list [])

let closed_type_info (id : TypeDeclId.id) : closed_type_info option =
  TypeDeclId.Map.find_opt id !closed_world

(** The type arguments actually printed for an ADT (see [keep_types]) *)
let filter_type_args (keep : bool list option) (l : 'a list) : 'a list =
  match keep with
  | None -> l
  | Some keep ->
      let rec go keep l =
        match (keep, l) with
        | b :: keep, x :: l -> if b then x :: go keep l else go keep l
        | _, l -> l
      in
      go keep l

(** The builtin types the library describes ([Aeneas.Deep.BuiltinTy]),
    identified by their Lean name: the constructor of [BuiltinTy], and whether
    the library describes their variants (constructors, projectors and
    eliminator). The other builtin types are in the crate's enumeration of type
    names, without variants. *)
let builtin_type_refs : (string * string * bool) list =
  [
    ("Option", ".option", true);
    ("alloc.vec.Vec", ".vec", false);
    ("core.ops.range.Range", ".range", true);
    ("Ordering", ".ordering", true);
  ]

(** The builtin functions the library describes ([Aeneas.Deep.Prim]), identified
    by their Lean name (the pure builtins of the translation, like [toResult] or
    the array accessors, are handled separately). *)
let prim_table : (string * string) list =
  [
    ("Array.repeat", ".arrayRepeat");
    ("Array.to_slice", ".arrayToSlice");
    ("Slice.len", ".sliceLen");
    ("alloc.vec.Vec.len", ".vecLen");
    ("alloc.vec.Vec.push", ".vecPush");
    ("alloc.vec.Vec.new", ".vecNew");
  ]

(** The name of the generated enumerations of the function and global names *)
let fun_name_enum = "FunName"

let global_name_enum = "GlobalName"

(** A Lean name as a constructor of one of the generated enumerations: the dots
    are replaced by underscores *)
let name_ctor (enum : string) (name : string) : string =
  let is_ident_char (c : char) =
    (c >= 'a' && c <= 'z')
    || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9')
    || c = '_' || c = '\''
  in
  (* Lean names may contain quoted components ([«x86_64-tables»]): we keep
     only the identifier characters *)
  let name = String.map (fun c -> if is_ident_char c then c else '_') name in
  enum ^ "." ^ name

(** The constructor of [TypeName] for a type declaration *)
let type_name_ctor (name : string) : string = name_ctor type_name_enum name

(** A function of the closed world (a constructor of [FunName]) *)
type closed_fun_info = {
  fun_ctor : string;  (** The constructor of [FunName] (crate functions) *)
  fun_ref : string;
      (** The function as an [Aeneas.Deep.FunRef]: [(.crate FunName.f)] or
          [(.prim .vecLen)] *)
  is_prim : bool;
  keep_fun_types : bool list option;
      (** The filter on the type arguments of the calls (builtin functions may
          drop some of their parameters) *)
  fun_decl : fun_decl;
  loop : (LoopId.id * bool) option;
}

(** The closed world of functions, keyed by the function id and the loop
    information (see {!regular_fun_id}), computed by {!extract_closed_world} *)
let fun_world : (int * (int * bool) option, closed_fun_info) Hashtbl.t =
  Hashtbl.create 64

let fun_world_key (id : FunDeclId.id) (lp : (LoopId.id * bool) option) :
    int * (int * bool) option =
  (FunDeclId.to_int id, Option.map (fun (lp, b) -> (LoopId.to_int lp, b)) lp)

let closed_fun_info (id : FunDeclId.id) (lp : (LoopId.id * bool) option) :
    closed_fun_info option =
  Hashtbl.find_opt fun_world (fun_world_key id lp)

(** A global of the closed world (a constructor of [GlobalName]) *)
type closed_global_info = { global_ctor : string; global : global_decl }

let global_world : closed_global_info GlobalDeclId.Map.t ref =
  ref (GlobalDeclId.Map.of_list [])

let closed_global_info (id : GlobalDeclId.id) : closed_global_info option =
  GlobalDeclId.Map.find_opt id !global_world

(** {1 Type descriptors} *)

(** The type environment of a deep term: how the type and const-generic
    variables are mapped to the binders of the [Aeneas.Deep.TyEnv] of the term.
    The binders are the type parameters of the definition, followed by the types
    which the descriptors can not express ("escaped" types), which are
    discovered while printing the body. *)
type deep_tyenv = {
  ty_params : TypeVarId.id list;  (** The type parameters, in binding order *)
  cg_params : ConstGenericVarId.id list;
  mutable ty_escapes : ty list;  (** The escaped types, in order *)
  mutable cg_escapes : const_generic list;
  allow_escapes : bool;
      (** [false] when describing the fields of a type declaration (the
          descriptors must be closed) *)
}

let mk_deep_tyenv (generics : generic_params) (allow_escapes : bool) :
    deep_tyenv =
  {
    ty_params = List.map (fun (p : type_param) -> p.index) generics.types;
    cg_params =
      List.map
        (fun (p : const_generic_param) -> p.index)
        generics.const_generics;
    ty_escapes = [];
    cg_escapes = [];
    allow_escapes;
  }

let escape_ty (tenv : deep_tyenv) (ty : ty) : string option =
  if not tenv.allow_escapes then None
  else
    let i =
      match list_index (fun ty' -> compare_ty ty ty' = 0) tenv.ty_escapes with
      | Some i -> i
      | None ->
          tenv.ty_escapes <- tenv.ty_escapes @ [ ty ];
          List.length tenv.ty_escapes - 1
    in
    Some ("(.var " ^ string_of_int (List.length tenv.ty_params + i) ^ ")")

let escape_cg (tenv : deep_tyenv) (cg : const_generic) : string option =
  if not tenv.allow_escapes then None
  else
    let i =
      match
        list_index (fun cg' -> compare_const_generic cg cg' = 0) tenv.cg_escapes
      with
      | Some i -> i
      | None ->
          tenv.cg_escapes <- tenv.cg_escapes @ [ cg ];
          List.length tenv.cg_escapes - 1
    in
    Some ("(.var " ^ string_of_int (List.length tenv.cg_params + i) ^ ")")

(** The descriptor of a type ([Aeneas.Deep.Ty]), if it can be expressed. In a
    definition (where escapes are allowed), the inexpressible atoms become type
    variables and the result is always [Some]. *)
let rec deep_ty (span : Meta.span) (ctx : extraction_ctx) (tenv : deep_tyenv)
    (ty : ty) : string option =
  let list (l : string list) = "[" ^ String.concat ", " l ^ "]" in
  match ty with
  | TVar (Free id) -> (
      match
        list_index
          (fun id' -> TypeVarId.to_int id = TypeVarId.to_int id')
          tenv.ty_params
      with
      | Some i -> Some ("(.var " ^ string_of_int i ^ ")")
      | None -> escape_ty tenv ty)
  | TVar (Bound _) -> escape_ty tenv ty
  | TLiteral lty -> (
      match lty with
      | TInt _ | TUInt _ ->
          Some ("(.scalar " ^ scalar_ty_str (literal_as_integer lty) ^ ")")
      | TBool -> Some ".bool"
      | TChar -> Some ".char"
      | _ -> escape_ty tenv ty)
  | TAdt (TTuple, { types; _ }) -> (
      match types with
      | [] -> Some ".unit"
      | [ ty ] -> deep_ty span ctx tenv ty
      | _ ->
          Option.map
            (fun tys -> "(.tuple " ^ list tys ^ ")")
            (list_map_opt (deep_ty span ctx tenv) types))
  | TAdt (TAdtId id, generics) when type_is_tuple_like ctx ty -> (
      (* A tuple struct: the tuple of its fields *)
      match TypeDeclId.Map.find_opt id ctx.trans_types with
      | None -> escape_ty tenv ty
      | Some decl ->
          let fields =
            type_decl_get_instantiated_fields_types decl None generics
          in
          deep_ty span ctx tenv
            (TAdt (TTuple, { generics with types = fields })))
  | TAdt (TAdtId id, generics) -> (
      match closed_type_info id with
      | None -> escape_ty tenv ty
      | Some info -> (
          let types = filter_type_args info.keep_types generics.types in
          match
            ( list_map_opt (deep_ty span ctx tenv) types,
              list_map_opt (deep_cg span ctx tenv) generics.const_generics )
          with
          | Some targs, Some cargs ->
              Some
                ("(.adt " ^ info.ref ^ " " ^ list targs ^ " " ^ list cargs ^ ")")
          | _ -> escape_ty tenv ty))
  | TAdt (TBuiltin TArray, { types = [ elem ]; const_generics = [ n ]; _ }) -> (
      match (deep_ty span ctx tenv elem, deep_cg span ctx tenv n) with
      | Some elem, Some n -> Some ("(.array " ^ elem ^ " " ^ n ^ ")")
      | _ -> escape_ty tenv ty)
  | TAdt (TBuiltin TSlice, { types = [ elem ]; _ }) -> (
      match deep_ty span ctx tenv elem with
      | Some elem -> Some ("(.slice " ^ elem ^ ")")
      | None -> escape_ty tenv ty)
  | TAdt (TBuiltin TStr, _) -> Some ".str"
  | TAdt (TBuiltin TResult, { types = [ elem ]; _ }) -> (
      match deep_ty span ctx tenv elem with
      | Some elem -> Some ("(.result " ^ elem ^ ")")
      | None -> escape_ty tenv ty)
  | TAdt (TBuiltin TLoopResult, { types = [ a; b ]; _ }) -> (
      match (deep_ty span ctx tenv a, deep_ty span ctx tenv b) with
      | Some a, Some b -> Some ("(.controlFlow " ^ a ^ " " ^ b ^ ")")
      | _ -> escape_ty tenv ty)
  | TAdt (TBuiltin _, _) -> escape_ty tenv ty
  | TArrow (a, b) -> (
      match (deep_ty span ctx tenv a, deep_ty span ctx tenv b) with
      | Some a, Some b -> Some ("(.arrow " ^ a ^ " " ^ b ^ ")")
      | _ -> escape_ty tenv ty)
  | TTraitType _ | TNever | TDynTrait _ | TError -> escape_ty tenv ty

(** The descriptor of a const-generic argument ([Aeneas.Deep.CArg]) *)
and deep_cg (_span : Meta.span) (_ctx : extraction_ctx) (tenv : deep_tyenv)
    (cg : const_generic) : string option =
  match cg with
  | CgValue (VScalar sv) ->
      Some ("(.lit " ^ Z.to_string (Scalars.get_val sv) ^ " (by decide))")
  | CgVar (Free id) -> (
      match
        list_index
          (fun id' ->
            ConstGenericVarId.to_int id = ConstGenericVarId.to_int id')
          tenv.cg_params
      with
      | Some i -> Some ("(.var " ^ string_of_int i ^ ")")
      | None -> escape_cg tenv cg)
  | _ -> escape_cg tenv cg

(** The descriptor of a type, in a definition (always succeeds) *)
let deep_ty_def (span : Meta.span) (ctx : extraction_ctx) (tenv : deep_tyenv)
    (ty : ty) : string =
  [%unwrap_with_span] span (deep_ty span ctx tenv ty)
    "Could not compute the type descriptor"

(** Print the type environment of a deep term:
    [⟨[T1, ..., Tn, ESC1, ...], [N1, ..., CESC1, ...]⟩] *)
let extract_deep_tyenv (span : Meta.span) (ctx : extraction_ctx)
    (fmt : F.formatter) (tenv : deep_tyenv) : unit =
  let sep () =
    F.pp_print_string fmt ",";
    F.pp_print_space fmt ()
  in
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt "⟨[";
  Collections.List.iter_link sep
    (fun id -> F.pp_print_string fmt (ctx_get_type_var span Item id ctx))
    tenv.ty_params;
  if tenv.ty_params <> [] && tenv.ty_escapes <> [] then sep ();
  Collections.List.iter_link sep
    (fun ty ->
      extract_ty span ctx fmt TypeDeclId.TreeSet.empty ~inside:false ty)
    tenv.ty_escapes;
  F.pp_print_string fmt "],";
  F.pp_print_space fmt ();
  F.pp_print_string fmt "[";
  Collections.List.iter_link sep
    (fun id ->
      F.pp_print_string fmt (ctx_get_const_generic_var span Item id ctx))
    tenv.cg_params;
  if tenv.cg_params <> [] && tenv.cg_escapes <> [] then sep ();
  Collections.List.iter_link sep
    (fun cg -> extract_const_generic span ctx fmt ~inside:false cg)
    tenv.cg_escapes;
  F.pp_print_string fmt "]⟩";
  F.pp_close_box fmt ()

(** Print the type and const-generic arguments of an ADT, as descriptors:
    [[T1, T2] [N1]] *)
let deep_adt_args (span : Meta.span) (ctx : extraction_ctx) (tenv : deep_tyenv)
    (info : closed_type_info) (generics : generic_args) : string =
  let list (l : string list) = "[" ^ String.concat ", " l ^ "]" in
  let types = filter_type_args info.keep_types generics.types in
  list (List.map (deep_ty_def span ctx tenv) types)
  ^ " "
  ^ list
      (List.map
         (fun cg ->
           [%unwrap_with_span] span (deep_cg span ctx tenv cg)
             "Could not compute the const-generic descriptor")
         generics.const_generics)

(** {1 The closed world: the enumeration of the type names and its instances} *)

let type_decl_variants_fields (decl : type_decl) : field list list =
  match decl.kind with
  | Struct fields -> [ fields ]
  | Enum variants -> List.map (fun (v : variant) -> v.fields) variants
  | Opaque -> []

(** Compute the closed world and print it at the beginning of the deep section.
    The types:
    {[
      inductive TypeName where
        | Foo
        | Bar

      instance : Aeneas.Deep.TypeNames TypeName where
        denote
          | .Foo, ρ => Foo (Aeneas.Deep.tyAt ρ.types 0)
          | .Bar, _ => Bar
        variants
          | .Foo => [[.var 0, .adt TypeName.Foo [.var 0] []], []]
          | .Bar => []

      instance : Aeneas.Deep.CtorFn TypeName TypeName.Foo 0 := ⟨fun _ => fun a0 a1 => Foo.Cons a0 a1⟩
      ...
      instance : Aeneas.Deep.ElimFn TypeName TypeName.Foo :=
        ⟨fun _ => fun x alts => Foo.casesOn x alts.1 alts.2.1⟩
    ]}
    The closed world contains all the type declarations (local, builtin and
    opaque) except the tuple structs (which are tuples) and the types with trait
    clauses (we don't describe trait instances). The variants are described, and
    the instances generated, for the inductive types whose field types can all
    be described.

    Then the functions and the globals:
    {[
      inductive FunName where
        | foo
        | bar_loop

      instance : Aeneas.Deep.FunNames FunName TypeName where
        defs
          | FunName.foo => ⟨⟨[(.var 0)], (.result (.var 0))⟩, fun ρ => @foo (Aeneas.Deep.tyAt ρ.types 0)⟩
          ...

      inductive GlobalName where
        | X

      instance : Aeneas.Deep.GlobalNames GlobalName TypeName where
        defs
          | GlobalName.X => ⟨(.scalar (.u .U32)), fun _ => X⟩
    ]}
    The functions (including the ones generated for loops and loop bodies, and
    the opaque ones) and the globals without trait clauses, whose signatures can
    be described, are in the closed world. The builtin functions (standard
    library models) are not. *)
let extract_closed_world (ctx : extraction_ctx) (fmt : F.formatter) : unit =
  (* The closed world *)
  let infos =
    List.filter_map
      (fun (id, (decl : type_decl)) ->
        let span = decl.item_meta.span in
        if
          type_is_tuple_like ctx (TAdt (TAdtId id, empty_generic_args))
          || decl.generics.trait_clauses <> []
        then None
        else
          let name =
            try Some (ctx_get_type (Some span) (TAdtId id) ctx)
            with Errors.CFailure _ -> None
          in
          match name with
          | None -> None
          | Some name -> (
              let keep_types =
                TypeDeclId.TreeMap.find_opt id ctx.types_filter_type_args_map
              in
              match
                List.find_opt (fun (n, _, _) -> n = name) builtin_type_refs
              with
              | Some (_, b, has_variants) when decl.builtin_info <> None ->
                  Some
                    ( id,
                      {
                        ctor_name = "";
                        ref = "(.builtin " ^ b ^ ")";
                        is_builtin = true;
                        decl;
                        has_variants;
                        keep_types;
                      } )
              | _ ->
                  let has_variants =
                    match (decl.kind, decl.builtin_info) with
                    | (Struct _ | Enum _), None -> true
                    | _ -> false
                  in
                  let ctor_name = type_name_ctor name in
                  Some
                    ( id,
                      {
                        ctor_name;
                        ref = "(.crate " ^ ctor_name ^ ")";
                        is_builtin = false;
                        decl;
                        has_variants;
                        keep_types;
                      } )))
      (TypeDeclId.Map.bindings ctx.trans_types)
  in
  closed_world := TypeDeclId.Map.of_list infos;
  let crate_infos = List.filter (fun (_, info) -> not info.is_builtin) infos in
  (* The descriptors of the fields, over the parameters of the declarations.
     The types whose fields can't be described lose their variants. *)
  let infos =
    List.map
      (fun (id, info) ->
        if not info.has_variants then (id, info, [])
        else
          let tenv = mk_deep_tyenv info.decl.generics false in
          let span = info.decl.item_meta.span in
          let variants =
            list_map_opt
              (fun fields ->
                list_map_opt
                  (fun (f : field) -> deep_ty span ctx tenv f.field_ty)
                  fields)
              (type_decl_variants_fields info.decl)
          in
          match variants with
          | Some variants -> (id, info, variants)
          | None ->
              info.has_variants <- false;
              (id, info, []))
      crate_infos
  in
  let list (l : string list) = "[" ^ String.concat ", " l ^ "]" in
  (* The enumeration *)
  F.pp_print_break fmt 0 0;
  F.pp_print_string fmt "/-- The type declarations of the crate -/";
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt ("inductive " ^ type_name_enum ^ " where");
  List.iter
    (fun (_, info, _) ->
      F.pp_print_cut fmt ();
      F.pp_print_string fmt
        ("| "
        ^ String.sub info.ctor_name
            (String.length type_name_enum + 1)
            (String.length info.ctor_name - String.length type_name_enum - 1)))
    infos;
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0;
  (* The [TypeNames] instance *)
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("instance : " ^ deep_prefix ^ "TypeNames " ^ type_name_enum ^ " where");
  F.pp_print_cut fmt ();
  if infos = [] then (
    F.pp_print_string fmt "denote t _ := nomatch t";
    F.pp_print_cut fmt ();
    F.pp_print_string fmt "variants t := nomatch t")
  else (
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt "denote";
    List.iter
      (fun (id, info, _) ->
        let span = info.decl.item_meta.span in
        let name = ctx_get_type (Some span) (TAdtId id) ctx in
        let types = filter_type_args info.keep_types info.decl.generics.types in
        let num_cgs = List.length info.decl.generics.const_generics in
        F.pp_print_cut fmt ();
        F.pp_open_hovbox fmt ctx.indent_incr;
        F.pp_print_string fmt
          ("| " ^ info.ctor_name ^ ", "
          ^ (if types = [] && num_cgs = 0 then "_" else "ρ")
          ^ " => " ^ name);
        List.iteri
          (fun i _ ->
            F.pp_print_space fmt ();
            F.pp_print_string fmt
              ("(" ^ deep_prefix ^ "tyAt ρ.types " ^ string_of_int i ^ ")"))
          types;
        for i = 0 to num_cgs - 1 do
          F.pp_print_space fmt ();
          F.pp_print_string fmt
            ("(ρ.consts.getD " ^ string_of_int i ^ " (Std.Usize.ofNat 0))")
        done;
        F.pp_close_box fmt ())
      infos;
    F.pp_close_box fmt ();
    F.pp_print_cut fmt ();
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt "variants";
    List.iter
      (fun (_, info, variants) ->
        F.pp_print_cut fmt ();
        F.pp_open_hovbox fmt ctx.indent_incr;
        F.pp_print_string fmt ("| " ^ info.ctor_name ^ " =>");
        F.pp_print_space fmt ();
        F.pp_print_string fmt (list (List.map list variants));
        F.pp_close_box fmt ())
      infos;
    F.pp_close_box fmt ());
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0;
  (* The instances *)
  List.iter
    (fun (id, info, _) ->
      if info.has_variants && not info.is_builtin then (
        let span = info.decl.item_meta.span in
        let name = ctx_get_type (Some span) (TAdtId id) ctx in
        let variants = type_decl_variants_fields info.decl in
        let print_instance (cls : string) (args : string) (body : string) =
          F.pp_print_break fmt 0 0;
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt
            ("instance : " ^ deep_prefix ^ cls ^ " " ^ type_name_enum ^ " "
           ^ info.ref ^ args ^ " :=");
          F.pp_print_space fmt ();
          F.pp_print_string fmt ("⟨fun _ => " ^ body ^ "⟩");
          F.pp_close_box fmt ()
        in
        (* Constructors *)
        List.iteri
          (fun vid (fields : field list) ->
            let cons =
              match info.decl.kind with
              | Enum _ ->
                  ctx_get_variant span (TAdtId id) (VariantId.of_int vid) ctx
              | _ -> ctx_get_struct span (TAdtId id) ctx
            in
            let args = List.mapi (fun i _ -> "a" ^ string_of_int i) fields in
            let body =
              if args = [] then cons
              else
                "fun " ^ String.concat " " args ^ " => " ^ cons ^ " "
                ^ String.concat " " args
            in
            print_instance "CtorFn" (" " ^ string_of_int vid) body)
          variants;
        (* Projectors *)
        (match info.decl.kind with
        | Struct fields ->
            List.iteri
              (fun i _ ->
                let field =
                  ctx_get_field span (TAdtId id) (FieldId.of_int i) ctx
                in
                print_instance "ProjFn"
                  (" " ^ string_of_int i)
                  ("fun x => x." ^ field))
              fields
        | _ -> ());
        (* Eliminator *)
        let alts =
          List.mapi
            (fun i _ ->
              "alts" ^ String.concat "" (List.init i (fun _ -> ".2")) ^ ".1")
            variants
        in
        print_instance "ElimFn" ""
          ("fun x alts => " ^ name ^ ".casesOn x " ^ String.concat " " alts)))
    infos;
  F.pp_print_break fmt 0 0;
  (*
   * The functions
   *)
  Hashtbl.reset fun_world;
  let funs =
    List.concat_map
      (fun (id, (trans : TranslateCore.fun_and_loops)) ->
        (trans.f, None)
        :: List.mapi
             (fun i (f : fun_decl) -> (f, Some (LoopId.of_int i, false)))
             trans.loops
        @ List.mapi
            (fun i (f : fun_decl) -> (f, Some (LoopId.of_int i, true)))
            trans.bodies
        |> List.filter_map (fun ((decl : fun_decl), lp) ->
            let span = decl.item_meta.span in
            (* The builtin functions the library describes *)
            let prim =
              match decl.builtin_info with
              | Some bi -> List.assoc_opt bi.extract_name prim_table
              | None -> None
            in
            (* The Lean models of the primitives don't take the trait
               instances of the Rust signature (e.g. [Clone] for
               [core::array::repeat]) *)
            if
              (decl.builtin_info <> None && prim = None)
              || decl.is_global_decl_body
              || (prim = None && decl.signature.generics.trait_clauses <> [])
            then None
            else
              let name =
                match prim with
                | Some _ -> Some ""
                | None -> (
                    try Some (ctx_get_local_function span id lp ctx)
                    with Errors.CFailure _ -> None)
              in
              let tenv = mk_deep_tyenv decl.signature.generics false in
              match
                ( name,
                  list_map_opt (deep_ty span ctx tenv) decl.signature.inputs,
                  deep_ty span ctx tenv decl.signature.output )
              with
              | Some name, Some inputs, Some output ->
                  let fun_ctor, fun_ref =
                    match prim with
                    | Some p -> ("", "(.prim " ^ p ^ ")")
                    | None ->
                        let c = name_ctor fun_name_enum name in
                        (c, "(.crate " ^ c ^ ")")
                  in
                  let info =
                    {
                      fun_ctor;
                      fun_ref;
                      is_prim = prim <> None;
                      keep_fun_types =
                        FunDeclId.TreeMap.find_opt id
                          ctx.funs_filter_type_args_map;
                      fun_decl = decl;
                      loop = lp;
                    }
                  in
                  Hashtbl.add fun_world (fun_world_key id lp) info;
                  if prim <> None then None
                  else Some (name, info, inputs, output)
              | _ -> None))
      (FunDeclId.Map.bindings ctx.trans_funs)
  in
  (* The interpretation of the parameters of a declaration, as arguments:
     [(Aeneas.Deep.tyAt ρ.types 0) ... (ρ.consts.getD 0 (Std.Usize.ofNat 0))] *)
  let print_params (generics : generic_params) : unit =
    List.iteri
      (fun i _ ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt
          ("(" ^ deep_prefix ^ "tyAt ρ.types " ^ string_of_int i ^ ")"))
      generics.types;
    List.iteri
      (fun i _ ->
        F.pp_print_space fmt ();
        F.pp_print_string fmt
          ("(ρ.consts.getD " ^ string_of_int i ^ " (Std.Usize.ofNat 0))"))
      generics.const_generics
  in
  let has_params (generics : generic_params) : bool =
    generics.types <> [] || generics.const_generics <> []
  in
  let strip (enum : string) (ctor : string) : string =
    String.sub ctor
      (String.length enum + 1)
      (String.length ctor - String.length enum - 1)
  in
  F.pp_print_break fmt 0 0;
  F.pp_print_string fmt "/-- The functions of the crate -/";
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt ("inductive " ^ fun_name_enum ^ " where");
  List.iter
    (fun (_, info, _, _) ->
      F.pp_print_cut fmt ();
      F.pp_print_string fmt ("| " ^ strip fun_name_enum info.fun_ctor))
    funs;
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0;
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("instance : " ^ deep_prefix ^ "FunNames " ^ fun_name_enum ^ " "
   ^ type_name_enum ^ " where");
  F.pp_print_cut fmt ();
  (* The implementation at the interpretation [ρ] of the parameters:
     [fun ρ => @NAME (ρ.types.getD 0 Unit) ...] *)
  let print_impl (name : string) (generics : generic_params) : unit =
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt
      ("fun "
      ^ (if has_params generics then "ρ" else "_")
      ^ " => "
      ^ (if has_params generics then "@" else "")
      ^ name);
    print_params generics;
    F.pp_close_box fmt ()
  in
  if funs = [] then F.pp_print_string fmt "defs f := nomatch f"
  else (
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt "defs";
    List.iter
      (fun (name, info, inputs, output) ->
        F.pp_print_cut fmt ();
        F.pp_open_hovbox fmt ctx.indent_incr;
        F.pp_print_string fmt ("| " ^ info.fun_ctor ^ " =>");
        F.pp_print_space fmt ();
        F.pp_print_string fmt ("⟨⟨" ^ list inputs ^ ",");
        F.pp_print_space fmt ();
        F.pp_print_string fmt (output ^ "⟩,");
        F.pp_print_space fmt ();
        print_impl name info.fun_decl.signature.generics;
        F.pp_print_string fmt "⟩";
        F.pp_close_box fmt ())
      funs;
    F.pp_close_box fmt ());
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0;
  (*
   * The globals
   *)
  let globals =
    List.filter_map
      (fun (id, (global : global_decl)) ->
        let span = global.span in
        (* The anonymous (promoted) constants are not extracted: their reads
           are inlined (see [Translate.export_global]) *)
        let is_anon_const =
          match
            GlobalDeclId.Map.find_opt id ctx.trans_ctx.crate.global_decls
          with
          | Some g -> LlbcAstUtils.global_decl_is_anon_const g
          | None -> false
        in
        if
          global.builtin_info <> None
          || global.generics.trait_clauses <> []
          || is_anon_const
        then None
        else
          let name =
            try Some (ctx_get_global span id ctx)
            with Errors.CFailure _ -> None
          in
          let tenv = mk_deep_tyenv global.generics false in
          match (name, deep_ty span ctx tenv global.ty) with
          | Some name, Some ty ->
              Some
                ( name,
                  { global_ctor = name_ctor global_name_enum name; global },
                  ty )
          | _ -> None)
      (GlobalDeclId.Map.bindings ctx.trans_globals)
  in
  global_world :=
    GlobalDeclId.Map.of_list
      (List.map (fun (_, info, _) -> (info.global.def_id, info)) globals);
  F.pp_print_break fmt 0 0;
  F.pp_print_string fmt "/-- The globals of the crate -/";
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt ("inductive " ^ global_name_enum ^ " where");
  List.iter
    (fun (_, info, _) ->
      F.pp_print_cut fmt ();
      F.pp_print_string fmt ("| " ^ strip global_name_enum info.global_ctor))
    globals;
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0;
  F.pp_print_break fmt 0 0;
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("instance : " ^ deep_prefix ^ "GlobalNames " ^ global_name_enum ^ " "
   ^ type_name_enum ^ " where");
  F.pp_print_cut fmt ();
  if globals = [] then F.pp_print_string fmt "defs g := nomatch g"
  else (
    F.pp_open_vbox fmt ctx.indent_incr;
    F.pp_print_string fmt "defs";
    List.iter
      (fun (name, info, ty) ->
        F.pp_print_cut fmt ();
        F.pp_open_hovbox fmt ctx.indent_incr;
        F.pp_print_string fmt ("| " ^ info.global_ctor ^ " =>");
        F.pp_print_space fmt ();
        F.pp_print_string fmt ("⟨" ^ ty ^ ",");
        F.pp_print_space fmt ();
        print_impl name info.global.generics;
        F.pp_print_string fmt "⟩";
        F.pp_close_box fmt ())
      globals;
    F.pp_close_box fmt ());
  F.pp_close_box fmt ();
  F.pp_print_break fmt 0 0

(** {1 Patterns and leaves} *)

(** Translate a pattern to a deep pattern, if supported.

    Returns the list of the variables bound by the pattern, in binding order
    (which is the order of the environment extension), together with a printer
    for the deep pattern. *)
let rec deep_pat (span : Meta.span) (ctx : extraction_ctx) (p : tpat) :
    (fvar list * (F.formatter -> unit)) option =
  match p.pat with
  | POpen (v, _) -> Some ([ v ], fun fmt -> F.pp_print_string fmt ".var")
  | PIgnored -> Some ([], fun fmt -> F.pp_print_string fmt ".ignore")
  | PAdt { variant_id = None; fields } when type_is_tuple_like ctx p.ty -> (
      match fields with
      | [] -> Some ([], fun fmt -> F.pp_print_string fmt ".ignore")
      | [ f ] -> deep_pat span ctx f
      | _ -> (
          match list_map_opt (deep_pat span ctx) fields with
          | None -> None
          | Some pats ->
              Some
                ( List.concat_map fst pats,
                  fun fmt ->
                    F.pp_print_string fmt "(.tuple ";
                    List.iter
                      (fun (_, p) ->
                        F.pp_print_string fmt "(.cons ";
                        p fmt;
                        F.pp_print_space fmt ())
                      pats;
                    F.pp_print_string fmt ".nil";
                    List.iter (fun _ -> F.pp_print_string fmt ")") pats;
                    F.pp_print_string fmt ")" )))
  | PConstant _ | PBound _ | PAdt _ -> None

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
    function of the environment.

    We bind the variables of the environment with let-bindings rather than with
    a pattern-matching lambda ([fun | x ::ₑ y ::ₑ .nil => ...]): pattern
    matching on long environments makes Lean generate matchers which the kernel
    rejects (observed with 14 variables). The name of the environment is quoted
    so that it can't clash with a variable name coming from Rust.
    {[
      (.shallow TY (fun «deep env» =>
        let x := Aeneas.Deep.Var.get .zero «deep env»
        let y := Aeneas.Deep.Var.get (.succ .zero) «deep env»
        (BODY : T)))
    ]}
    [ty] is the type of the expression (the expected type when it is known). *)
let extract_deep_escape (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (env : denv) (fmt : F.formatter) (ty : ty) (e : texpr) :
    unit =
  let env_name = "«deep env»" in
  F.pp_open_vbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("(.shallow " ^ deep_ty_def span ctx tenv ty ^ " (fun " ^ env_name ^ " =>");
  List.iteri
    (fun i id ->
      F.pp_print_cut fmt ();
      F.pp_print_string fmt
        ("let " ^ ctx_get_var span id ctx ^ " := " ^ deep_prefix ^ "Var.get ");
      extract_var_index fmt i;
      F.pp_print_string fmt (" " ^ env_name))
    env;
  F.pp_print_cut fmt ();
  (* The body is annotated with its shallow type: the expected type coming
     from the node is the (reducible) denotation of a descriptor, which the
     tactics of the auto-parameters of the shallow code (array literals, ...)
     don't see through *)
  extract_annotated_shallow span ctx fmt { e with ty };
  F.pp_print_string fmt "))";
  F.pp_close_box fmt ()

(** The deep node for a binary operation, if there is one: the constructor and
    its data, to be applied to the two deep arguments. *)
let deep_binop (binop : binop) : string option =
  match binop with
  | Add (OPanic, ty) -> Some (".scalarBinop .add " ^ scalar_ty_str ty)
  | Sub (OPanic, ty) -> Some (".scalarBinop .sub " ^ scalar_ty_str ty)
  | Mul (OPanic, ty) -> Some (".scalarBinop .mul " ^ scalar_ty_str ty)
  | Div (OPanic, ty) -> Some (".scalarBinop .div " ^ scalar_ty_str ty)
  | Rem (OPanic, ty) -> Some (".scalarBinop .rem " ^ scalar_ty_str ty)
  | Shl (OPanic, ty, rhs) ->
      Some (".scalarBinop (.shl " ^ scalar_ty_str rhs ^ ") " ^ scalar_ty_str ty)
  | Shr (OPanic, ty, rhs) ->
      Some (".scalarBinop (.shr " ^ scalar_ty_str rhs ^ ") " ^ scalar_ty_str ty)
  | BitAnd ty -> Some (".scalarBitop .and " ^ scalar_ty_str ty)
  | BitOr ty -> Some (".scalarBitop .or " ^ scalar_ty_str ty)
  | BitXor ty -> Some (".scalarBitop .xor " ^ scalar_ty_str ty)
  | BoolAnd -> Some ".boolBinop .and"
  | BoolOr -> Some ".boolBinop .or"
  | BoolXor -> Some ".boolBinop .xor"
  | Ne _ -> Some ".bne"
  | _ -> None

(** The deep node for a unary operation, if there is one *)
let deep_unop (unop : unop) : string option =
  match unop with
  | Neg ty when Scalars.integer_type_is_signed ty ->
      Some (".neg ." ^ int_name ty)
  | Not (Some ty) -> Some (".bitNot " ^ scalar_ty_str ty)
  | Not None -> Some ".boolNot"
  | Cast (CastLit (src, tgt))
    when literal_type_is_integer src && literal_type_is_integer tgt ->
      let src = literal_as_integer src in
      let tgt = literal_as_integer tgt in
      Some (".cast " ^ scalar_ty_str src ^ " " ^ scalar_ty_str tgt)
  | Cast (CastLit (TBool, tgt)) when literal_type_is_integer tgt ->
      Some (".castFromBool " ^ scalar_ty_str (literal_as_integer tgt))
  | _ -> None

(** Print a literal as a deep node, if there is one ([.uscalarLit], ...).

    The bound of a scalar literal is discharged with [decide]: the bounds
    ([UScalar.cMax], ...) are concrete numbers for all the scalar types, the
    platform-dependent ones being approximated conservatively. *)
let extract_deep_literal (fmt : F.formatter) (lit : literal) : bool =
  match lit with
  | VScalar sv ->
      let ty = Scalars.get_ty sv in
      let v = Scalars.get_val sv in
      let cons =
        if Scalars.integer_type_is_signed ty then ".iscalarLit"
        else ".uscalarLit"
      in
      let v =
        if Z.lt v Z.zero then "(" ^ Z.to_string v ^ ")" else Z.to_string v
      in
      F.pp_print_string fmt
        ("(" ^ cons ^ " ." ^ int_name ty ^ " " ^ v ^ " (by decide))");
      true
  | VBool b ->
      F.pp_print_string fmt
        ("(.boolLit " ^ (if b then "true" else "false") ^ ")");
      true
  | _ -> false

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

(** The type [ty] such that the given type is [Result ty], if any *)
let unwrap_result_ty (ty : ty) : ty option =
  match ty with
  | TAdt (TBuiltin TResult, { types = [ ty ]; _ }) -> Some ty
  | _ -> None

(** {1 Matches} *)

(** An ADT of the closed world with variants, at some type arguments: we can
    match on it and construct it with the first-order nodes *)
type deep_adt_info = { info : closed_type_info; generics : generic_args }

(** Lookup the closed-world information for an ADT type, if it has variants *)
let deep_adt_info (ty : ty) : deep_adt_info option =
  match ty with
  | TAdt (TAdtId id, generics) -> (
      match closed_type_info id with
      | Some info when info.has_variants -> Some { info; generics }
      | _ -> None)
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
    - matches on types outside the closed world (or without variants)
    - matches with a default branch ([_ => ...]): Lean compiles those to an
      auxiliary definition which is not definitionally equal to a [casesOn]
    - matches on literals, nested patterns *)
let plan_deep_match (span : Meta.span) (fresh : unit -> fvar_id) (scrut : texpr)
    (branches : match_branch list) :
    (deep_adt_info * (fvar list * texpr) list) option =
  match deep_adt_info scrut.ty with
  | None -> None
  | Some info ->
      let num_variants = type_decl_num_variants info.info.decl in
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
    structure): returns the closed-world information and the variables bound by
    the fields. *)
let plan_deep_struct_pat (span : Meta.span) (ctx : extraction_ctx)
    (fresh : unit -> fvar_id) (pat : tpat) : (deep_adt_info * fvar list) option
    =
  match pat.pat with
  | PAdt { variant_id; fields } when not (type_is_tuple_like ctx pat.ty) -> (
      (* Structures, but also enumerations with a single variant: the shallow
         printer prints [let ⟨ x, y ⟩ := e] for both, and the elaboration is
         the same ([casesOn]) *)
      match deep_adt_info pat.ty with
      | Some info
        when type_decl_num_variants info.info.decl = 1
             && Option.fold ~none:true
                  ~some:(fun vid -> VariantId.to_int vid = 0)
                  variant_id ->
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

(** {1 Closed terms} *)

(** Is the expression closed data: literals and constructor applications
    (including array literals and structure values) without free variables? We
    use this to choose the tag of the leaves standing for closed terms. *)
let rec is_closed_data (e : texpr) : bool =
  match e.e with
  | Const _ -> true
  | Meta (_, e) -> is_closed_data e
  | Qualif { id = AdtCons _; _ } -> true
  | App _ -> (
      let app, args = destruct_apps e in
      match app.e with
      | Qualif { id = AdtCons _; _ } -> List.for_all is_closed_data args
      | _ -> false)
  | StructUpdate { init; updates; _ } ->
      Option.fold ~none:true ~some:is_closed_data init
      && List.for_all (fun (_, v) -> is_closed_data v) updates
  | _ -> false

(** The number of nodes of an expression *)
let rec texpr_num_nodes (e : texpr) : int =
  match e.e with
  | FVar _ | BVar _ | CVar _ | Const _ | Qualif _ | EError _ -> 1
  | Meta (_, e) -> texpr_num_nodes e
  | App (f, a) -> 1 + texpr_num_nodes f + texpr_num_nodes a
  | Lambda (_, b) -> 1 + texpr_num_nodes b
  | Let (_, _, e1, e2) -> 1 + texpr_num_nodes e1 + texpr_num_nodes e2
  | Switch (s, If (t, e)) ->
      1 + texpr_num_nodes s + texpr_num_nodes t + texpr_num_nodes e
  | Switch (s, Match brs) ->
      1 + texpr_num_nodes s
      + List.fold_left
          (fun n (br : match_branch) -> n + texpr_num_nodes br.branch)
          0 brs
  | StructUpdate { init; updates; _ } ->
      1
      + Option.fold ~none:0 ~some:texpr_num_nodes init
      + List.fold_left (fun n (_, v) -> n + texpr_num_nodes v) 0 updates
  | Loop _ -> 1

(** The number of let-bindings of an expression *)
let texpr_num_lets (e : texpr) : int =
  let count = ref 0 in
  let visitor =
    object
      inherit [_] iter_expr as super

      method! visit_Let env monadic pat e1 e2 =
        incr count;
        super#visit_Let env monadic pat e1 e2
    end
  in
  visitor#visit_texpr () e;
  !count

(** Is the expression closed (no free variables)? *)
let texpr_is_closed (e : texpr) : bool =
  FVarId.Set.subset (texpr_get_fvars e) (texpr_get_bound_fvars e)

(** Closed sub-expressions bigger than this (in number of nodes) are printed as
    a single shallow leaf rather than as a deep term: the denotation of a leaf
    is the term itself, so the theorem holds trivially, and the deep structure
    of large constant terms (precomputed tables, for instance) is of no interest
    while elaborating their deep terms is prohibitively expensive. *)
let closed_max_size = 64

(** Bodies with more than this many let-bindings are printed through the escape
    hatch: the deep term of a let-chain is quadratic in its length (every node
    carries its context), and the elaboration of chains of several hundreds of
    bindings exceeds the heartbeat budget. *)
let deep_max_lets = 500

(** The types of the pure builtins *)
let mk_usize_ty : ty = TLiteral (TUInt Usize)

let mk_array_or_slice_ty (kind : array_or_slice) (elem : ty)
    (const_generics : const_generic list) : ty =
  match kind with
  | Array ->
      TAdt
        (TBuiltin TArray, { types = [ elem ]; const_generics; trait_refs = [] })
  | Slice ->
      TAdt
        ( TBuiltin TSlice,
          { types = [ elem ]; const_generics = []; trait_refs = [] } )

(** {1 Expressions} *)

(** Print a deep expression.

    - [tenv]: the type environment of the deep term (see {!deep_tyenv})
    - [fresh]: generator of fresh variable ids, shared with the one used to open
      the binders of the function body.
    - [env]: the deep environment (see {!denv}). The extraction context [ctx]
      must contain names for all the variables of [env].
    - [expected]: the type expected by the context, when it is known (the type
      annotations of the application nodes are not always reliable after the
      micro-passes). *)
let rec extract_deep_texpr (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) ?(expected : ty option) (e : texpr) : unit =
  match e.e with
  | (App _ | Qualif _ | StructUpdate _ | Let _ | Switch _ | Lambda _)
    when texpr_num_nodes e > closed_max_size && texpr_is_closed e ->
      (* Large closed term: a single shallow leaf *)
      let ty = Option.value expected ~default:e.ty in
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt
        (if is_closed_data e then "(.lit" else "(.leaf (.other \"closed\")");
      F.pp_print_space fmt ();
      F.pp_print_string fmt (deep_ty_def span ctx tenv ty);
      F.pp_print_space fmt ();
      extract_annotated_shallow span ctx fmt { e with ty };
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | FVar id -> extract_deep_var fmt (denv_index span env id)
  | BVar _ -> [%internal_error] span
  | Const lit when extract_deep_literal fmt lit -> ()
  | CVar _ | Const _ ->
      F.pp_print_string fmt ("(.lit " ^ deep_ty_def span ctx tenv e.ty ^ " ");
      extract_texpr span ctx fmt ~inside:true ~inside_do:false e;
      F.pp_print_string fmt ")"
  | Meta (_, e) -> extract_deep_texpr span ctx tenv fresh env fmt ?expected e
  | Lambda _ ->
      let xl, body = raw_destruct_lambdas e in
      extract_deep_lambdas span ctx tenv fresh env fmt ?expected e xl body
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
      let ty = Option.value expected ~default:e.ty in
      match if binds_comparison then None else deep_pat span ctx pat with
      | None -> (
          (* Structure patterns: [let ⟨ a, b ⟩ := e] is a match with a single
             branch *)
          match
            if binds_comparison then None
            else plan_deep_struct_pat span ctx fresh pat
          with
          | None -> extract_deep_escape span ctx tenv env fmt ty e
          | Some (info, vs) ->
              if monadic then (
                (* [let ⟨ a, b ⟩ ← e; k] is elaborated to
                   [bind e (fun x => S.casesOn x (fun a b => k))] *)
                let x = { id = fresh (); basename = None; ty = pat.ty } in
                F.pp_open_hvbox fmt 0;
                F.pp_open_hovbox fmt ctx.indent_incr;
                F.pp_print_string fmt "(.bind";
                F.pp_print_space fmt ();
                extract_deep_texpr span ctx tenv fresh env fmt
                  ~expected:bound_ty bound;
                F.pp_print_space fmt ();
                F.pp_print_string fmt ".var";
                F.pp_close_box fmt ();
                F.pp_print_space fmt ();
                let ctx, env = bind_vars span ctx env [ x ] in
                extract_deep_match span ctx tenv fresh env fmt ?expected
                  (mk_texpr_from_fvar x) (Some pat.ty) info
                  [ (vs, next) ];
                F.pp_print_string fmt ")";
                F.pp_close_box fmt ())
              else
                extract_deep_match span ctx tenv fresh env fmt ?expected bound
                  (Some pat.ty) info
                  [ (vs, next) ])
      | Some (vs, ppat) ->
          F.pp_open_hvbox fmt 0;
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt (if monadic then "(.bind" else "(.let_");
          F.pp_print_space fmt ();
          (* The type of the bound expression is given by the pattern *)
          extract_deep_texpr span ctx tenv fresh env fmt ~expected:bound_ty
            bound;
          F.pp_print_space fmt ();
          ppat fmt;
          F.pp_close_box fmt ();
          F.pp_print_space fmt ();
          let ctx, env = bind_vars span ctx env vs in
          extract_deep_texpr span ctx tenv fresh env fmt ?expected next;
          F.pp_print_string fmt ")";
          F.pp_close_box fmt ())
  | Switch (scrut, If (e_then, e_else)) ->
      F.pp_open_hvbox fmt 0;
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.ite";
      F.pp_print_space fmt ();
      extract_deep_cond span ctx tenv fresh env fmt scrut;
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx tenv fresh env fmt ?expected e_then;
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx tenv fresh env fmt ?expected e_else;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Switch (scrut, Match branches) -> (
      match plan_deep_match span fresh scrut branches with
      | Some (info, brs) ->
          extract_deep_match span ctx tenv fresh env fmt ?expected scrut None
            info brs
      | None ->
          extract_deep_escape span ctx tenv env fmt
            (Option.value expected ~default:e.ty)
            e)
  | App _ | Qualif _ -> extract_deep_app span ctx tenv fresh env fmt ?expected e
  | StructUpdate supd -> (
      let ty = Option.value expected ~default:e.ty in
      (* A structure of the closed world with all its fields: a constructor
         node *)
      let full_ctor =
        match (supd.struct_id, supd.init, ty) with
        | TAdtId id, None, TAdt (TAdtId id', generics)
          when TypeDeclId.to_int id = TypeDeclId.to_int id' -> (
            match closed_type_info id with
            | Some info when info.has_variants -> (
                match info.decl.kind with
                | Struct fields ->
                    let updates =
                      List.sort
                        (fun (f1, _) (f2, _) -> FieldId.compare_id f1 f2)
                        supd.updates
                    in
                    if
                      List.length updates = List.length fields
                      && List.for_all Fun.id
                           (List.mapi
                              (fun i (fid, _) -> FieldId.to_int fid = i)
                              updates)
                    then Some ({ info; generics }, List.map snd updates)
                    else None
                | _ -> None)
            | _ -> None)
        | _ -> None
      in
      match full_ctor with
      | Some (info, args) ->
          extract_deep_ctor span ctx tenv fresh env fmt info None args
      | None ->
          (* We eta-expand the structure update over the initial value (if
             there is one) and the field values *)
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
          extract_deep_eta_leaf span ctx tenv fresh env fmt tag mk_shallow args
            (Some ty))
  | Loop _ ->
      (* The loop nodes should have been eliminated in {!PureMicroPasses} *)
      [%admit_raise] span "Unreachable" fmt
  | EError _ -> F.pp_print_string fmt "sorry"

(** Print a list of expressions: [(.cons A (.cons B .nil))]. The expected types
    are given with the expressions. *)
and extract_deep_exprs (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) (args : (texpr * ty) list) : unit =
  F.pp_open_hovbox fmt ctx.indent_incr;
  List.iter
    (fun (arg, expected) ->
      F.pp_print_string fmt "(.cons ";
      extract_deep_texpr span ctx tenv fresh env fmt ~expected arg;
      F.pp_print_space fmt ())
    args;
  F.pp_print_string fmt ".nil";
  List.iter (fun _ -> F.pp_print_string fmt ")") args;
  F.pp_close_box fmt ()

(** Print a call node:
    {[
      (.call FREF [targs] [cargs] [inputs] OUTPUT rfl rfl ARGS)
    ]}
    [inputs] and [output] are the signature instantiated with the arguments. *)
and extract_deep_call (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) (fref : string) (targs : ty list)
    (cargs : const_generic list) (inputs : ty list) (output : ty)
    (args : texpr list) : unit =
  let list (l : string list) = "[" ^ String.concat ", " l ^ "]" in
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("(.call " ^ fref ^ " "
    ^ list (List.map (deep_ty_def span ctx tenv) targs)
    ^ " "
    ^ list
        (List.map
           (fun cg ->
             [%unwrap_with_span] span (deep_cg span ctx tenv cg)
               "Could not compute the const-generic descriptor")
           cargs)
    ^ " "
    ^ list (List.map (deep_ty_def span ctx tenv) inputs)
    ^ " "
    ^ deep_ty_def span ctx tenv output
    ^ " rfl rfl");
  F.pp_print_space fmt ();
  extract_deep_exprs span ctx tenv fresh env fmt (List.combine args inputs);
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(** Print a constructor node:
    {[
      (.ctor TypeName.T v [targs] [cargs] [field types] rfl ARGS)
    ]} *)
and extract_deep_ctor (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) (info : deep_adt_info)
    (variant_id : VariantId.id option) (args : texpr list) : unit =
  let fields =
    type_decl_get_instantiated_fields_types info.info.decl variant_id
      info.generics
  in
  let vid = Option.fold ~none:0 ~some:VariantId.to_int variant_id in
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("(.ctor " ^ info.info.ref ^ " " ^ string_of_int vid ^ " "
    ^ deep_adt_args span ctx tenv info.info info.generics
    ^ " ["
    ^ String.concat ", " (List.map (deep_ty_def span ctx tenv) fields)
    ^ "] rfl");
  F.pp_print_space fmt ();
  extract_deep_exprs span ctx tenv fresh env fmt (List.combine args fields);
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(** Print a match with a deep eliminator:
    {[
      (.match_ TypeName.T [targs] [cargs] [[field types], ...] rfl SCRUT
       (.cons BRANCH_0
       (.cons BRANCH_1
       .nil)))
    ]}
    [brs]: for every variant, in order, the variables bound by the branch (the
    fields of the variant) and the body of the branch. *)
and extract_deep_match (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) ?(expected : ty option) (scrut : texpr)
    (scrut_expected : ty option) (info : deep_adt_info)
    (brs : (fvar list * texpr) list) : unit =
  let shape =
    "["
    ^ String.concat ", "
        (List.map
           (fun (vs, _) ->
             "["
             ^ String.concat ", "
                 (List.map
                    (fun (v : fvar) -> deep_ty_def span ctx tenv v.ty)
                    vs)
             ^ "]")
           brs)
    ^ "]"
  in
  F.pp_open_vbox fmt 0;
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt
    ("(.match_ " ^ info.info.ref ^ " "
    ^ deep_adt_args span ctx tenv info.info info.generics
    ^ " " ^ shape ^ " rfl");
  F.pp_print_space fmt ();
  extract_deep_texpr span ctx tenv fresh env fmt ?expected:scrut_expected scrut;
  F.pp_close_box fmt ();
  F.pp_print_cut fmt ();
  F.pp_open_vbox fmt 0;
  List.iter
    (fun (vs, body) ->
      F.pp_print_string fmt "(.cons ";
      let ctx, env = bind_vars span ctx env vs in
      F.pp_open_hovbox fmt ctx.indent_incr;
      extract_deep_texpr span ctx tenv fresh env fmt ?expected body;
      F.pp_close_box fmt ();
      F.pp_print_cut fmt ())
    brs;
  F.pp_print_string fmt ".nil";
  List.iter (fun _ -> F.pp_print_string fmt ")") brs;
  F.pp_close_box fmt ();
  F.pp_print_string fmt ")";
  F.pp_close_box fmt ()

(** Print nested lambdas: [(.lam T1 p1 (.lam T2 p2 body))] *)
and extract_deep_lambdas (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) ?(expected : ty option) (e : texpr) (xl : tpat list)
    (body : texpr) : unit =
  (* All the patterns must be supported, otherwise we print the whole lambda
     through the escape hatch *)
  let pats = List.map (deep_pat span ctx) xl in
  if List.exists Option.is_none pats then
    extract_deep_escape span ctx tenv env fmt
      (Option.value expected ~default:e.ty)
      e
  else
    let pats = List.map Option.get pats in
    F.pp_open_hovbox fmt ctx.indent_incr;
    let ctx, env =
      List.fold_left2
        (fun (ctx, env) (vs, ppat) (p : tpat) ->
          F.pp_print_string fmt ("(.lam " ^ deep_ty_def span ctx tenv p.ty ^ " ");
          ppat fmt;
          F.pp_print_space fmt ();
          bind_vars span ctx env vs)
        (ctx, env) pats xl
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
    extract_deep_texpr span ctx tenv fresh env fmt ?expected:body_expected body;
    List.iter (fun _ -> F.pp_print_string fmt ")") pats;
    F.pp_close_box fmt ()

(** Print an [if] condition.

    The comparisons [=], [<], [<=], [>], [>=] are printed by the shallow printer
    with the infix notations, which Lean elaborates to propositions: we use the
    dedicated constructors of [Cond]. All the other conditions are boolean
    expressions, which the shallow [if] turns into [b = true]: we use
    [Cond.bool]. *)
and extract_deep_cond (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) (scrut : texpr) : unit =
  let app, args = destruct_apps scrut in
  match (app.e, args) with
  | Qualif { id = FunOrOp (Unop (Not None)); _ }, [ c ] ->
      (* [if ¬ c] elaborates to [ite (¬ ...)] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.not";
      F.pp_print_space fmt ();
      extract_deep_cond span ctx tenv fresh env fmt c;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | _ ->
      let cons =
        match (app.e, args) with
        | ( Qualif
              {
                id = FunOrOp (Binop ((Eq _ | Lt _ | Le _ | Gt _ | Ge _) as op));
                _;
              },
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
              extract_deep_texpr span ctx tenv fresh env fmt arg)
            args;
          F.pp_print_string fmt ")"
      | None ->
          F.pp_print_string fmt "(.bool";
          F.pp_print_space fmt ();
          extract_deep_texpr span ctx tenv fresh env fmt scrut;
          F.pp_print_string fmt ")");
      F.pp_close_box fmt ()

(** Print an application (or a top-level qualifier). *)
and extract_deep_app (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) ?(expected : ty option) (e : texpr) : unit =
  let app, args = destruct_apps e in
  let print_simple (cons : string) (args : texpr list) : unit =
    F.pp_open_hovbox fmt ctx.indent_incr;
    F.pp_print_string fmt ("(" ^ cons);
    List.iter
      (fun arg ->
        F.pp_print_space fmt ();
        extract_deep_texpr span ctx tenv fresh env fmt arg)
      args;
    F.pp_print_string fmt ")";
    F.pp_close_box fmt ()
  in
  let eta_leaf (q : qualif) : unit =
    let mk_shallow (args : texpr list) : texpr =
      [%add_loc] mk_apps span app args
    in
    extract_deep_eta_leaf span ctx tenv fresh env fmt (qualif_tag ctx q)
      mk_shallow args expected
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
      extract_deep_cond span ctx tenv fresh env fmt e;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Qualif { id = FunOrOp (Binop binop); _ }, [ _; _ ]
    when Option.is_some (deep_binop binop) ->
      print_simple (Option.get (deep_binop binop)) args
  | Qualif { id = FunOrOp (Unop unop); _ }, [ _ ]
    when Option.is_some (deep_unop unop) ->
      print_simple (Option.get (deep_unop unop)) args
  | Qualif { id = FunOrOp (Fun (Pure Assert)); _ }, [ cond ] ->
      (* [massert] takes a proposition: the condition is handled like the
         condition of an [if] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.assert";
      F.pp_print_space fmt ();
      extract_deep_cond span ctx tenv fresh env fmt cond;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Qualif _, [ arg ] when is_result_ok app ->
      let expected = Option.bind expected unwrap_result_ty in
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt "(.ok";
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx tenv fresh env fmt ?expected arg;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | Qualif _, [ ({ e = Qualif _; _ } as err) ] when is_result_fail app ->
      (* The error is a closed term: we print it shallowly *)
      let ty =
        match Option.bind expected unwrap_result_ty with
        | Some ty -> ty
        | None -> (
            match unwrap_result_ty e.ty with
            | Some ty -> ty
            | None -> [%craise] span "Unexpected type for a failure")
      in
      F.pp_print_string fmt ("(.fail " ^ deep_ty_def span ctx tenv ty ^ " ");
      extract_texpr span ctx fmt ~inside:true ~inside_do:false err;
      F.pp_print_string fmt ")"
  | Qualif { id = AdtCons { adt_id = TTuple; _ }; _ }, _ -> (
      (* Tuples *)
      match args with
      | [] -> F.pp_print_string fmt ".unitLit"
      | [ arg ] -> extract_deep_texpr span ctx tenv fresh env fmt ?expected arg
      | _ ->
          let expected =
            match expected with
            | Some (TAdt (TTuple, { types; _ }))
              when List.length types = List.length args -> types
            | _ -> List.map (fun (a : texpr) -> a.ty) args
          in
          F.pp_open_hovbox fmt ctx.indent_incr;
          F.pp_print_string fmt "(.tuple";
          F.pp_print_space fmt ();
          extract_deep_exprs span ctx tenv fresh env fmt
            (List.combine args expected);
          F.pp_print_string fmt ")";
          F.pp_close_box fmt ())
  | ( Qualif
        {
          id = AdtCons { adt_id = TBuiltin TLoopResult; variant_id = Some vid };
          _;
        },
      [ arg ] )
    when (vid = loop_result_continue_id || vid = loop_result_break_id)
         && Option.is_some
              (try_unwrap_loop_result (Option.value expected ~default:e.ty)) ->
      let a, b =
        Option.get
          (try_unwrap_loop_result (Option.value expected ~default:e.ty))
      in
      let cons, expected =
        if vid = loop_result_continue_id then (".continue_", a)
        else (".break_", b)
      in
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt
        ("(" ^ cons ^ " "
        ^ deep_ty_def span ctx tenv a
        ^ " "
        ^ deep_ty_def span ctx tenv b);
      F.pp_print_space fmt ();
      extract_deep_texpr span ctx tenv fresh env fmt ~expected arg;
      F.pp_print_string fmt ")";
      F.pp_close_box fmt ()
  | ( Qualif ({ id = AdtCons { adt_id = TAdtId id; variant_id }; generics } as q),
      _ ) -> (
      (* A constructor of the closed world applied to all its arguments: a
         constructor node *)
      match closed_type_info id with
      | Some info
        when info.has_variants
             && List.length
                  (type_decl_get_instantiated_fields_types info.decl variant_id
                     generics)
                = List.length args ->
          extract_deep_ctor span ctx tenv fresh env fmt { info; generics }
            variant_id args
      | _ -> eta_leaf q)
  | ( Qualif ({ id = Proj { adt_id = TAdtId id; field_id }; generics } as q),
      [ arg ] ) -> (
      (* A projection on a structure of the closed world *)
      match closed_type_info id with
      | Some info when info.has_variants -> (
          match info.decl.kind with
          | Struct _ ->
              let fields =
                type_decl_get_instantiated_fields_types info.decl None generics
              in
              let field_ty =
                [%unwrap_with_span] span
                  (List.nth_opt fields (FieldId.to_int field_id))
                  "Invalid field"
              in
              F.pp_open_hovbox fmt ctx.indent_incr;
              F.pp_print_string fmt
                ("(.proj " ^ info.ref ^ " "
                ^ string_of_int (FieldId.to_int field_id)
                ^ " "
                ^ deep_adt_args span ctx tenv info generics
                ^ " "
                ^ deep_ty_def span ctx tenv field_ty
                ^ " rfl");
              F.pp_print_space fmt ();
              extract_deep_texpr span ctx tenv fresh env fmt
                ~expected:(TAdt (TAdtId id, generics))
                arg;
              F.pp_print_string fmt ")";
              F.pp_close_box fmt ()
          | _ -> eta_leaf q)
      | _ -> eta_leaf q)
  | Qualif ({ id = FunOrOp (Fun (FromLlbc (FunId fid, lp))); generics } as q), _
    -> (
      (* A call to a function of the closed world, applied to all its
         arguments: a call node. The input and output types are the signature
         instantiated with the generic arguments of the call. *)
      match closed_fun_info fid lp with
      | Some info
        when List.length args = List.length info.fun_decl.signature.inputs ->
          let subst =
            make_subst_from_generics info.fun_decl.signature.generics generics
          in
          let isig = fun_sig_substitute subst info.fun_decl.signature in
          extract_deep_call span ctx tenv fresh env fmt info.fun_ref
            (filter_type_args info.keep_fun_types generics.types)
            generics.const_generics isig.inputs isig.output args
      | _ -> eta_leaf q)
  | ( Qualif
        { id = FunOrOp (Fun (Pure ToResult)); generics = { types = [ t ]; _ } },
      [ _ ] ) ->
      (* [toResult x] is [lift x] *)
      extract_deep_call span ctx tenv fresh env fmt "(.prim .lift)" [ t ] []
        [ t ] (mk_result_ty t) args
  | ( Qualif
        {
          id = FunOrOp (Fun (Pure (IndexAtIndex kind)));
          generics = { types = [ t ]; const_generics; _ };
        },
      [ _; _ ] )
    when (kind = Slice && const_generics = [])
         || (kind = Array && List.length const_generics = 1) ->
      let container = mk_array_or_slice_ty kind t const_generics in
      extract_deep_call span ctx tenv fresh env fmt
        (if kind = Array then "(.prim .arrayIndex)" else "(.prim .sliceIndex)")
        [ t ] const_generics [ container; mk_usize_ty ] (mk_result_ty t) args
  | ( Qualif
        {
          id = FunOrOp (Fun (Pure (UpdateAtIndex kind)));
          generics = { types = [ t ]; const_generics; _ };
        },
      [ _; _; _ ] )
    when (kind = Slice && const_generics = [])
         || (kind = Array && List.length const_generics = 1) ->
      let container = mk_array_or_slice_ty kind t const_generics in
      extract_deep_call span ctx tenv fresh env fmt
        (if kind = Array then "(.prim .arrayUpdate)" else "(.prim .sliceUpdate)")
        [ t ] const_generics
        [ container; mk_usize_ty; t ]
        (mk_result_ty container) args
  | ( Qualif
        {
          id = FunOrOp (Fun (Pure (IndexMutAtIndex kind)));
          generics = { types = [ t ]; const_generics; _ };
        },
      [ _; _ ] )
    when (kind = Slice && const_generics = [])
         || (kind = Array && List.length const_generics = 1) ->
      let container = mk_array_or_slice_ty kind t const_generics in
      extract_deep_call span ctx tenv fresh env fmt
        (if kind = Array then "(.prim .arrayIndexMut)"
         else "(.prim .sliceIndexMut)")
        [ t ] const_generics [ container; mk_usize_ty ]
        (mk_result_ty (mk_simpl_tuple_ty [ t; mk_arrow t container ]))
        args
  | Qualif ({ id = Global gid; generics } as q), [] -> (
      (* A global of the closed world *)
      match closed_global_info gid with
      | Some info ->
          let subst = make_subst_from_generics info.global.generics generics in
          let ty = ty_substitute subst info.global.ty in
          let list (l : string list) = "[" ^ String.concat ", " l ^ "]" in
          F.pp_print_string fmt
            ("(.global " ^ info.global_ctor ^ " "
            ^ list (List.map (deep_ty_def span ctx tenv) generics.types)
            ^ " "
            ^ list
                (List.map
                   (fun cg ->
                     [%unwrap_with_span] span (deep_cg span ctx tenv cg)
                       "Could not compute the const-generic descriptor")
                   generics.const_generics)
            ^ " "
            ^ deep_ty_def span ctx tenv ty
            ^ " rfl)")
      | None -> eta_leaf q)
  | Qualif q, _ -> eta_leaf q
  | _, [] -> extract_deep_texpr span ctx tenv fresh env fmt ?expected app
  | _, _ ->
      (* Regular application: [(.app (.app f a) b)] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      List.iter (fun _ -> F.pp_print_string fmt "(.app ") args;
      extract_deep_texpr span ctx tenv fresh env fmt app;
      List.iter
        (fun arg ->
          F.pp_print_space fmt ();
          extract_deep_texpr span ctx tenv fresh env fmt arg;
          F.pp_print_string fmt ")")
        args;
      F.pp_close_box fmt ()

(** Print a leaf eta-expanded over its arguments, applied to the deep arguments:
    {[
      (.app (.app (.leaf TAG TY (fun (x : T1) (y : T2) => (SHALLOW : T))) x') y')
    ]}
    [mk_shallow] builds the shallow expression from the (fresh) variables
    standing for the arguments. [expected] is the type of the whole application,
    if known. *)
and extract_deep_eta_leaf (span : Meta.span) (ctx : extraction_ctx)
    (tenv : deep_tyenv) (fresh : unit -> fvar_id) (env : denv)
    (fmt : F.formatter) (tag : string) (mk_shallow : texpr list -> texpr)
    (args : texpr list) (expected : ty option) : unit =
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
  let leaf_ty = mk_arrows (List.map (fun (v : fvar) -> v.ty) vars) shallow.ty in
  F.pp_open_hovbox fmt ctx.indent_incr;
  List.iter (fun _ -> F.pp_print_string fmt "(.app ") args;
  (* The leaf *)
  F.pp_open_hovbox fmt ctx.indent_incr;
  F.pp_print_string fmt ("(.leaf " ^ tag);
  F.pp_print_space fmt ();
  F.pp_print_string fmt (deep_ty_def span ctx tenv leaf_ty);
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
      extract_deep_texpr span ctx tenv fresh env fmt arg;
      F.pp_print_string fmt ")")
    args;
  F.pp_close_box fmt ()

(** {1 Declarations} *)

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

(** A formatter which discards its output *)
let null_formatter () : F.formatter =
  F.make_formatter (fun _ _ _ -> ()) (fun () -> ())

(** Print the deep term and the denotation theorem for a declaration (a function
    or a global) with a body.

    - [def_name]: the name of the (shallow) declaration
    - [unfold]: if [true], the proof of the theorem starts by unfolding the
      declaration (recursive definitions, globals)
    - [comment]: prints the comment which links the deep term to the Rust
      declaration

    The body is printed twice: a first time to a null formatter, to discover the
    types which the descriptors can not express (they become type variables,
    listed in the type environment printed in the header), and a second time for
    real. *)
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
      let ctx_g, type_params, cg_params, trait_clauses =
        ctx_add_generic_params span def.item_meta.name Item
          def.signature.llbc_generics def.signature.generics ctx
      in
      (* The type environment and the body printer *)
      let tenv = mk_deep_tyenv def.signature.generics true in
      let print_body (fmt : F.formatter) : unit =
        let ctx_b, env = bind_vars span ctx_g [] input_vars in
        F.pp_open_hovbox fmt ctx.indent_incr;
        if texpr_num_lets body.body > deep_max_lets then
          (* The body is too long for a deep term: escape hatch *)
          extract_deep_escape span ctx_b tenv env fmt def.signature.output
            body.body
        else
          extract_deep_texpr span ctx_b tenv fresh env fmt
            ~expected:def.signature.output body.body;
        F.pp_close_box fmt ()
      in
      (* First pass: compute the type environment *)
      let input_tys =
        List.map (deep_ty_def span ctx_g tenv) def.signature.inputs
      in
      let output_ty = deep_ty_def span ctx_g tenv def.signature.output in
      let null_fmt = null_formatter () in
      print_body null_fmt;
      F.pp_print_flush null_fmt ();
      (*
       * The deep term
       *)
      F.pp_print_break fmt 0 0;
      comment ();
      F.pp_print_space fmt ();
      (* Open a vbox so that every line after the first one gets indented *)
      F.pp_open_vbox fmt ctx.indent_incr;
      (* The header:
         [def NAME.deep GENERICS : Aeneas.Deep.Expr TypeName ⟨[T1, ...], [N1, ...]⟩ [T1, ..., Tn] T :=] *)
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt ("def " ^ deep_name);
      F.pp_print_space fmt ();
      let space = ref true in
      (let space = Some space in
       extract_generic_params span ctx_g fmt TypeDeclId.TreeSet.empty ~space
         Item def.signature.generics (Some def.signature.explicit_info)
         type_params cg_params trait_clauses);
      insert_req_space fmt space;
      F.pp_print_string fmt ":";
      F.pp_print_space fmt ();
      F.pp_open_hovbox fmt ctx.indent_incr;
      F.pp_print_string fmt
        (deep_prefix ^ "Expr " ^ type_name_enum ^ " " ^ fun_name_enum ^ " "
       ^ global_name_enum);
      F.pp_print_space fmt ();
      extract_deep_tyenv span ctx_g fmt tenv;
      F.pp_print_space fmt ();
      F.pp_print_string fmt ("[" ^ String.concat ", " input_tys ^ "]");
      F.pp_print_space fmt ();
      F.pp_print_string fmt output_ty;
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      F.pp_print_string fmt ":=";
      F.pp_close_box fmt ();
      F.pp_print_space fmt ();
      (* The body: the inputs are the initial environment *)
      print_body fmt;
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
         [f G x y = Aeneas.Deep.Expr.denote (f.deep G) (x ::ₑ y ::ₑ Aeneas.Deep.Env.nil)] *)
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
      List.iter (fun name -> F.pp_print_string fmt (name ^ " ::ₑ ")) input_names;
      F.pp_print_string fmt (deep_prefix ^ "Env.nil)");
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
