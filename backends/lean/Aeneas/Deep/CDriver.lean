module
public import Lean
public import Aeneas.Deep.Report
public import Aeneas.Deep.CPrint
public meta import Aeneas.Deep.CPrint
public section

/-! # The driver of the C printer

`#deep_c "file.c" crate` compiles the deep terms of the crate `crate` (the namespace of its
generated enumerations; all the crates of the environment when omitted) with
`Aeneas.Deep.Compile.compile`, prints the instances reachable from the closed functions
with the trusted printer (`Aeneas.Deep.CPrint.program`) and writes the translation unit
to `file.c`. Options: `externals := [(name, definition), …]` gives the C definitions of
the opaque types (by C name), `entries := [(name, targs, cargs), …]` asks for instances
of generic functions.

The deep terms are packaged as `AnyDeep` values: a generic term is instantiated with `Nat`
for its type parameters and `0` for its const generics (the printer only reads the
descriptors), and the tables of the crate (parameters of the type of the terms, possibly
noncomputable) are replaced by computable stand-ins through `unsafeCast`, which is sound
because the constructors of the terms do not store them. The C name of a definition is
derived from its Lean name as the printer of the deep terms derives the constructors of
`FunName` (so that the definitions and the call sites agree): the crate namespace is
dropped, and every byte which is not an identifier character becomes `_`. -/

namespace Aeneas.Deep

open Lean Meta Elab Command CPrint

/-- A C identifier from a Lean name string, as `name_ctor` in `ExtractDeep.ml`: every byte
which is not an identifier character becomes `_` (and the quote `_q`, as in the printer) -/
meta def cNameOfLean (s : String) : String :=
  String.join <| s.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '_' then c.toString else if c == '\'' then "_q" else "_"

/-- The arguments `N F G instN instF instG σ Γ τ` of the type of a deep term, under its
binders -/
meta def deepTypeArgs (n : Name) : TermElabM (Array Lean.Expr) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun _ ty => do
    let ty ← whnfD ty
    pure ty.getAppArgs

/-- The crate of a deep term: the namespace of its enumeration of type names (`N`), which
is the namespace the printer of the deep terms derived the constructor names from -/
meta def crateOf (n : Name) : TermElabM (Option Name) := do
  match (← deepTypeArgs n)[0]? with
  | some (Lean.Expr.const tn _) => pure (some tn.getPrefix)
  | _ => pure none

/-- The deep terms of the environment (of the crate `crate`, if given), with their C
names -/
meta def crateDeepTerms (crate : Option Name) : TermElabM (Array (Name × String)) := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if !n.isInternal && n.getString! == "deep" then acc.push n else acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  let names ← names.filterM isDeepTerm
  let mut out := #[]
  for n in names do
    let some c ← crateOf n | continue
    if let some crate := crate then
      unless c == crate do continue
    let cs := (n.components.map Name.toString).dropLast.drop c.components.length
    out := out.push (n, cNameOfLean (".".intercalate cs))
  pure out

/-- `0 : Usize` (`Usize.ofNat 0` with its bound proved by `decide`) -/
meta def usizeZero : MetaM Lean.Expr := do
  let ofNat := Lean.mkConst ``Aeneas.Std.Usize.ofNat
  let .forallE _ _ body _ ← inferType ofNat | throwError "unexpected type of Usize.ofNat"
  let .forallE _ hty _ _ := body.instantiate1 (mkRawNatLit 0)
    | throwError "unexpected type of Usize.ofNat"
  let h ← mkDecideProof (← whnfR hty.consumeMData)
  pure (mkApp2 ofNat (mkRawNatLit 0) h)

/-- Instantiate the parameters of a deep term: the types with `Nat`, the const generics
with `0`, the instances by synthesis. Returns the term, its type and the numbers of type
and const-generic parameters; `none` for a parameter the driver cannot instantiate. -/
meta def instantiateDeep (n : Name) : TermElabM (Option (Lean.Expr × Lean.Expr × Nat × Nat)) := do
  let ci ← getConstInfo n
  let lvls := ci.levelParams.map fun _ => Level.zero
  let mut e := Lean.mkConst n lvls
  let mut ty := ci.type.instantiateLevelParams ci.levelParams lvls
  let mut nT := 0
  let mut nC := 0
  repeat
    let .forallE _ bt body bi := ty | break
    let mut arg := none
    try
      if bt.isSort then
        nT := nT + 1
        arg := some (Lean.mkConst ``Nat)
      else if bt.isConstOf ``Aeneas.Std.Usize then
        nC := nC + 1
        arg := some (← usizeZero)
      else if bi.isInstImplicit then
        arg := some (← synthInstance bt)
    catch _ => pure ()
    let some a := arg | return none
    e := mkApp e a
    ty := body.instantiate1 a
  pure (some (e, ty, nT, nC))

syntax (name := deepC) "#deep_c" str (ident)? (&" externals" " := " term)?
  (&" entries" " := " term)? : command

/-- Compile and print the deep terms of a crate to a C file -/
elab_rules : command
  | `(#deep_c $path:str $[$crate:ident]? $[externals := $ext:term]? $[entries := $ent:term]?) => do
    let terms ← liftTermElabM (crateDeepTerms (crate.map (·.getId)))
    if terms.isEmpty then throwError "no deep term in the environment"
    let report ← liftTermElabM do
      -- the crate parameters, from the first term
      let args ← deepTypeArgs terms[0]!.1
      unless args.size == 9 do throwError "unexpected type of {terms[0]!.1}"
      let (N, F, G, instN) := (args[0]!, args[1]!, args[2]!, args[3]!)
      let dF ← mkAppOptM ``CPrint.dummyFunNames #[F, N, instN]
      let dG ← mkAppOptM ``CPrint.dummyGlobalNames #[G, N, instN]
      let anyTy := mkAppN (Lean.mkConst ``CPrint.AnyDeep) #[N, F, G, instN, dF, dG]
      let mut elems := #[]
      let mut skipped := #[]
      let mut nc := #[]
      for (n, cname) in terms do
        -- a deep term without compiled code (a shallow leaf of it refers to a
        -- noncomputable function) cannot be evaluated; it is outside the fragment anyway
        if isNoncomputable (← getEnv) n then
          nc := nc.push cname
          continue
        let some (e, ety, nT, nC) ← instantiateDeep n
          | skipped := skipped.push cname; continue
        let a := (← whnfD ety).getAppArgs
        unless a.size == 9 do throwError "unexpected type of {n}"
        let ty' := mkAppN (Lean.mkConst ``Aeneas.Deep.Expr) #[N, F, G, instN, dF, dG, a[6]!, a[7]!, a[8]!]
        let e' ← mkAppOptM ``unsafeCast #[none, ty', e]
        elems := elems.push <| mkAppN (Lean.mkConst ``CPrint.AnyDeep.mk)
          #[N, F, G, instN, dF, dG, toExpr cname, toExpr nT, toExpr nC, a[6]!, a[7]!, a[8]!, e']
      let fns ← mkListLit anyTy elems.toList
      let strTy := Lean.mkConst ``String
      let extElt ← mkAppM ``Prod #[strTy, strTy]
      let externals ← match ext with
        | some t => do
          let v ← Term.elabTerm t (some (← mkAppM ``List #[extElt]))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars v
        | none => mkAppOptM ``List.nil #[extElt]
      let tyN := mkApp (Lean.mkConst ``Aeneas.Deep.Ty) N
      let entElt ← mkAppM ``Prod #[strTy, ← mkAppM ``Prod
        #[← mkAppM ``List #[tyN], ← mkAppM ``List #[Lean.mkConst ``Aeneas.Deep.CArg]]]
      let entries ← match ent with
        | some t => do
          let v ← Term.elabTerm t (some (← mkAppM ``List #[entElt]))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars v
        | none => mkAppOptM ``List.nil #[entElt]
      let reprN ← synthInstance (mkApp (Lean.mkConst ``Repr [Level.zero]) N)
      let reprF ← synthInstance (mkApp (Lean.mkConst ``Repr [Level.zero]) F)
      let reprG ← synthInstance (mkApp (Lean.mkConst ``Repr [Level.zero]) G)
      let app := mkAppN (Lean.mkConst ``CPrint.program)
        #[N, F, G, instN, dF, dG, reprN, reprF, reprG, fns, externals, entries]
      let r ← unsafe evalExpr' Report ``Aeneas.Deep.CPrint.Report app (safety := .unsafe)
      pure (r, skipped, nc)
    let (report, skipped, nc) := report
    IO.FS.writeFile path.getString report.text
    let skippedMsg := if skipped.isEmpty then "" else
      s!"\nskipped (parameters the driver cannot instantiate): {", ".intercalate skipped.toList}"
    let ncMsg := if nc.isEmpty then "" else
      s!"\nnoncomputable deep terms (not evaluable): {nc.size}"
    logInfo m!"deep_c: {report.printed} / {report.total} function instances printed to {path.getString} ({terms.size} deep terms){skippedMsg}{ncMsg}\n{"\n".intercalate report.failures.toList}"

end Aeneas.Deep
