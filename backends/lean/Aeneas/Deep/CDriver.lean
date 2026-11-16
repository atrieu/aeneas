module
public import Lean
public import Aeneas.Deep.Report
public import Aeneas.Deep.CPrint
public meta import Aeneas.Deep.CPrint
public section

/-! # The driver of the C printer

`#deep_c "file.c"` compiles every *closed* deep term of the environment (the functions
and globals without type or const-generic parameters) with `Aeneas.Deep.Compile.compile`,
prints the result with the trusted printer (`Aeneas.Deep.CPrint`) and writes the
translation unit to `file.c`; `#deep_c "file.c" crate` restricts to the deep terms of the
crate `crate` (the namespace of its generated enumerations). The C name of a function is
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

/-- The crate of a deep term: the namespace of its enumeration of type names (`N` in
`Expr N F G σ Γ τ`), which is the namespace the printer of the deep terms derived the
constructor names from -/
meta def crateOf (n : Name) : TermElabM (Option Name) := do
  let ci ← getConstInfo n
  let ty ← whnfD ci.type
  match ty.getAppArgs[0]? with
  | some (Expr.const tn _) => pure (some tn.getPrefix)
  | _ => pure none

/-- The closed deep terms of the environment (of the crate `crate`, if given), with
their C names -/
meta def closedDeepTerms (crate : Option Name) : TermElabM (Array (Name × String)) := do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if !n.isInternal && n.getString! == "deep" then acc.push n else acc
  let names := names.qsort (fun a b => a.toString < b.toString)
  let names ← names.filterM isDeepTerm
  let closed ← names.filterM fun n => do
    let ci ← getConstInfo n
    pure !ci.type.isForall
  let mut out := #[]
  for n in closed do
    let some c ← crateOf n | continue
    if let some crate := crate then
      unless c == crate do continue
    let cs := (n.components.map Name.toString).dropLast.drop c.components.length
    out := out.push (n, cNameOfLean (".".intercalate cs))
  pure out

/-- Compile and print the closed deep terms of the environment (of one crate, when its
namespace is given) to a C file -/
elab "#deep_c" path:str crate:(ident)? : command => do
  let terms ← liftTermElabM (closedDeepTerms (crate.map (·.getId)))
  let mut outs : Array FnOut := #[]
  let mut failures : Array String := #[]
  for (n, cname) in terms do
    let ci ← getConstInfo n
    let e := mkConst n (ci.levelParams.map mkLevelParam)
    let r ← liftTermElabM do
      -- `e : @Expr N F G instN instF instG σ Γ τ`: the tables `instF`/`instG` of the crate
      -- may be noncomputable, and the printer never consults them: it is run on `e` cast
      -- to the type with the computable stand-ins
      let ty ← whnfD ci.type
      let args := ty.getAppArgs
      unless args.size == 9 do throwError "unexpected type of {n}: {ty}"
      let (N, F, G, instN, σ, Γ, τ) := (args[0]!, args[1]!, args[2]!, args[3]!, args[6]!, args[7]!, args[8]!)
      let dF ← mkAppOptM ``CPrint.dummyFunNames #[F, N, instN]
      let dG ← mkAppOptM ``CPrint.dummyGlobalNames #[G, N, instN]
      let ty' := mkAppN (mkConst ``Aeneas.Deep.Expr) #[N, F, G, instN, dF, dG, σ, Γ, τ]
      let e' ← mkAppOptM ``unsafeCast #[none, ty', e]
      let reprN ← synthInstance (mkApp (mkConst ``Repr [Level.zero]) N)
      let reprF ← synthInstance (mkApp (mkConst ``Repr [Level.zero]) F)
      let reprG ← synthInstance (mkApp (mkConst ``Repr [Level.zero]) G)
      let app := mkAppN (mkConst ``CPrint.printFunction)
        #[N, F, G, instN, dF, dG, σ, reprN, reprF, reprG, Γ, τ, toExpr cname, e']
      try
        unsafe evalExpr' FnOut ``Aeneas.Deep.CPrint.FnOut app (safety := .unsafe)
      catch ex =>
        -- a deep term without compiled code: a shallow leaf of it refers to a
        -- noncomputable function (such a term is outside the fragment anyway)
        let msg ← ex.toMessageData.toString
        let reason := if (msg.splitOn "noncomputable").length > 1 then "noncomputable deep term"
          else s!"not evaluable: {msg.take 200}"
        pure { name := cname, text := s!"/* {cname}: {reason} */", ok := false }
    outs := outs.push r
    unless r.ok do failures := failures.push r.text
  let text := assemble outs
  IO.FS.writeFile path.getString text
  let ok := outs.filter (·.ok) |>.size
  logInfo m!"deep_c: {ok} / {terms.size} closed deep terms printed to {path.getString}\n{"\n".intercalate failures.toList}"

end Aeneas.Deep
