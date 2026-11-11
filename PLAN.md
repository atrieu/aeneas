# Plan: a "deep" printing mode for the Lean backend

Goal: add a `-deep` mode to the Lean backend. For each extracted definition, the mode
prints a Lean term that constructs the AST of the definition's body, plus a theorem stating
that the denotation of this term equals the shallow definition.

The recommended design is an intrinsically typed deep AST over shallow Lean types, printed
from the pure AST right before extraction, with the denotation theorem proved by `rfl`
(plus one `unfold` for recursive definitions and globals).

## 1. Design decisions

### 1.1 What gets embedded

The pure AST as it reaches `src/extract/Extract.ml`, after all micro-passes. That is the
exact input of the shallow printer, so the theorem states that the two printers agree on
the same term. Loops have already been turned into `_loop` functions or into applications
of the `loop` combinator at that point, so the deep AST does not need a loop binder.

### 1.2 Deep structure, shallow leaves

The Lean AST is indexed by a typing context and a result type, both made of ordinary Lean
types. Binders use typed de Bruijn indices. Constants, called functions, globals, trait
method references and projectors are shallow leaves that carry a tag for inspection.
Generics, const generics and trait clauses stay outside the deep term, as Lean binders of
the generated definition.

Sketch (the exact constructor list is settled by the spike, see phase 1):

```lean
namespace Aeneas.Deep

inductive Var : List Type → Type → Type 1
| zero : Var (τ :: Γ) τ
| succ : Var Γ τ → Var (σ :: Γ) τ

/-- Irrefutable patterns; `Δ` lists the bound types in binding order. -/
inductive Pat : Type → List Type → Type 1
| var    : Pat τ [τ]
| ignore : Pat τ []
| pair   : Pat α Δ₁ → Pat β Δ₂ → Pat (α × β) (Δ₁ ++ Δ₂)

mutual
/-- `if` conditions, mirroring what the shallow printer emits. -/
inductive Cond : List Type → Type 1
| bool : Expr Γ Bool → Cond Γ                 -- `if b` elaborates to `ite (b = true)`
| lt   : Expr Γ α → Expr Γ α → Cond Γ         -- `if x < y`, Prop-valued
| ...

inductive Expr : List Type → Type → Type 1
| var     : Var Γ τ → Expr Γ τ
| leaf    : Leaf → τ → Expr Γ τ               -- literal / fn / global / projector, plus a tag
| app     : Expr Γ (α → β) → Expr Γ α → Expr Γ β
| lam     : Pat α Δ → Expr (Δ ++ Γ) β → Expr Γ (α → β)
| let_    : Expr Γ α → Pat α Δ → Expr (Δ ++ Γ) β → Expr Γ β
| bind    : Expr Γ (Result α) → Pat α Δ → Expr (Δ ++ Γ) (Result β) → Expr Γ (Result β)
| ite     : Cond Γ → Expr Γ τ → Expr Γ τ → Expr Γ τ
| match_  : Expr Γ σ → Elim σ shape → Branches Γ shape τ → Expr Γ τ
| loop    : Expr Γ (α → Result (ControlFlow α β)) → Expr Γ α → Expr Γ (Result β)
| shallow : Vars Γ tys → Fn tys τ → Expr Γ τ  -- escape hatch for unsupported constructs
end

@[expose] def Expr.denote : Expr Γ τ → Env Γ → τ   -- structural recursion
```

### 1.3 Matches use generated eliminators

A match node carries a shape (the list of field types per variant) and an eliminator of
type `σ → Alts shape τ → τ`. For each user ADT, deep mode prints a small `@[reducible]`
eliminator wrapping `T.casesOn` with a constant motive. The library ships eliminators for
`Option`, `Prod`, `ControlFlow`, `Bool` and the other builtin types that appear in matches.
Because the shallow `match` also unfolds to `T.casesOn`, both sides are definitionally
equal.

### 1.4 The theorem is `rfl`, modulo one unfolding for recursion

The generated file contains one deep term and one theorem per function:

```lean
def mul2_add1.deep : Deep.Expr [Std.U32] (Result Std.U32) :=
  .bind (.binop .add (.var .zero) (.var .zero)) .var
        (.binop .add (.var .zero) (.leaf .lit 1#u32))

theorem mul2_add1.deep_eq (x : Std.U32) :
    mul2_add1 x = mul2_add1.deep.denote (x ::ₕ []ₕ) := by rfl

-- recursive or partial_fixpoint function: the deep term calls the shallow `list_nth` as a leaf
theorem list_nth.deep_eq {T : Type} (l : CList T) (i : Std.U32) :
    list_nth l i = list_nth.deep.denote (l ::ₕ i ::ₕ []ₕ) := by unfold list_nth; rfl
```

Deep terms are never recursive, so they always compile without `partial_fixpoint`.
Globals are `@[irreducible]`, so their theorem also goes through `unfold`.

### 1.5 The denotation must mirror the custom `do` elaborator exactly

This is the one hard contract of the design. The elaborator in
`backends/lean/Aeneas/Do/Elab.lean` produces a fixed term shape per construct, and each
denotation clause has to reduce to it:

| Pure construct | Shallow term after elaboration | Denotation clause |
|---|---|---|
| monadic `let x ← e` | `Aeneas.Std.bind e (fun x => k)` | same `bind` |
| `let (a, b) ← e` | `bind e (uncurry fun a b => k)`, right-nested | `Pat.uncurry` built the same way |
| pure `let x := e` | zeta `let` | zeta `let` |
| `if c` | `ite c inst t e`, with `c : Prop` or `b = true` | `Cond.denote` plus a `Decidable` instance chosen by cases |
| `match x with` | matcher unfolding to `T.casesOn` | generated eliminator |
| single-constructor pattern | `T.casesOn` | `Pat` clause, equal by structure eta |
| `loop (fun … => body) init` | `Std.loop` | `Std.loop` |
| `x + y` on scalars | `HAdd` instance returning `Result` | same operator as a tagged leaf |

Matches on scalar literals such as `| 0#uscalar =>` elaborate through decidable equality
and need their own treatment. They stay on the escape hatch until phase 3.

### 1.6 Universe

The AST indices live in `Type`, so deep terms are stated at universe zero. The shallow
definitions are universe polymorphic, and the theorem only covers their `Type 0` instance.
Rust types all live there, so this is not a practical restriction, but it must be
documented.

### 1.7 Output layout and naming

Print into a separate file rather than interleaving with the shallow output. In split mode
that is `Deep.lean` next to `Funs.lean`, and `<Crate>Deep.lean` otherwise. The file imports
the shallow module and `Aeneas.Deep`, and the generated library entry point gains an import
for it. The shallow output stays byte-identical, so existing proofs are unaffected and the
deep file can be ignored or regenerated independently.

Names are `f.deep` and `f.deep_eq`, registered through the names map the way decreases
proofs are (see `ctx_add_decreases_proof` in `src/extract/ExtractBase.ml`), so collisions
are detected.

### 1.8 Alternatives considered

- **Fully deep embedding** with type codes and a universal value domain. Gives a
  compiler-level semantics, but every theorem becomes a real proof rather than `rfl`, and
  it needs an interpreter with environments and fuel. Keep as an optional later phase if
  someone needs to reason about the translation generically.
- **PHOAS binders.** Denotation is trivial but the term is hidden under Lean lambdas, which
  defeats inspection.
- **Lean-side reifier** reading the elaborated term and rebuilding the AST. Avoids OCaml
  work but loses the pure-AST structure and the Rust-level metadata, which is the point of
  printing from the backend. Useful later as a cross-check.

## 2. Phases

### Phase 1: spike, Lean only

- Write `backends/lean/Aeneas/Deep/Basic.lean` with the sketch above.
- Hand-write deep terms for four functions from the Demo and Loops tests: a bind chain
  (`mul2_add1`), a lambda with a backward function (`choose`), a recursive match
  (`list_nth`), and a loop (`sum_loop`).
- Confirm every row of the contract table by printing the elaborated shallow terms with
  `pp.all`, and confirm the `rfl` proofs.
- Time `rfl` on a hand-built term the size of the largest Hashmap function.
- Stop and revisit the design if any contract fails.

### Phase 2: MVP in the compiler

- Add `Config.extract_deep` and a `-deep` flag in `src/Main.ml`, Lean-only like
  `-emit-json`, rejected with `-decreases-clauses` because the dependent `if h:` form breaks
  the contract.
- Create `src/extract/ExtractDeep.ml`, registered in the dune module list, mirroring the
  structure of `extract_texpr` but keeping a stack of opened free-variable ids to compute
  de Bruijn indices.
- Support variables, leaves, application, lambda, pure and monadic lets with variable and
  tuple patterns, `if`, `ok`, `fail`, and the `loop` combinator. Everything else goes through
  the `shallow` escape hatch so that coverage is total from day one.
- Add the `extract_deep` field to `gen_config`, the file generation in `src/Translate.ml`,
  and the entry-point import.
- Enable it on the Demo and Loops tests with a `//@ [lean] aeneas-args=-deep` comment, add
  the lakefile entries, run `gmake test`, then `lake build` in `tests/lean`.

### Phase 3: patterns and matches

- Add `Cond`, the `Pat` and `match_` nodes, the library eliminators for builtin types, and
  the generated per-type eliminators printed in the deep file.
- Handle struct construction and update as constructor plus projector leaves, which is what
  structure instance notation elaborates to.
- Add scalar literal matches.
- Enable the Adt, Traits, Closures, SwitchTest and Joins tests.

### Phase 4: recursion, loops to recursive functions, globals

- Emit `unfold f; rfl` for functions flagged `is_rec` or for loop functions.
- Cover `-loops-to-rec`.
- Cover globals with the same unfolding.
- Enable Constants, LoopsRec and Hashmap.

### Phase 5: polish and documentation

- Refine leaf tags with the Rust name, loop id and call kind.
- Record the deep names in the JSON manifest (`src/EmitJson.ml`).
- Document the mode in `documentation/` and the relevant skill files (the compiler-dev skill
  asks for this after any Lean backend change).
- Measure the build time of the deep files in CI and decide whether deep mode stays opt-in
  per test.

Optional later work: a deep embedding of the type declarations themselves, and the fully
deep variant if someone needs to reason about the translation generically.

## 3. Risks to watch

- **`rfl` cost on large bodies.** Definitional unfolding of a structurally recursive
  denotation on a term with hundreds of binds may be slow. Phase 1 measures it; the
  fallback is `simp only [Expr.denote, …]` with the generated heartbeat limit.
- **Decidable instance mismatch in `if`.** The instance picked by `Cond.dec` must be the
  same constant that instance synthesis picks for the shallow term, otherwise `rfl` fails.
  The spike checks this per condition kind.
- **Module system.** Generated files use `@[expose] public section`, and `Expr.denote` and
  the eliminators must be exposed too, or `rfl` cannot see through them from the deep file.
- **Elaboration time of the deep terms.** Heavy implicit inference on nested constructors
  can be slow. Print explicit context annotations where the spike shows they are needed.

## 4. Phase 1 log (2026-11-10)

Status: **the design holds.** Every contract row exercised by the spike is verified by a
closed proof, across a module boundary, with no axioms beyond `propext`,
`Classical.choice` and `Quot.sound`.

Files:

- `backends/lean/Aeneas/Deep/Basic.lean`: `HList`, `Var`, `Pat`, `Cond`, `Expr`,
  `Branches`, the denotation, builtin eliminators, and the `Expr.lit/call/ok/pair/binop/…`
  helper abbreviations the printer will use.
- `backends/lean/Aeneas/Deep/Tactic.lean`: `deep_rfl` (kernel-only reflexivity, the default
  for generated theorems) and `deep_rfl_meta` (delta-expands matchers, then `Meta` refl, for
  debugging).
- `backends/lean/Aeneas/Deep/Tests/Shallow.lean`: shallow definitions copied from the Demo
  and Loops tests, in a `module` with `@[expose] public section` like generated code.
- `backends/lean/Aeneas/Deep/Tests.lean`: hand-written deep terms and theorems for
  `mul2_add1`, `use_mul2_add1`, `use_incr`, `choose`, `i32_id`, `list_nth`,
  `list_nth_mut`, `sum_loop.body`, `sum_loop`, `sum`, plus a structural function over the
  AST (`numBinds`) to show the terms are inspectable.
- `Aeneas.lean` imports `Aeneas.Deep`.

Contract table outcome:

| Construct | Verified by | Notes |
|---|---|---|
| monadic `let x ← e` | `mul2_add1`, `sum` | plain `rfl` |
| `let (a, b) ← e` (`uncurry`) | `list_nth_mut` | equal by structure eta of `Prod` |
| bare monadic statement (`let _ ←` dropped by the printer) | `use_incr` | `Pat.ignore` |
| pure `let x := e` | `choose`, `list_nth_mut` | the unfolding lemma shows `have`; `isDefEq` handles both |
| `if b` with `b : Bool` | `choose` | `Cond.bool`, instance `instDecidableEqBool` |
| `if x = c`, `if x < y` on scalars | `i32_id`, `list_nth`, `sum_loop.body` | the instance stored in `Cond` is the one synthesis finds |
| `match` on a user ADT | `list_nth`, `list_nth_mut` | needs `deep_rfl`/`deep_rfl_meta`, see below |
| lambda with tuple pattern | `sum_loop` | structure eta again |
| `loop body init` | `sum_loop` | plain `rfl` |
| recursive `partial_fixpoint` function | `i32_id`, `list_nth`, `list_nth_mut` | `unfold f` then reflexivity |
| universe-polymorphic shallow def | `choose` | theorem stated at `Type` |

Two facts changed the plan:

1. **Plain `rfl` cannot prove the match cases.** `Meta.isDefEq` never delta-expands a
   matcher application (`f.match_1`) stuck on a variable (`Lean.Meta.unfoldDefinition?`
   returns `none` for matchers when smart unfolding is on), so it cannot equate it with the
   `T.casesOn` application of the deep eliminator. Disabling smart unfolding globally works
   but blows the recursion depth on 100 binds. The fix is a tactic: `deep_rfl` assigns
   `Eq.refl lhs` and lets the kernel check, which handles matchers natively;
   `deep_rfl_meta` delta-expands the matchers of the goal first and then runs the usual
   reflexivity, for readable failures. Generated theorems use `by deep_rfl` and
   `by unfold f; deep_rfl`.
2. **The kernel path is also the fast one.** Timings on a synthetic chain of `n` binds
   (`let x_{i+1} ← x_i + 1#u32`), with the heartbeat and recursion limits generated files use:

   | n | `rfl` (Meta) | `deep_rfl_meta` | `deep_rfl` (kernel) | kernel check of the deep term itself |
   |---|---|---|---|---|
   | 100 | 0.54 s | 0.58 s | 0.11 s | 0.45 s |
   | 300 | 8.8 s | 9.8 s | 0.32 s | 3.8 s |

   Meta-level reflexivity is superlinear; the kernel is close to linear. The remaining
   superlinear cost is the kernel check of the deep term *definition*: every node carries
   its context `Γ` as an implicit argument, so the elaborated term is quadratic in the
   nesting depth. This is fine for the sizes Aeneas produces (the largest Hashmap function
   has about 25 binds) and only matters for functions with hundreds of binds. The shallow
   `do` elaborator itself hits the recursion limit at 1000 binds, so that is the ceiling
   anyway.

Smaller findings:

- Instance arguments of `Cond` constructors (`[inst : DecidableEq α]`, `[ord : LT α]`)
  must be bound explicitly in patterns (`.lt (ord := o) (inst := i) a b`), otherwise
  instance synthesis gets stuck on the pattern. Printing is unaffected (synthesis fills
  them at construction time). Keep them named.
- `Expr.denote` must stay structurally recursive (it is). Structural recursion over the
  mutual family works with `termination_by structural`.
- Matchers of the shallow module are visible across the module boundary with
  `@[expose] public section`, so the separate deep file layout is fine.
- `#print axioms` on every theorem: `propext`, `Classical.choice`, `Quot.sound` only.

Not exercised by the spike, deferred to phase 3 as planned: struct construction and
update, single-constructor (`⟨a, b⟩`) patterns, matches with a default `_` branch, matches
on scalar literals (`| 0#uscalar =>`), closures, trait method calls, globals.

## 5. Phase 2 log (2026-11-10)

Status: **the MVP works end to end.** `aeneas -backend lean -deep` prints a deep term and
a denotation theorem for every transparent function; the Demo and Loops tests build with
them (14 and 108 theorems, no `sorry`), with 4 and 19 escape hatches, all of them for
`match` expressions, as planned.

Files:

- `src/extract/ExtractDeep.ml` (new): the deep printer. `extract_fun_decl_deep` prints the
  `def f.deep` and `theorem f.deep_eq`; `extract_deep_texpr` mirrors `extract_texpr`.
- `src/Config.ml`, `src/Main.ml`: the `-deep` flag (Lean only, rejected with
  `-decreases-clauses`, `-use-fuel`, `-borrow-check`).
- `src/Translate.ml`: `gen_config` gets `extract_deep` and `append_deep`; the function
  groups dispatch to the deep printer; the file generation.
- `src/pure/PureMicroPassesGeneral.ml`: a real typing bug fixed on the way, see below.
- `backends/lean/Aeneas/Deep/Basic.lean`: two new nodes, `Expr.decide` and
  `Expr.assert`, see below.
- `tests/src/demo.rs`, `tests/src/loops.rs`: `//@ [lean] aeneas-args=-deep`.

Design decisions taken during the implementation:

1. **Leaves are eta-expanded shallow terms.** Rather than printing the head of a call,
   constructor, projector or operator as a bare constant, the printer reuses the shallow
   printer on the application with fresh variables for the arguments, wrapped in a
   typed lambda: `(.leaf (.fn "demo::incr") (fun (i : Std.U32) => (incr i : Result Std.U32)))`.
   This makes the denotation beta-reduce to *exactly* the shallow term, whatever
   notation, implicit argument or coercion the shallow printer relies on, and it covers
   every qualifier uniformly (struct updates and array literals included). The tag keeps
   the Rust-level identity of the leaf.
2. **Output layout.** Lean module names depend on where the destination directory sits
   under the lake root, which Aeneas does not know. In split mode the convention already
   exists (`Crate.Funs` imports `Crate.Types`), so the deep terms go to a separate
   `Deep.lean` importing `Funs` and the library entry point imports it. In non-split mode
   the deep terms are **appended at the end of the single generated file**, after a
   `/-! ## Deep embedding of the function bodies -/` header: the shallow part of the file
   is unchanged as a prefix, and no import is needed. (The first attempt with a separate
   file produced an import cycle on the Demo test.)
3. **Propositions versus booleans.** The pure AST types comparisons as `Bool`, but the
   shallow printer prints them with infix notations that Lean elaborates to `Prop`, and
   each consumer decides what happens next: `if` and `massert` take the proposition
   (`massert (b : Prop) [Decidable b]`), everything else gets a `decide` coercion. The
   deep AST now mirrors this: `Cond` for `if`, a new `Expr.assert (c : Cond Γ)` node for
   `massert`, and a new `Expr.decide (c : Cond Γ) : Expr Γ Bool` node for comparisons in
   boolean positions. A non-monadic `let` binding a comparison would bind a `Prop` in the
   shallow code; the printer falls back to the escape hatch for it (none occur in the
   tests).
4. **Type annotations come from the context, not from the AST.** The `ty` field of
   application nodes is not reliable after the micro-passes. The printer threads an
   expected type down from the function signature and from the let-binding patterns and
   uses it for the leaf annotation, falling back to the type derived from the head. The
   case that revealed this was `Array.update` in `copy_carray`: the micro-pass introducing
   `UpdateAtIndex` typed its result with the type of the continuation instead of
   `Result (Array …)`. That bug is fixed in `PureMicroPassesGeneral.ml` as well.
5. **Escape hatch layout.** `(.shallow (fun | x ::ₕ y ::ₕ .nil => (BODY)))` is printed
   with vertical boxes so that the body always starts to the right of the `|`, which the
   parser requires.

Known gaps carried to the next phases:

- Matches, single-constructor patterns, scalar literal matches: escape hatch (phase 3).
- Names `f.deep` and `f.deep_eq` are not registered in the names map, so a Rust item named
  `deep` inside `f` would clash. Register them like the decreases proofs (phase 5).
- Leaf tags use the internal debug names of the pure AST (`"panic.+::<u32>"`,
  `"@Result::Ok"`); switch to Rust names when polishing (phase 5).
- The `Pure Return`/`Pure Fail` builtins and the `Result` constructors are both handled,
  but `fail` with a non-closed error argument falls back to a generic leaf.

## 6. Phase 3 log (2026-11-10)

Status: **matches and struct patterns are deep.** Over the eight test modules with deep
mode enabled, only five escape hatches remain, all of them for constructs that cannot be
mirrored definitionally (see below).

| Module | Theorems | Escape hatches | Eliminators generated |
|---|---|---|---|
| Demo | 14 | 0 | 5 |
| Loops | 108 | 0 | 29 |
| Adt | 2 | 0 | 1 |
| Traits | 34 | 0 | 3 |
| Closures | 20 | 0 | 0 |
| SwitchTest | 1 | 1 (literal match) | 0 |
| Joins | 9 | 3 (literal matches) | 3 |
| Hashmap (split mode, `-loops-to-rec`) | 30 | 1 (default branch) | 11 |

No `sorry` anywhere; the whole `tests/lean` suite builds.

What was added:

- **Per-type eliminators.** In deep mode the type pass prints, for every type extracted
  as an inductive (transparent, non-builtin, not a tuple struct), a reducible
  `T.deepElim : Aeneas.Deep.Elim (T params) [[fields of variant 0], ...]` defined as
  `fun x alts => T.casesOn x alts.1 alts.2.1 ...`. Type parameters are implicit. The
  eliminators come before the function terms thanks to the declaration order. Builtin
  types rely on the library: only `Option` for now (`Aeneas.Deep.Option.deepElim`).
- **Matches.** `plan_deep_match` checks that every branch is a constructor pattern with
  simple field patterns (ignored fields get fresh variables, since the matcher's
  alternatives take all fields), that every variant is covered, and that the scrutinee's
  type has an eliminator; it then prints `(.match_ scrut T.deepElim (.cons br₀ (.cons br₁ .nil)))`
  with the branches in variant order. Anything else goes through the escape hatch.
- **Struct patterns** (`let ⟨ a, b ⟩ := e`, `let ⟨ a, b ⟩ ← e`) are printed as single-branch
  matches: the custom `do` elaborator compiles them to `S.casesOn`, so the same node
  works. The monadic form binds the value first (`.bind e .var (.match_ (.var .zero) …)`),
  which is exactly `bind e (fun x => S.casesOn x …)`. Tuple structs are treated as tuples.
- **Expected types** flow into the match scrutinee of a struct pattern (the pattern's
  type) and into every branch.

Limitations established by experiment (in the Lean spike, across a module boundary):

- **Default branches** (`| _ => e`). Lean compiles them to an auxiliary
  `f._sparseCasesOn_n` built on `T.rec` with the motive
  `fun t => (Nat.hasNotBit … t.ctorIdx → motive t) → motive t`, which is not
  definitionally equal to a `T.casesOn` with the default duplicated per variant (both
  the kernel and `Meta.isDefEq` reject it). Such matches stay on the escape hatch. They
  are rare in Aeneas output because the symbolic execution expands every variant; the
  one occurrence in the tests is `match o with | some x => … | _ => …` in Hashmap.
- **Scalar literal matches** (`| 0#uscalar => …`) elaborate to `UScalar.casesOn a (fun bv =>
  dite (bv = 0#32) (Eq.ndrec_symm (h_1 ())) …)`, a shape with casts that no simple
  node mirrors. They stay on the escape hatch. A later refinement could print a node that
  reproduces this shape exactly, or the micro-passes could turn such switches into
  `if` chains before extraction.
- Nested patterns and variable patterns binding the whole scrutinee are not supported
  (escape hatch); none occur in the tests.

Phase 4 (recursion, `-loops-to-rec`, globals) is partly done already: recursive
functions and `-loops-to-rec` work (Hashmap). Globals are still skipped.

## 7. Phase 4 log (2026-11-10)

Status: **globals, recursion and `-loops-to-rec` are covered.** Deep mode is enabled on
ten test crates; the whole `tests/lean` suite builds.

| Module | Theorems | Escape hatches |
|---|---|---|
| Demo | 14 | 0 |
| Loops | 109 | 0 |
| Adt | 2 | 0 |
| Traits | 39 | 0 |
| Closures | 20 | 0 |
| SwitchTest | 1 | 1 |
| Joins | 9 | 3 |
| Hashmap (split, `-loops-to-rec`) | 30 | 1 |
| Constants | 28 | 0 |
| LoopsRec (`-loops-to-rec`) | 84 | 0 |

What was added:

- **Globals.** The deep pass now runs `export_global` too (`extract_globals = true` in the
  deep configs). The function printer was refactored into `extract_decl_deep`, shared by
  `extract_fun_decl_deep` and the new `extract_global_decl_deep`, which prints the deep
  term of the initializer's body (the global's type is the initializer's output type, as in
  the shallow printer) and a theorem proved by `unfold X; deep_rfl`, since globals are
  `@[irreducible]`. Generic globals (trait constants) work: the generics become binders of
  `X.deep` and explicit arguments in the theorem, exactly as for functions. The loops of a
  global initializer go through the ordinary function path.
- **Recursion and `-loops-to-rec`** needed no new code: recursive groups already got
  `unfold f; deep_rfl`, and Hashmap and LoopsRec exercise both.

Nothing new was found in the contract table: the shallow printer's `:= do` versus `:=`
choice for globals does not matter, because `Expr.bind` denotes `Std.bind` either way.

Still deferred: default branches and scalar-literal matches (hard limits, see phase 3),
registration of the `.deep`/`.deep_eq` names in the names map, Rust names in leaf tags,
documentation and skill files (phase 5).

## 8. Phase 5 log (2026-11-10)

Status: **done.** Polish and documentation.

- **Names.** `f.deep` and `f.deep_eq` are now registered in the names map
  (`ExtractBase.id` has `DeepTermId`/`DeepEqId`, wrapping the `FunId`/`GlobalId` of the
  declaration; `ctx_add_deep_names` is called from `ctx_add_fun_decl` and
  `ctx_add_global_decl` when `-deep` is set). The printer looks the names up instead of
  concatenating, so a Rust item that would clash is reported like any other collision.
- **Manifest.** With `-emit-json -deep`, function and global entries carry `deep_term`
  and `deep_theorem` (full Lean names). The fields are absent otherwise, so existing
  manifests are unchanged.
- **Leaf tags** keep the Rust-side names already produced by the pure-AST printers
  (`crate::f`, `^loopN`, `@assert`, `panic.+::<u32>`, …); their format is now documented
  on the `Leaf` type.
- **Build time**, measured as wall-clock `lean` elaboration including imports:

  | Module | Shallow only | With the deep section |
  |---|---|---|
  | Loops (109 theorems) | 3.5 s | 4.4 s |
  | Constants (28 theorems) | 2.6 s | 2.7 s |
  | Hashmap `Funs.lean` / `Deep.lean` | 2.8 s | 3.0 s |

  The cost is modest; deep mode stays opt-in per test (`//@ [lean] aeneas-args=-deep`).
- **Documentation.** New `documentation/deep-embedding.md` (usage, generated artifacts,
  the AST, tactics, writing functions over deep terms, limitations, performance,
  implementation notes); entries in `CLAUDE.md`, `documentation/README.md` and the file
  layout table of `aeneas-overview.md`; `emit-json.md` describes the new fields. Skill
  files: `aeneas-lean-core` mentions `Deep.lean` in the file layout, and
  `aeneas-compiler-dev` gets a "Deep Printing Mode" section with the rules for touching
  the mode (mirror the elaborated term, escape hatch over errors, reuse the shallow
  printer for leaves, do not trust application-node types, how to test).

Open items, out of scope of this plan:

- Default-branch and scalar-literal matches on the escape hatch (hard limits, phase 3).
  The cleanest fix is upstream: make the micro-passes produce `if` chains for scalar
  switches, and avoid wildcard branches.
- `Aeneas.lean` imports `Aeneas.Deep`, including the spike tests, so CI compiles them;
  kept as is by decision. Dropping the tests from the umbrella would need a lakefile
  target to keep them in CI.
- The spike's `Tests.lean` could grow into a proper regression suite for the contracts
  (one hand-written theorem per construct).

## 9. Realistic trial: curve25519-dalek (2026-11-10)

The Beneficial-AI-Foundation `curve25519-dalek-fork` extracts the crate with the Aeneas
release pinned at exactly this tree's base commit, with `-split-files -emit-json` over four
target configurations. Re-running its pipeline with the local binaries plus `-deep`:

- the shallow `Funs.lean` and `Types.lean` are byte-identical to the committed ones;
- `Deep.lean` (1,912 theorems for 1,046 functions and the globals, 17 eliminators) builds
  in 95 s against 46 s for `Funs.lean`, with the fork's Lean project pointed at the local
  Aeneas library.

Three rounds were needed, each fixing a real gap:

1. 55 escape hatches at first: 40 matches on `core::cmp::Ordering` (no library
   eliminator: added `Ordering.deepElim`), 12 `let ⟨ x ⟩ := e` on single-variant *enums*
   (the planner only accepted structures), 3 literal matches on `Nat` (hard limit).
2. Two kernel rejections: the `fun | x ::ₕ … ::ₕ .nil =>` escape hatch on an environment
   of 14 variables made Lean generate a matcher the kernel rejects. The escape hatch now
   binds the variables with `let x := Var.get … «deep env»` lines, which involve no
   matcher. And the two basepoint-table constants exceeded `maxRecDepth 2048`; the deep
   output now uses at least 10000.
3. The same two constants (chains of 768 monadic binds) then exceeded the heartbeat
   budget while elaborating their deep terms. Two rules were added: closed sub-terms
   larger than 64 nodes become single shallow leaves, and bodies with more than 500
   let-bindings are escaped as a whole. The largest fully deep body has 260 binds.

Final count: 5 escape hatches out of 1,912 (3 literal matches, the 2 tables), 9 closed
leaves, no `sorry`. The reproduction script is the fork's `scripts/aeneas-translate.sh`
with the local `charon`/`aeneas` and `-deep` added, and `lakefile.toml` pointing the
`aeneas` requirement at `backends/lean` by path.
