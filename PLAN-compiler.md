# Plan: a verified compiler from the deep representation to a small imperative language

Goal: a compiler, written and verified in Lean, from the deep terms produced by `-deep`
(`Aeneas.Deep.Expr`, see `PLAN.md` and `documentation/deep-embedding.md`) to a small
C-shaped imperative IR, with a proof that the compiled program behaves like the deep
term's denotation, hence (by the `f.deep_eq` theorems) like the translated Rust function.
C itself is produced from the IR by a small *trusted* printer, as in Fiat-Crypto: the
verified pipeline stops at the IR, and the printer is kept small enough to review and is
checked by differential testing.

## 0. What the deep representation gives and lacks

The deep AST has first-order *control structure* (binds, lets, ifs, matches, loops) but
*shallow leaves*: a call `incr x` is `(.leaf (.fn "demo::incr") (fun x => incr x))`, an
addition is `(.leaf (.binop "panic.+::<u32>") (fun x y => x + y))`. The leaf's string tag
is metadata; the leaf's meaning is an opaque Lean function. This was the right choice for
the `rfl` theorems, but a compiler cannot compile a Lean function: it needs to know *which*
function or primitive a leaf is, as data. The first phase of this project is therefore a
**first-order leaf layer**, and it is the only part that touches Aeneas itself.

Data from the trial on curve25519-dalek (1,912 deep terms):

| | count |
|---|---|
| monadic binds / pure lets | 7,919 / 477 |
| calls (leaves tagged `.fn`) | 8,101 |
| constructors / projections / binops / unops / globals | 1,559 / 979 / 1,385 / 419 / 292 |
| matches / ifs / asserts / loops | 348 / 144 / 85 / 291 |
| lambdas outside loop bodies (closures) | 6 definitions |
| applications of a variable (calls to backward functions returned by callees) | 194 |

Nearly everything is first-order straight-line code with calls, matches and loops. The
two higher-order features come from Aeneas's treatment of mutable borrows: a function
returning `&mut` yields a backward closure (6 definitions here), and library functions
such as `index_mut` return one that the caller applies later (194 sites). A small
imperative language has no closures, so these need a dedicated treatment (section 3).

## 1. Phase A: first-order leaves (Aeneas side)

Replace the string-tagged leaves by structured, generated data, keeping the shallow value
next to it so that the `rfl` theorems keep working:

- **Primitives.** Dedicated nodes with a *fixed* denotation defined in the library:
  `scalarBinop (op : ScalarBinOp) (ty)`, `scalarUnop`, `cast`, comparisons (already
  `Cond`), `ok`, `fail`, `assert`, tuples, `decide`. For each, the library defines
  `op.denote` by cases (`| .add, ty => HAdd.hAdd`), reducible, so that the shallow printer's
  `x + y` and the deep node denote the same term definitionally. The printer stops
  eta-expanding these leaves.
- **Closed world of the crate.** Per crate, generate an inductive `FunName` (one
  constructor per translated function, with its signature as data `sig : FunName → Sig`),
  an implementation table `impl : (f : FunName) → f.sig.denote` (the shallow functions),
  a deep table `deepImpl : (f : FunName) → Expr f.sig.inputs f.sig.output`, and the
  assembled theorem `∀ f, impl f = fun args => (deepImpl f).denote args` (from the
  per-function `deep_eq`). Calls become `Expr.call (f : FunName) (args)`, denoting
  `impl f`. Likewise a `TypeName` inductive with variant/field descriptors, and
  constructor / projection / match nodes indexed by it; the generated eliminators gain the
  *lawful* decomposition `cases : T → Σ i, HList (fields i)` with the law
  `elim x alts = uncurry (alts i) (cases x)`, proved by `cases x; rfl`, so that a compiler
  and its proof can inspect scrutinees.
- **Library primitives.** Calls to the standard-library models (`Array.index_usize`,
  `Vec.push`, `core.num.U32.wrapping_add`, …) become `Expr.prim (p : PrimName) (args)`
  with a fixed denotation table in the library; the target language reuses this table for
  its own primitive instructions, so their correctness is by reflexivity. A `PrimName`
  enumeration is maintained by hand (or extracted from the `rust_fun` attributes), and it
  only contains operations the C printer can express (with an explicit check for the
  fallible ones).
- **Trait implementations.** Trait impls are records of functions; a method call through
  a dictionary parameter is a projection followed by a call. Generate an `ImplName` table
  (impl → method → `FunName`) so that, once generics are instantiated, such calls resolve
  to direct calls at compile time.

Everything else (generics as binders, `HList` environments, `rfl` theorems) is unchanged.
After this phase a deep term is a closed first-order program over named functions and
primitives, which is what a compiler consumes.

## 2. Phase B: the C-shaped IR and its semantics

A WHILE-style language shaped like C, whose *values are Lean values* of the shallow types
(a typed store), and whose semantics is a definitional interpreter into the same `Result`
monad as the translation:

```
e ::= x | lit | prim p (e₁ … eₙ) | ctor T v (e₁ … eₙ) | proj T f e            -- pure, C-expressible
s ::= x := e | x ← call f (e₁ … eₙ) | x ← prim p (…) (fallible primitives: checked arithmetic, …)
    | s₁ ; s₂ | if c then s₁ else s₂ | switch e { v ⟨x₁ … xₖ⟩ ⇒ s } | assert c
    | loop s | continue | break | return e | fail err
```

`exec : Stmt → Store → Result (Store ⊕ Value)` is defined by structural recursion plus
`partial_fixpoint` for `loop`, exactly like `Std.loop`. Choosing the same monad is what
makes the correctness statement an *equation* rather than a simulation diagram, following
the Interaction-Trees approach to compiler correctness (both semantics denote into the
same monad; correctness is equality/bisimulation of the two denotations).

Decisions fixed by the C target:

- **Typed store with Lean values.** The IR keeps Lean types (`U32`, generated ADTs,
  `Array α n`, `Vec α`, …); the printer maps them to C types. No untyped value domain and
  no encoding lemmas: since the printer is trusted anyway, the verified part gains nothing
  from a memory-level value representation, and the typed IR gives the printer the type
  information it needs.
- **Tuples are flattened** into one local per component in the IR, and a function
  returning a tuple returns through out-parameters. The store invariant of the proof
  relates an environment tuple to its component variables.
- **Monomorphic instances.** The compiler runs on deep terms instantiated at concrete
  types and dictionaries (`f.deep (T := U32) inst`), so the IR has no generics. A
  monomorphization pass computes the set of instances reachable from the entry points
  (the public Rust functions); each instance is compiled and proved separately, and
  dictionary method calls resolve to direct calls through the `ImplName` table.
- **Primitives are C-expressible.** Fallible scalar operations (overflow-checked
  arithmetic, shifts, casts, division) are fallible IR primitives whose failure the
  printer renders as a check plus error return; wrapping and bit operations are pure.
  Anything outside the `PrimName` table makes the function uncompilable, reported as such.
- **Value semantics.** Arrays and vectors are copied in the IR semantics. In-place updates
  are a printer concern (section 7).

## 3. Phase C: closures and mutable borrows

Options, in the order they should be tried:

1. **First-order fragment only.** Compile functions whose deep terms have no `lam` outside
   loop bodies and no application of a variable; report the rest. On dalek this covers all
   but the 6 definitions with closures and the 194 backward-function sites (which cluster
   in a limited number of functions).
2. **Borrow idioms.** The 194 sites follow a fixed shape produced by Aeneas:
   `let (x, back) ← index_mut v i; …; let v' := back x'`. The compiler recognizes the
   shape and lowers it to the imperative `x := v[i]; …; v[i] := x'`, with one lemma per
   library primitive relating the model of `index_mut` and its backward function to the
   in-place update (`back x' = Array.update v i x'`, provable from the models). This is
   the inverse of Aeneas's own transformation and recovers the imperative view of `&mut`.
3. **General closures by defunctionalization.** Each `lam` becomes a tagged environment
   record plus a generated `apply` function; the proof is a classic but sizeable
   simulation. Only if (1)+(2) leave something that matters. For the backward functions
   returned by *translated* functions (`choose`, `list_nth_mut`), the same idiom as (2)
   applies at the call sites, so (3) may never be needed.

## 4. Correctness statement and proof structure

For a translated function `f` with first-order deep term `d = deepImpl f`:

```
theorem compile_correct (f : FunName) (args : HList f.sig.inputs) :
  exec (compileFun f) (storeOf args) = Result.map (fun v => inr v) (impl f args)
```

(`impl f args = (deepImpl f).denote args` is the deep theorem; the right-hand side is the
denotation of the deep term.) The proof is by induction on the deep term with a store
invariant "the store agrees with the `HList` environment on the variables in scope":

- `var`, literals, primitives, constructors, projections: reflexivity, since the target
  primitives reuse the denotation tables.
- `bind` / `let`: `Std.bind` of the two sides, by the monad laws and the invariant on the
  extended store.
- `ite` / `assert` / `decide`: `ite` on the same decidable proposition on both sides.
- `match`: the lawful eliminator decomposes the scrutinee; `switch` does the same.
- `loop`: both sides are least fixpoints of monotone functionals in the same CCPO; the
  equation is proved by fixpoint induction (the `partial_fixpoint` induction principles
  and the `Lean.Order` library that `Aeneas.Std.WP` already uses). This is the one
  non-routine case.
- `call`: by the induction hypothesis on the callee's compiled body (the closed world
  gives a well-founded order: mutual recursion is handled by proving all functions of a
  recursive group together, or by proving the open statement "if the callees are correct
  then so is the caller" and closing it by fixpoint induction over the whole table).

Divergence and failure come for free from working in `Result`: equality of ITrees
covers `div` and `fail` without separate statements.

## 5. Phases and effort

| Phase | Content | Effort |
|---|---|---|
| A | first-order leaves: primitive nodes, `FunName`/`TypeName`/`ImplName` tables, lawful eliminators, `PrimName` table; printer and library changes; tests | 2 weeks |
| B | the IR, its interpreter, monomorphization, the compiler for the first-order fragment (straight-line, ifs, matches, calls, loops, flattened tuples) | 1 to 2 weeks |
| D | correctness proof for the first-order fragment, loops last | 2 to 3 weeks |
| C | borrow idioms (recognition, lowering, per-primitive lemmas), then measure what is left | 1 to 2 weeks |
| P | the trusted C printer and its differential tests (section 7) | 1 week |
| E | optional: defunctionalization for the remaining closures | open |

Phase A is also independently useful: it makes the deep terms closed first-order programs,
which the operational semantics discussed earlier and any other tool would want too.
Phase P can start as soon as phase B exists, before the proofs.

## 6. Risks

- **Scope creep in phase A.** The set of primitives in real code is large (the dalek
  translation references hundreds of library functions). Keep `PrimName` open-ended:
  unknown library calls stay shallow leaves and make the function uncompilable, reported
  as such, rather than blocking the whole crate.
- **Loop proof.** Fixpoint induction over two `partial_fixpoint` definitions in the ITree
  monad is the proof most likely to need library lemmas that do not exist yet.
- **Evaluation order and effects.** The deep terms are in monadic normal form, so effects
  are already sequenced; keep the target's pure expressions genuinely pure (no fallible
  primitive inside an expression) to avoid an order-of-evaluation argument.
- **Printer trust.** Everything the printer decides is unverified: type layouts, the
  `Result` calling convention, overflow checks, copying versus in-place updates. Keep each
  of these a small table or a local rule, and keep the differential tests running on every
  change.

## 7. Phase P: the trusted C printer

A small function from the IR to C text. What it decides, and therefore what is trusted:

- **Types.** Scalars to `uint*_t`/`int*_t`/`size_t`, `Bool` to `bool`, generated ADTs to
  tagged unions (structs with a tag and a union of field structs), flattened tuples to
  separate variables or a struct, `Array α n` to a fixed C array inside a struct, `Vec α`
  and slices to a length plus a heap buffer. One C program per Aeneas target configuration
  (`x86_64` / `i686`), since `usize` and the translation itself differ.
- **Calling convention.** `Result T` functions return an error code and write their value
  to an out-parameter; `fail` returns the code; `assert` checks and returns it. Calls
  propagate the code.
- **Primitives.** A table from `PrimName` to C: `__builtin_add_overflow` and friends for
  the checked operations, plain operators for wrapping and bit operations, explicit casts,
  range checks for shifts and division.
- **Memory.** Value semantics by default: assignments of arrays and structs copy. The
  borrow-idiom lowering of phase C emits an explicit in-place update instruction whose IR
  semantics is still the functional update; the printer renders it in place, which is
  sound when the old value is dead afterwards, something Rust's ownership guarantees but
  the IR does not record, so the printer applies a conservative liveness check and copies
  otherwise.
- **Differential testing.** For functions with test vectors (the RFC 7748 X25519 vectors
  in the dalek fork, for instance), compile and run the C, and compare with the Lean
  models evaluated on the same inputs. This is the check on the trusted part.

## 8. Phase A log

### A.1 Primitive nodes (2026-11-11)

Done. The AST has first-order nodes with a fixed denotation for the scalar and boolean
primitives: `scalarBinop (op) (ty)` (`+ - * / % <<< >>> &&& ||| ^^^`), `neg`, `bitNot`,
`cast`, `castFromBool`, `boolBinop` (`&& || ^^`), `boolNot`, `bne`, `uscalarLit`,
`iscalarLit`, `boolLit`, `unitLit`, and `Cond.not` for `if ¬ c`. The denotation tables
(`ScalarBinop.denote`, `ScalarTy.cast`, …) are written with the very notations the shallow
printer prints, so the `rfl` theorems hold unchanged. `ScalarTy` (`u UScalarTy | i IScalarTy`)
is the first piece of the type-descriptor language.

Two elaboration facts recorded on the way: `¬ b` in a boolean position is
`decide (¬ b = true)` and `if ¬ b` is `ite (¬ b = true) (instDecidableNot …)`; `x != y` is
`bne`, not `decide (x ≠ y)`.

Deep mode was enabled on five more Lean-only tests (CastSigned, Scalars, BoolCmp,
OverflowingOps, UintDivOps) to cover the operators; all fifteen deep-enabled modules build.
Still printed as shallow leaves: wrapping/unchecked operation modes other than the checked
one (the standard-library `wrapping_*` functions are calls, handled by A.4), `Array.to_slice`,
raw-pointer casts, char/string literals, and const-generic variables.

### A.2 Closed world of types (2026-11-11)

Done. The AST is now indexed by *type descriptors* rather than by Lean types:
`Expr N σ Γ τ` with `N` a per-crate enumeration of the type names (`TypeName`, printed at
the start of the deep section with a `TypeNames N` instance giving the Lean type and the
variants of every name), `σ : TyEnv` the interpretation of the type and const-generic
binders of the definition, `Γ : List (Ty N)`, `τ : Ty N`. The descriptors (`Ty N`: var,
scalar, bool, char, unit, str, tuple, adt with type and const-generic arguments, array,
slice, result, controlFlow, arrow) are plain data, so a consumer of a deep term can read
the type of every variable and sub-term. The environments (`Env N σ Γ`), variables and
patterns are indexed by descriptors too; patterns gained `tuple` (one sub-pattern per
component, so that each component is bound at its own descriptor).

New nodes: `tuple`, `ok`, `fail`, `continue_`, `break_`, and the ADT nodes `ctor`,
`proj`, `match_`, indexed by a type name and denoting through generated `CtorFn`,
`ProjFn`, `ElimFn` instances (one per variant / field / type). The three ADT nodes carry
the instantiated field types together with a proof that they agree with the declaration;
the printer emits `rfl`, so the denotation reduces by iota and the `rfl` theorems are
unchanged. (Substituting the type arguments into the declared field types inside
`Expr.denote` would have required a propositional substitution lemma, hence a cast.)
`Ty.denote` is reducible so that the `Decidable`/`BEq` instances of the comparison nodes
are still found by instance resolution.

Types the descriptors can not express (trait-associated types, raw pointers, types with
trait clauses, `State`, `Error`, …) are *escaped into type variables*: the printer prints
each body twice, a first pass collecting the escaped types, which are appended to the type
environment printed in the header (`⟨[T, inst.Item], [N]⟩`). This keeps the descriptors
closed (decidable equality, no Lean type inside) without losing coverage. The closed world
includes all type declarations except tuple structs (tuples) and types with trait
clauses; variants are described for local inductives and for a whitelist of builtin
types whose Lean model mirrors the Rust declaration (`Option`, `Ordering`,
`core.ops.range.Range`, `core.ops.control_flow.ControlFlow`): the other builtins
(`alloc.vec.Vec` has a single `slice` field in Lean) are opaque in the closed world.

Results on the test suite: all fifteen deep-enabled modules build; no escape hatch was
added, the struct patterns, matches, constructors and projections of the tests are all
first-order (Hashmap: 22 `ctor`, 8 `match_`, 25 `proj`, 1 `shallow`). The deep sections
cost more elaboration than before (Loops: 12 s against 4.4 s), to be looked at if it
becomes a problem (the `rfl` proofs of the ADT nodes each evaluate the field types). The
literal bound proofs are now `by decide` (the `first | decide | scalar_tac` form produced
an unused-tactic warning per literal, 2971 in dalek).

Not done yet, from the plan: the lawful decomposition `cases : T → Σ i, HList (fields i)`
with its law (to be added to `ElimFn` when phase D needs it).

### A.3 Closed world of functions and globals (2026-11-11)

Done, with the same design as A.2: per crate, `FunName` and `GlobalName` enumerations
with `FunNames FunName TypeName` and `GlobalNames GlobalName TypeName` instances, giving the
signature of every function (descriptors over its parameters) and its shallow
implementation at any interpretation of the parameters (`| FunName.list_nth, ρ =>
@list_nth (ρ.types.getD 0 Unit)`), and the type and value of every global. `Expr` is now
`Expr N F G σ Γ τ`; the new nodes are `call f targs cargs inputs output h₁ h₂ args` (a
call to a function of the crate applied to all its arguments, the instantiated signature
carried with `rfl` proofs as for the ADT nodes) and `global g targs cargs τ h`.

The tables are `defs : FunName → FunDef TypeName`, one record `⟨sig, impl⟩` per
function: the first version had separate `sig` and `impl` methods, and on curve25519-dalek
(1,562 functions) the elaboration of the `impl` table timed out, every arm's expected type
unfolding the 1,562-arm `sig` table. The enumeration constructors are the Lean names with
the non-identifier characters replaced (`edwards.EdwardsPoint.«x86_64-tables»` →
`edwards_EdwardsPoint__x86_64_tables_`); promoted constants (not extracted, their reads
are inlined) are left out of `GlobalName`.

In the closed world: the local functions (including the loop and loop-body functions and
the opaque ones) and globals without trait clauses whose signature can be described. Out
of it, and still leaves: the builtin functions (standard-library models, the A.4
`PrimName` table), the functions with trait clauses (their calls pass instances), trait
methods called through an instance (`inst.method x`, including the calls to concrete
impls, which the pure AST represents as `TraitMethod` calls; resolving them to the impl's
function is the `ImplName` work left for the monomorphization of phase B), and partial
applications. The per-crate deep table `deepImpl` and the assembled theorem of the plan
are not generated: they are only needed by the compiler proof, and will be generated when
phase D fixes their statement.

### A.4 Primitives (2026-11-12)

Done. Type names are now `TypeRef N := builtin (b : BuiltinTy) | crate (T : N)` and
function names `FunRef F := prim (p : Prim) | crate (f : F)`, so that the library can
describe, independently of any crate, the standard-library types it models (`BuiltinTy`:
`Option`, `Vec`, `Range`, `Ordering`, with their variants and the constructor/projector/
eliminator instances for the three inductive ones) and the primitive operations (`Prim`,
with `Prim.def : Prim → FunDef N` giving the signature and the implementation): the
builtins of the translation (`lift`, `Array.index_usize`, `Array.update`,
`Array.index_mut_usize` and the slice versions) and a first set of standard-library
functions (`Array.repeat`, `Array.to_slice`, `Slice.len`, `Vec.len`, `Vec.push`,
`Vec.new`). The printer maps the Lean names of the builtin types and functions to these
enumerations (`builtin_type_refs`, `prim_table`); the pure builtins are matched directly
on their identifiers, their signatures being built from the generic arguments. A
primitive's Rust trait clauses (`Clone` for `core::array::repeat`) are ignored, as the
Lean models don't take the instances.

Three things found on curve25519-dalek on the way: the denotation of a type variable must be
a reducible lookup (`tyAt`, not `List.getD`) for the `Decidable`/`BEq` instances of the
comparison nodes to be found when the compared type is an escaped type (a `String` here);
the bodies printed through the escape hatch must be annotated with their shallow type
(the auto-parameters of array literals do not see through the denotation of a descriptor);
and a builtin unit struct (`alloc::alloc::Global`, passed as a type argument to the
`IntoIterator` impl of `Vec`) must keep its Lean name rather than become `.unit` like the
tuple structs.

Still leaves, by frequency in dalek: the iterator adapters (`Range::next`, `rev`,
`step_by`, `into_iter`, `next` through clauses), `Into::into`, `Vec` indexing through
the `Index`/`IndexMut` impls (a trait clause on the index type), `core::mem::replace`,
`Option::map`, `copy_from_slice`, `Clone for [T; N]`, the `subtle` crate's trait methods.
Extending `Prim` is a matter of adding a constructor, its `Prim.def` and the table entry;
the trait-method calls are for the monomorphization of phase B.

Results of phase A on curve25519-dalek (`Deep.lean`, 117,000 lines, builds in 3 min 20 s,
no error, no warning): 1,912 theorems; 6,697 `call` nodes (2,259 of them primitives), 292
`global`, 478 `ctor`, 348 `match_`, 979 `proj`; 1,404 function leaves left (8,101 before
phase A), 5 escape hatches (unchanged), no escaped type. On the test suite: 15 modules,
all green; the Loops module (109 theorems) builds in 16 s.

## 9. Phase B log

### B.1 The IR, its interpreter, the compiler and its proof (2026-11-16)

Done, in `backends/lean/Aeneas/Deep/IR.lean` (the IR), `Compile.lean` (the compiler),
`CompileCorrect.lean` (the correctness theorem, i.e. the core of phase D, which turned out
to be within reach once the IR was fixed) and `Report.lean` (the coverage report).

**The IR.** A first-order imperative language in A-normal form, with the typing discipline
of the deep AST (descriptors over the closed world, store `Env N σ Γ`):

- `IExpr`: the pure, C-expressible expressions (variables, literals, the pure scalar and
  boolean operations, `c ? t : e`, tuples, constructors, projections, pure calls and
  globals, the loop-control values `continue_`/`break_`);
- `Stmt`: `pure e`, `ret e`, `fail`, the block-scoped bindings `letVal e p k` (pure
  expression), `letStmt s p k` (the value of a statement computing a value: an `if` or a
  `switch` whose branches return) and `bindStmt s p k` (the monadic bind of a fallible
  statement), the fallible primitives `call`, `global`, `scalarBinop`, `neg`, `assert`,
  `ite`, `switch` (one branch per variant, binding the fields), `loop p init body`.

Two decisions differ from section 2 of the plan, both in favour of a smaller verified
part:

1. **No mutable typed store, no flattening.** Variables are bound once (block scoping,
   as C locals), the only mutation a C realisation needs being the update of the loop
   state at `continue`; tuples stay tuple values (the printer maps them to structs).
   The IR is thus a *sublanguage* of the deep AST with an explicit separation of pure
   expressions and effectful statements, which is exactly the contract the printer
   needs, and the store invariant of the proof is trivial (same environments).
2. **The semantics reuses `Std.loop`.** `Stmt.exec : Stmt N F G σ Γ τ → Env N σ Γ →
   τ.denote σ` is structurally recursive; `loop` denotes `Std.loop` applied to the
   interpretation of the body. The correctness theorem for loops is then a congruence,
   not a fixpoint induction.
3. **No monomorphization in the verified part.** The compiler and its proof are generic
   in the type environment `σ` and the descriptors: the `call` nodes carry their
   descriptor arguments, and instantiation is the printer's concern (it prints one C
   function per reachable instance, with `Stmt.calls` listing the call sites).

**The compiler** (`Compile.compile : Expr N F G σ Γ τ → Except Unsupported (Stmt N F G σ Γ τ)`)
recognises the first-order fragment: `compileExpr` for the pure fragment, `compileStmt`
for the monadic spine (a `bind`/`let` of an `if` or a `match` computing a value becomes a
`bindStmt`/`letStmt`, `loop (lam …) init` becomes `loop`, `ok`/`fail` become returns).
Shallow leaves, lambdas, applications and the escape hatch are reported as `Unsupported`
with their reason (the tag of the leaf, so that the report lists the missing primitives).

**The theorem** `compile_correct : compile e = .ok s → s.exec env = e.denote env`, by
strong induction on `sizeOf e` (the structural recursion of theorems over the mutual
inductive families is not accepted by Lean, nor is well-founded recursion on them inferred
automatically; the generated `sizeOf_spec` lemmas plus `omega` make the size induction
cheap). The proof is one tactic macro per node: unfold the compiler, case on the results
of the recursive calls, unfold the two denotations, rewrite with the induction hypotheses.
No `sorry`, no axiom beyond the standard ones.

**Coverage.** `#deep_report` runs the compiler on every `f.deep` of the environment (by
`whnf` under the binders of `f.deep`) and lists the unsupported terms by reason. On the
test suite (the 15 deep-enabled modules, 460 deep terms, reported module by module since
the modules cannot be imported together; the hand-written terms of `Aeneas/Deep/Tests.lean`,
which every report also counts, are excluded from the numbers), 264 compile; the rest
are the closures (`lambda`, 37), the `Vec` indexing through the `Index`/`IndexMut` impls
(13), the escape hatches (`shallow`, 6), the calls through trait clauses and to trait
impls (about 17), and a tail of standard-library leaves (`cast_signed`, `wrapping_sub`,
`is_multiple_of`, `div_ceil`, `Result::is_ok`, the `u32::MAX`-style globals, literal
leaves). On curve25519-dalek (1,912 deep terms), 1,132 compile after the tuple-struct fix
below (1,007 before it), the blockers being the iterator adapters (`Range::next` 127,
`Rev::next` 40, `StepBy::next` 20, `into_iter`/`next` through trait clauses about 120,
`slice::Iter::next` 17), the `Array` literals (59), `Into::into` (32), the `subtle` trait
methods (`conditional_negate` 18, `ct_eq` 7), `Clone for [T; N]` (17), `as_mut_slice`
(17) and `@getTarget` (15).

The constructors of tuple structs (`FieldElement51(…)`, `RistrettoPoint(…)`, …, about 100
sites on dalek) were printed as leaves: fixed, they are tuples (a single field being the
field itself), the component types being the instantiated field types of the declaration
(a first version passed the struct type itself as the expected type of the array literals
inside, which broke 16 functions of dalek with an internal error of the shallow printer;
the final translation has no error and the 1,912 theorems build).

Tests: `Aeneas/Deep/Tests.lean` compiles the hand-written terms (all but the two returning
closures) and checks the interpreter against the shallow functions on sample inputs
(`Result` is an interaction tree, observed with `Result.reducesTo` under `native_decide`).

Found on the way: `Result` is `ITree RustEffect`, so results have no decidable equality
and are compared by observation; `native_decide` and `#eval` on the deep terms need
`public meta import` of the modules under the module system; the dalek trial moved from
the session scratchpad (purged by the system after three days) to `build/dalek-trial/`
(git-ignored), with the fork's Lean project now at `curve25519-dalek/lean` and its
`lakefile.lean` pointing `aeneas` at this checkout.

## 10. Phase C log

### C.1 Borrow idioms (2026-11-16)

Done, in the same modules as phase B (`IR.lean`, `Compile.lean`, `CompileCorrect.lean`),
with two new primitives in `Basic.lean` and a printer change.

**The data.** On curve25519-dalek the 194 applications of a variable are all applications
of backward functions: 59 come from the array and slice `index_mut` primitives
(`conditional_assign`/`conditional_swap` on the limbs, `square2`, `zeroize`, …), a few from
`Vec` indexing (a leaf until now), and about 40 from the crate's own `IndexMut` impls
(`Scalar52::index_mut`, `Scalar29::index_mut`, used by `from_bytes` and `from_bytes_wide`),
which return a closure built by the callee. The shape is always the one of section 3:
`bind (call indexMut [v, i]) (tuple [x, back]) …; let_ (app (var back) x') …`, the
container `v` being a variable, a projection or a global, the index a variable or a
literal; `back` is applied once per path (the branches of an `if` may each apply it).

**The lowering.** Rather than a separate rewriting pass on the deep terms (which would
have to remove `back` from the typing context, hence rename every variable), the IR gets a
statement and an expression:

- `Stmt.borrow m targs cargs inputs h₁ h₂ args p k`, for `m : MutIndex` (`array`, `slice`,
  `vec`), with the arguments and the proofs of the `call` node it replaces. Its semantics
  reads the element and binds, through the pattern `p`, the pair of the element and of the
  *setter at the index* as the backward function (`MutIndex.borrow`); the continuation `k`
  is typed in the same context as the deep term (the closure variable is still bound, to a
  closure of a known shape).
- `IExpr.appVar f a`: the application of a variable bound to a closure.

The compiler recognises `bind (call (prim indexMut) …) p k` (an inner `match` in the
`bind` arm, see below) and `app (var f) a`. A C realisation renders `borrow` as the read
`x = v[i]` and `appVar back x'` as the store `v[i] = x'` (in place when the old value of
`v` is dead, a copy otherwise: the printer's decision, section 7).

**The lemma.** `MutIndex.borrow_eq`: the borrow *is* the `index_mut` primitive. For arrays
and slices this is reflexivity, since `Array.index_mut_usize v i` is defined as
`do let x ← index_usize v i; ok (x, set v i)`; for `Vec` it is the monad laws
(`Vec.index_mut` goes through the slice). The correctness proof of the `bind` case
rewrites with it; the trusted part gains nothing beyond "`Array.set` is the store", which
it needed for an update primitive anyway.

**The closure discipline.** The correctness theorem does not care what a closure variable
is used for, but the printer does: `Stmt.borrowsOk` checks, with a list of marks for the
context, that the closures of a body are only the backward functions bound by a `borrow`,
and are only applied (`appVar`), and that the result of an `index_mut` primitive is
bound by a `borrow` (not by a plain `bindStmt`, not returned). `compile` runs it after
`compileStmt` and reports `closureVar`. The pattern of a `borrow` can be `(x, back)`,
`(_, back)` or `(x, _)` (`Pat.borrowMarks`).

**The printer.** `Vec::index` and `Vec::index_mut` at the `SliceIndex<usize, [T]>`
instance become the primitives `vecIndex`/`vecIndexMut` (modelled at that instance, so a
call at another instance, a range, stays a leaf: `prim_required_impl` and
`prim_impl_matches` in `ExtractDeep.ml`); their single type argument is the element type.
The second half of a borrow through a field, `let v := back x'; ok { self with slots := v }`,
was a leaf too (a partial structure update): it is now a constructor node whose other
fields are projections of the initial value, which is what the elaborator makes of the
update (so the `deep_eq` theorems are still reflexivity).

**Coverage** (same counting as phase B, the hand-written terms excluded). Test suite:
276 of the 460 deep terms compile (264 after phase B); the applications of backward
functions are all gone, the remaining failures of the borrow-heavy modules being the
closures returned by the crate's functions (`lambda`, 40), `core::mem::replace`, the
`usize::MAX` global and the standard-library leaves listed in section 9. On
curve25519-dalek, 1,144 of 1,912 (1,132 after phase B): no `application` is reported any
more; the 4 `closureVar` are `Scalar52::from_bytes`/`from_bytes_wide` and their `u32`
twins (the crate's `IndexMut` closures), the 4 `lambda` are the two `IndexMut` impls and
the two `square2` (a `for x in self.0.iter_mut()` loop whose state carries a closure).
The gain on dalek is small because the functions using borrows mostly use iterators as
well: the blockers are now the iterator adapters (`Range::next` 127, `Rev::next` 40,
`StepBy::next` 20, `into_iter`/`next` through trait clauses about 120, `slice::Iter::next`
17), the `Array` literals (59), `Into::into` (32), the `subtle` trait methods,
`Clone for [T; N]` (17), `as_mut_slice` (17) and `@getTarget` (15).

**What is left for closures.** The backward functions returned by the functions of the
crate (6 definitions on dalek, about 40 call sites; `list_nth_mut`-style functions and
the loops returning borrows in the test suite): either phase E, or a split of such a
function into a getter and a setter derived from its deep term (sound only if the body
is re-run for the setter, which the ITree semantics does not equate with the single run
unless the body is effect-free: not pursued).

The compiler reports the first failure of a body (the bound term before the
continuation), so that the reasons of the report stay comparable with phase B.

Found on the way: Lean's `split` on a `match` whose discriminant is a variable
generalises the variable (the proof scripts unify with the goal instead of naming it);
a first compiler arm whose pattern looks inside a sub-term (`bind (call (prim …) …) p k`
before `bind e p k`) leaves the generic arm without an unconditional equation lemma, so
`simp only [compileStmt]` can no longer unfold `compileStmt (bind e p k)` for an abstract
`e` (hence the inner `match e, compileStmt e with` in a single `bind` arm, which `split`
handles while keeping `e` abstract); the equation lemmas of the compiler are generated on
first use and now cost about ten seconds, charged to the heartbeats of the theorem which
triggers them (`maxHeartbeats 1000000` in `CompileCorrect.lean`); `Array.set` must be
qualified (`Std.Array.set`) in the IR, the root `Array.set` being Lean's.

## 11. Phase P log

### P.1 The trusted C printer (2026-11-16)

Done, in `backends/lean/Aeneas/Deep/CPrint.lean` (the printer, about 700 lines of plain
Lean, no proof) and `CDriver.lean` (the `#deep_c "file.c"` command), with the differential
test `Aeneas/Deep/Tests/C/` (`harness.c`, `run.sh`).

**Shape.** `printFunction name e` compiles the deep term `e` (`Compile.compile`) and prints
the IR as one C function; the driver runs it on every *closed* deep term of the
environment through the Lean interpreter (`evalExpr`: the IR value never leaves Lean,
the printer is an ordinary function on `Stmt`) and assembles the translation unit: a
prelude (the `<stdint.h>` scalars, `unit_t`, the error codes), the struct definitions
collected on demand in dependency order, the prototypes of every callee, the functions.
The tables of the crate (`FunNames`, `GlobalNames`) are parameters of the type of every
deep term but the printer never consults them (the call nodes carry their instantiated
signatures), and they may be noncomputable (dalek's shallow functions call axiomatized
externals): the driver casts the term to the type with computable stand-ins
(`unsafeCast`, sound because the constructors do not store the parameters) and evaluates
with `safety := .unsafe`. The C names of the functions, globals and types are the names
of the constructors of the generated enumerations (`deriving Repr`, now emitted by
`-deep`); the driver derives the name of a definition from its Lean name with the same
sanitisation, relative to the crate namespace (the namespace of the enumerations).
Printing is in continuation style: a statement receives a *destination* for its value
(`return` through the out-parameter, `return` of a pure value, an assignment, nothing),
pure expressions are rendered to C expressions and may emit statements first (the
application of a backward function, an `if` expression with effects, `Array::repeat`).

**What is trusted** (the list at the top of `CPrint.lean`, section 7 of this plan):

- *Types.* Scalars to the fixed-width C types (`usize` to `size_t`, 128-bit scalars to the
  `__int128` extension; 64-bit target assumed); `Unit` to a byte; tuples and the ADTs of
  the closed world to structs, with a tag and a union of field structs for the types with
  several variants; `Array α n` to a struct holding a C array, so that assignment copies;
  `Slice α` and `Vec α` to pointer-and-length *views*; `ControlFlow` to a tagged union.
  Type variables (the printer handles monomorphic terms; a call to a generic callee gets
  a mangled prototype), recursive types (a C realisation needs boxing), opaque types,
  strings and closures as values are refused and reported.
- *Calling convention.* `Result τ` functions return an error code and write their value
  to `*out` (none for `Result Unit`); pure functions return their value; globals are
  nullary functions; calls propagate the code.
- *Primitives.* `__builtin_*_overflow` for the checked arithmetic; explicit checks for
  the divisor (and `MIN / -1`; `MIN % -1` is `0` as in the model), the shift amount
  (computed in the unsigned type), the index; casts are C casts (two's complement);
  `update`/`push` copy an array and write a slice or a vector in place; vectors grow with
  `realloc` and are never freed.
- *Borrows.* A `borrow` reads the element after its bounds check and records the
  container and the index; `appVar back x'` copies the container (arrays) or writes in
  place (slices, vectors) and stores the element. For the views the old value is updated
  too: the realisation assumes, as Rust guarantees, that it is dead.

**Differential tests.** `run.sh` generates the C of the hand-written terms of
`Tests.lean`, compiles it with `harness.c` and runs the values the Lean tests check
(`reducesOn`/`execOn`): all 18 checks pass (checked arithmetic and its overflow, the
recursion of `i32_id`, the loop of `sum`, matches on `Option`, structures, the array and
vector borrows with their bounds checks). `run_loops.sh` does the same on the generated
`loops` crate (`harness_loops.c`, expected values from the Rust source): 10 checks pass
(the `while` loops with their tuple state, the sums with mutable and shared borrows, the
overflow of `sum 100000`, `clear` on a vector updated in place, the loops ignoring their
input borrow, `copy_carray` with its array literal constant provided by the harness since
array literals are still leaves).

**On the generated crates.** The test crates print and compile (`clang -std=c11 -Wall`,
no warning): `loops` 59 of its 77 closed deep terms (the others: closures, the recursive
`List` type, the array literal constant), `loops_rec` 54 of 70, `demo` 22 of 24,
`scalars` 27 of 60 (standard-library leaves), `hashmap` its 2 closed terms (the crate is
generic in `T`: monomorphization is the next step of this phase). On curve25519-dalek,
947 of the 1,599 closed deep terms are printed: 24,000 lines of C, 2,135 functions and
prototypes, compiled by `clang -std=c11 -Wall` without a warning (the field arithmetic,
`pow2k` and its loop, the reductions, the scalar arithmetic, the global constants as
nullary functions). Of the rest, 472 are outside the fragment of the compiler, 17 have no
compiled code (a shallow leaf of theirs refers to a noncomputable function), and 163 are
refused by the printer: 157 use an opaque type it cannot lay out, `subtle::Choice` in 75
of them (among which the `conditional_assign`/`conditional_swap` of the field elements
whose borrows phase C recovered) and the iterator adapters (`Rev<Range<usize>>`,
`StepBy`, `Iter`) in the others, and 6 carry a closure in a value.

**What the C does not yet do.** Monomorphization of the generic functions (the printer
prints the closed terms; a call to `list_nth [U32]` gets a prototype and no body); a
table of C definitions for the external types of a crate (`subtle::Choice` is a `u8`),
the first blocker on dalek; recursive types (boxing); the `-loops-to-rec` loops are
recursive C functions (no tail-call promise); no memory management for vectors; the
warnings `clang -Wall` emits on the output (`-Wparentheses-equality`, unused temporaries)
are cosmetic and disabled by the harness scripts.

### P.2 Instances, external types, the first iterator primitive (2026-11-16)

**Instances.** The printer prints a generic function once per instance reachable from
the closed functions (and from the `entries` the user asks for): the type and
const-generic parameters (`Ty.var i`, `CArg.var i`) are resolved through the environment
of the instance, every descriptor the printer reads going through `resolve`, and the
instance is named after its arguments (`pair_swap__u32`). The worklist lives in Lean
(`CPrint.program`): the driver packages every deep term of the crate as an `AnyDeep` (the
generic ones instantiated with `Nat` and `0`, an interpretation the printer never reads)
and the call sites of a printed body (`crateFun`, from the `call` nodes) feed the
worklist. Checked by the harness: the generic `pair_swap` of the hand-written tests is
printed at `u32` for its closed caller.

**External types.** `externals := [(name, definition)]` on `#deep_c` gives the C
definitions of the opaque types of the closed world; `subtle::Choice` is
`struct subtle_Choice { uint8_t f0; };`.

**`Range<usize>::next`.** The first iterator primitive, `rangeNextUsize` in `Basic.lean`
(the `Iterator` impl of `Range` at the `Step` instance of `usize`, recognised by the
printer of the deep terms through `prim_required_impl`, with no type argument), rendered
by the C printer as the comparison of the bounds and the step of the start (the model
only fails on a `Step` invariant, impossible for `usize`). The `for i in a..b` loops of
dalek go through it.

**Numbers.** Compiler coverage on dalek: 1,234 of the 1,912 deep terms (1,144 after
phase C: the 122 `for` loops over ranges and their callers); the test suite is unchanged
(276 of 460, its loops are `while` loops). C: the `loops` crate prints 59 instances of
its 109 deep terms (the generic ones are now counted, and printed when reached) and the
harness still passes; dalek prints 1,112 function instances (947 before): 31,000 lines of
C compiled by `clang -std=c11 -Wall` without a warning, including the
`conditional_assign`/`conditional_swap` family on `subtle::Choice`, the `for` loops of the
field and scalar arithmetic (`add_assign`, `Scalar52::add`, `from_bytes`,
`from_montgomery`) and the global constants. The remaining refusals of the printer are
the iterator adapter types (`Rev<Range<usize>>` 36, `StepBy` 20, `RangeInclusive` 4,
`Iter`/`IterMut` 6) and 6 closures in values; 27 deep terms have no compiled code (a
noncomputable leaf) and are skipped by the driver.

**Next.** The adapters `Rev` and `StepBy` over ranges (the next iterator primitives,
which also need their types in the closed world as structures over a `Range`), the
`Array` literals (59 terms), `Into::into` and the `subtle` trait methods.

### P.3 The iterator adapters over ranges (2026-11-17)

The next blockers of the plan: `Rev<Range<usize>>` and `StepBy<Range<usize>>`, used by
the `for i in (a..b).rev()` and `step_by(k)` loops of dalek.

**Types.** `Rev` and `StepBy` become builtin types of the library (`BuiltinTy.rev`,
`.stepBy`), with the variants of their Lean models (`Rev I = { iter }`,
`StepBy I = { iter, step_by }`) and the constructor, projector and eliminator instances,
so that the C printer lays them out as structs over the range. The printer of the deep
terms refers to them (`builtin_type_refs`) without building or inspecting their values
(the deep terms only pass them through the primitives), as for `Vec`.

**Primitives.** Four primitives at `usize` (`rangeRevUsize`, `revRangeNextUsize`,
`rangeStepByUsize`, `stepByRangeNextUsize`), whose implementations are the
standard-library models at the `Step` instance of `usize` (`Iterator::rev` is
`Rev { iter }`, `Rev::next` is `next_back`, which steps the end down; `step_by` fails on a
zero step; `StepBy::next` is `next` followed by `step - 1` skips, hence the start advanced
by the step and bounded by the end). The C printer renders them accordingly. The printer
of the deep terms recognises the calls through a table of specifications
(`prim_required_impl`): the trait instances the call must be at (`IteratorRange
StepUsize`, the `DoubleEndedIterator` of `Range`), and, for the primitives at a single
instance, the instantiated signature it must have (as deep descriptors), which also
fixes the imprecision of `Range::next` (a `Range<u8>` would have matched).

**Checked** by the hand-written harness: the five range primitives as shallow one-liners
(`range_next`, `range_rev`, `rev_next`, `range_step_by`, `step_by_next`, whose `deep_eq`
are reflexivity) against values computed from the models (`rev_next (0..3)` is
`some 2, 0..2`; `step_by (0..10) 3` yields `0, 3, 6, 9` then `none`; `step_by 0` panics).

**Numbers.** On dalek all 36 `rev` and `Rev::next` sites and all 20 `step_by` and
`StepBy::next` sites are primitives now; the compiler covers 1,270 of the 1,912 deep
terms (1,234 before), and the C printer prints 1,204 function instances (1,112 before):
34,000 lines, `clang -std=c11 -Wall` warning-free, with the reversed-range loops of the
Pippenger multiscalar multiplication among them. The `step_by` loops (the `mul_base` of
the basepoint tables) are still outside the fragment, blocked by `LookupTable::select`,
a function with trait clauses: on dalek the `StepBy` rendering is exercised by the
harness only. The printer refuses 26 terms for an
opaque type (`RangeInclusive` 4, the slice iterators `Iter`/`IterMut` 22) and 6 for a
closure in a value; the compiler's largest remaining blockers are the `Array` literals
(59), `Into::into` (32), `into_iter`/`next` through trait clauses (about 80: the
`for x in slice` loops), the `subtle` methods (`conditional_negate` 22), `Ord::cmp` on
`i8` (20), `LookupTable::select` (18, a function with trait clauses), `Clone for [T; N]`
and `as_mut_slice` (17 each) and `@getTarget` (15).

**Next.** The `Array` literals (a node of the deep AST, with its compilation and the
proof case) and the slice iterators (`Iter<T>::next`, `iter()`, `into_iter` on slices and
arrays: a primitive over a slice and an index would cover the `for x in slice` loops).

### A.5 Array literals (2026-11-17)

The `Array` literals (59 terms on dalek, the constant tables of the field arithmetic and
the lookup tables; `copy_carray` in the tests) were leaves. They are a node of the deep
AST now: `array τ n h es` with `es : Exprs … (List.replicate n τ)`, denoting
`Env.toArray h (es.denote env)`, that is `Array.make n [e₁, …, eₙ]` exactly as the shallow
printer prints them (the `deep_eq` theorems stay reflexivity; the length proof of
`Array.make` is hidden inside `Env.toArray`, so that the correctness proof rewrites the
elements without a dependent-proof motive). The IR has the same node, the compiler maps
one to the other, the proof case is the one of `tuple`, and the C printer prints a
compound literal of the array struct. The printer of the deep terms finds the literals as
structure updates of the builtin array type (`StructUpdate` with `TBuiltin TArray`, the
elements by field index), which is how the pure AST represents array aggregates, not
as constructor applications (a first attempt matched `AdtCons` and never fired).

**Numbers.** All 59 array literals of dalek are nodes (100 in the deep file, counting
the four target configurations): the compiler covers 1,329 of the 1,912 deep terms
(1,270 before) and the C printer prints 1,263 function instances (1,204 before): 40,000
lines, `clang -std=c11 -Wall` warning-free, the constant tables of the field and scalar
arithmetic among them (nullary functions returning the array compound literal). The test
suite gains the two `copy_carray` constants (278 of 460), the loops harness exercises the
printed constant and no longer needs its stub, and the hand-written `arr_lit` is checked
by the harness.

**Next.** The slice iterators (`Iter<T>::next`, `iter()`, `into_iter` on slices and
arrays: about 25 concrete sites, plus the loops through trait clauses they would unblock),
`Into::into` (32), the `subtle` methods, `Clone for [T; N]` and `as_mut_slice` (17 each).

### A.6 The slice iterators (2026-11-17)

`slice::Iter<T>` becomes a builtin type of the library (`BuiltinTy.sliceIter`, the slice
and an index; the index of the Lean model is a `Nat`, described as a `usize` for the C
layout, which nothing in the verified part depends on since the deep terms never build or
inspect an iterator), with four primitives generic in the element type: `[T]::iter`,
`into_iter` on `&[T]` and on `&[T; N]`, and `Iter<T>::next` (the element at the index if
it is below the length, the index stepped). The C printer renders the iterator as the
slice view and the index; the printer of the deep terms maps the four standard-library
functions through `prim_table` (no trait instance to check). Checked by the hand-written
harness (`slice_iter`, `slice_into_iter`, `array_into_iter`, `slice_iter_next`: the
elements in order, then `none`). The test crates do not use slice iterators.

**Numbers.** On dalek the 30 slice-iterator sites (5 `iter`, 8 `into_iter`, 17 `next`)
are primitives; the compiler covers 1,341 of the 1,912 deep terms (1,329 before) and the
C printer prints 1,291 function instances (1,263 before): 41,000 lines,
`clang -std=c11 -Wall` warning-free. The printer refuses 16 terms (opaque
`RangeInclusive`, `IterMut`, the Rust `Result` and `CtOption` types, and 6 closures in
values). The compiler's remaining blockers are the calls through trait clauses
(`into_iter`/`next` of generic iterators, about 80, in functions outside the closed
world), `Into::into` (32), the `subtle` methods (`conditional_negate` 22), `Ord::cmp`
on `i8` (20), `LookupTable::select` (18), `as_mut_slice` and `Clone for [T; N]` (17 each)
and `@getTarget` (15).

**Next.** `Into::into` at concrete instances (`u64::from(u32)`-style conversions), the
Rust `Result` as a builtin type with variants (for the printer), `as_mut_slice` and
`Clone for [T; N]` as primitives (an identity and a copy), and the `subtle` methods on
`u64` as primitives of their models.

## 12. A complete example: modular inversion (2026-11-17)

`tests/src/modinv.rs` (the test crate `Modinv`) computes `a⁻¹ = a^(P-2) mod P` for the
prime `P` below `2^32` by square-and-multiply; everything is first-order checked
arithmetic, a `while` loop and calls. `tests/lean/Modinv/Example.lean` walks through the
pipeline: the generated deep terms and their reflexive `deep_eq` theorems, `#deep_report`
(the five functions and the constant compile), the end-to-end theorems
`inv_mod_ir_correct`/`pow_mod_ir_correct` (`compile_correct` composed with `deep_eq`: the
IR program computes the translated function), and the sample values by `native_decide`
(`3⁻¹ = 1431655764`, on the translated function and on the IR interpreter).
`Modinv/GenC.lean` prints the C (six functions, 130 lines: the constant as a nullary
function, `mul_mod` with its overflow and division checks, the loop body returning the
`ControlFlow` union, the loop threading its tuple state), and `Modinv/C/run.sh` compiles
it with `Modinv/C/harness.c` and checks the same values, the inverses of `2` and
`123456789`, `pow_mod 2 10`, `inv_mod 0`, and the overflow of `mul_mod` on operands above
`P`, which the C reports as the model does.

