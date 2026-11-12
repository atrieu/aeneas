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
