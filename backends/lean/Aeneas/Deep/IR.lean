module
public import Aeneas.Deep.Basic
@[expose] public section

/-! # The C-shaped intermediate representation

The target of the compiler of the deep terms (`Aeneas.Deep.Compile`), and the source of the
trusted C printer. It is a first-order imperative language in A-normal form:

- **expressions** (`IExpr`) are pure and C-expressible: variables, literals, the pure scalar
  and boolean operations, tuples, the constructors and projections of the ADTs of the closed
  world, pure calls (functions whose result is not in `Result`), the loop-control values;
- **statements** (`Stmt`) sequence the effects: fallible calls and checked scalar operations,
  assertions, failures, returns, `if`/`switch`, `loop`, block-scoped bindings
  (`letVal` of a pure expression, `letStmt` of the value computed by a statement, `bindStmt`
  of the result of a fallible statement), and the mutable borrow of an element of an array,
  a slice or a vector (`borrow`, see `MutIndex`).

The IR keeps the typing discipline of the deep AST: terms are indexed by descriptors over the
closed world of the crate, and the store is the same environment `Env N σ Γ`. Variables are
bound once (block scoping, as C locals); the only mutation a C realisation needs is the
update of the loop state at `continue`. The semantics is a definitional interpreter into the
same `Result` monad as the translation (`Stmt.exec`); loops reuse `Std.loop`, so that the
correctness of the compiler is an equation between the interpreter and the denotation of the
deep term, without a fixpoint induction of its own.

What the C printer decides (and is trusted for) is listed in `PLAN-compiler.md`. -/

namespace Aeneas.Deep.IR

open Aeneas.Std

/-! ## Mutable borrows of an element

`index_mut` on an array, a slice or a vector returns the element and a backward function
which, applied to the new value of the element, gives the updated container (this is how
the translation models `&mut v[i]`). In the standard-library models the backward function
*is* the functional update at the index: `index_mut_usize v i` is
`do let x ← index_usize v i; ok (x, set v i)` (`MutIndex.borrow_eq`). The `borrow`
statement of the IR makes this explicit: its semantics reads the element and binds the pair
of the element and the setter closure, and the application of the closure (`IExpr.appVar`)
is, for a C realisation, the store `v[i] = x'`. -/

/-- The primitives returning a mutable borrow of an element -/
inductive MutIndex where
  | array
  | slice
  | vec
  deriving DecidableEq, Repr

/-- The `index_mut` primitive -/
@[reducible] def MutIndex.prim : MutIndex → Prim
  | .array => .arrayIndexMut
  | .slice => .sliceIndexMut
  | .vec => .vecIndexMut

/-- The semantics of a borrow: the element, paired with the setter at the index as the
backward function -/
def MutIndex.borrow {N : Type} [TypeNames N] : (m : MutIndex) → (ρ : TyEnv) →
    HList (Tys.denote ρ (Prim.def (N := N) m.prim).sig.inputs) →
    Ty.denote ρ (Prim.def (N := N) m.prim).sig.output
  | .array, _, .cons v (.cons i .nil) =>
    Std.bind (Std.Array.index_usize v i) (fun x => Result.ok (x, Std.Array.set v i))
  | .slice, _, .cons v (.cons i .nil) =>
    Std.bind (Slice.index_usize v i) (fun x => Result.ok (x, Slice.set v i))
  | .vec, _, .cons v (.cons i .nil) =>
    Std.bind (alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice _) v i)
      (fun x => Result.ok (x, alloc.vec.Vec.set v i))

/-- The borrow is the `index_mut` primitive: one lemma per primitive, relating the model
of `index_mut` and its backward function to the update at the index -/
theorem MutIndex.borrow_eq {N : Type} [TypeNames N] (m : MutIndex) (ρ : TyEnv)
    (hl : HList (Tys.denote ρ (Prim.def (N := N) m.prim).sig.inputs)) :
    m.borrow ρ hl = Fn.apply ((Prim.def (N := N) m.prim).impl ρ) hl := by
  cases m <;> (cases hl; rename_i v hl; cases hl; rename_i i hl; cases hl)
  · rfl
  · rfl
  · change _ = alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice _) v i
    simp only [MutIndex.borrow, alloc.vec.Vec.index_mut, alloc.vec.Vec.index,
      core.slice.index.Usize.index_mut, core.slice.index.Usize.index, Slice.index_mut_usize,
      Bind.bind, Pure.pure, Std.bind_assoc, Std.bind_ok]
    rfl

/-- Is this function an `index_mut` primitive (whose result holds a closure)? -/
def _root_.Aeneas.Deep.FunRef.isIndexMut {F : Type} : FunRef F → Bool
  | .prim .arrayIndexMut | .prim .sliceIndexMut | .prim .vecIndexMut => true
  | _ => false

mutual
  /-- Pure, C-expressible expressions -/
  inductive IExpr (N F G : Type) [TypeNames N] [FunNames F N] [GlobalNames G N] (σ : TyEnv) :
      List (Ty N) → Ty N → Type 1 where
    | var {Γ : List (Ty N)} {τ : Ty N} (v : Var N Γ τ) : IExpr N F G σ Γ τ
    /-- The application of a variable bound to a closure: the backward function of a
    `borrow`, applied to the new value of the element -/
    | appVar {Γ : List (Ty N)} {α β : Ty N} (f : Var N Γ (.arrow α β)) (a : IExpr N F G σ Γ α) :
        IExpr N F G σ Γ β
    | uscalarLit {Γ : List (Ty N)} (ty : UScalarTy) (n : Nat) (h : n ≤ UScalar.cMax ty) :
        IExpr N F G σ Γ (.scalar (.u ty))
    | iscalarLit {Γ : List (Ty N)} (ty : IScalarTy) (n : Int)
        (h : IScalar.cMin ty ≤ n ∧ n ≤ IScalar.cMax ty) : IExpr N F G σ Γ (.scalar (.i ty))
    | boolLit {Γ : List (Ty N)} (b : Bool) : IExpr N F G σ Γ .bool
    | unitLit {Γ : List (Ty N)} : IExpr N F G σ Γ .unit
    /-- The bitwise operations `&&& ||| ^^^` -/
    | scalarBitop {Γ : List (Ty N)} (op : ScalarBitop) (ty : ScalarTy)
        (a b : IExpr N F G σ Γ (.scalar ty)) : IExpr N F G σ Γ (.scalar ty)
    | bitNot {Γ : List (Ty N)} (ty : ScalarTy) (a : IExpr N F G σ Γ (.scalar ty)) :
        IExpr N F G σ Γ (.scalar ty)
    | cast {Γ : List (Ty N)} (src tgt : ScalarTy) (a : IExpr N F G σ Γ (.scalar src)) :
        IExpr N F G σ Γ (.scalar tgt)
    | castFromBool {Γ : List (Ty N)} (tgt : ScalarTy) (a : IExpr N F G σ Γ .bool) :
        IExpr N F G σ Γ (.scalar tgt)
    | boolBinop {Γ : List (Ty N)} (op : BoolBinop) (a b : IExpr N F G σ Γ .bool) :
        IExpr N F G σ Γ .bool
    | boolNot {Γ : List (Ty N)} (a : IExpr N F G σ Γ .bool) : IExpr N F G σ Γ .bool
    /-- `a != b`. The instance is the one of the deep term (the printer trusts it to be the
    structural equality of scalars and booleans). -/
    | bne {Γ : List (Ty N)} {α : Ty N} [inst : BEq (α.denote σ)] (a b : IExpr N F G σ Γ α) :
        IExpr N F G σ Γ .bool
    | decide {Γ : List (Ty N)} (c : ICond N F G σ Γ) : IExpr N F G σ Γ .bool
    /-- A conditional expression (`c ? t : e`) -/
    | ite {Γ : List (Ty N)} {τ : Ty N} (c : ICond N F G σ Γ) (t e : IExpr N F G σ Γ τ) :
        IExpr N F G σ Γ τ
    | tuple {Γ : List (Ty N)} {tys : List (Ty N)} (es : IExprs N F G σ Γ tys) :
        IExpr N F G σ Γ (.tuple tys)
    | ctor {Γ : List (Ty N)} (T : TypeRef N) (v : Nat) [inst : CtorFn N T v]
        (targs : List (Ty N)) (cargs : List CArg) (fields : List (Ty N))
        (h : Tys.denote σ fields = TypeNames.fieldTys T v (Ty.argEnv σ targs cargs))
        (args : IExprs N F G σ Γ fields) : IExpr N F G σ Γ (.adt T targs cargs)
    | proj {Γ : List (Ty N)} (T : TypeRef N) (f : Nat) [inst : ProjFn N T f]
        (targs : List (Ty N)) (cargs : List CArg) (τ : Ty N)
        (h : (TypeNames.fieldTys T 0 (Ty.argEnv σ targs cargs)).getD f Unit = τ.denote σ)
        (e : IExpr N F G σ Γ (.adt T targs cargs)) : IExpr N F G σ Γ τ
    /-- A global whose type is not in `Result` -/
    | global {Γ : List (Ty N)} (g : G) (targs : List (Ty N)) (cargs : List CArg) (τ : Ty N)
        (h : Ty.denote (Ty.argEnv σ targs cargs) (GlobalNames.ty (N := N) g) = τ.denote σ) :
        IExpr N F G σ Γ τ
    /-- A call to a function whose result is not in `Result` (a pure function) -/
    | call {Γ : List (Ty N)} (f : FunRef F) (targs : List (Ty N)) (cargs : List CArg)
        (inputs : List (Ty N)) (output : Ty N)
        (h₁ : Tys.denote σ inputs = Tys.denote (Ty.argEnv σ targs cargs) (FunRef.sig (N := N) f).inputs)
        (h₂ : Ty.denote (Ty.argEnv σ targs cargs) (FunRef.sig (N := N) f).output = output.denote σ)
        (args : IExprs N F G σ Γ inputs) : IExpr N F G σ Γ output
    /-- `ControlFlow.cont e`: in a loop body, `continue` with the new state -/
    | continue_ {Γ : List (Ty N)} (α β : Ty N) (e : IExpr N F G σ Γ α) :
        IExpr N F G σ Γ (.controlFlow α β)
    /-- `ControlFlow.done e`: in a loop body, `break` with the result -/
    | break_ {Γ : List (Ty N)} (α β : Ty N) (e : IExpr N F G σ Γ β) :
        IExpr N F G σ Γ (.controlFlow α β)

  inductive IExprs (N F G : Type) [TypeNames N] [FunNames F N] [GlobalNames G N] (σ : TyEnv) :
      List (Ty N) → List (Ty N) → Type 1 where
    | nil {Γ : List (Ty N)} : IExprs N F G σ Γ []
    | cons {Γ : List (Ty N)} {τ : Ty N} {tys : List (Ty N)}
        (e : IExpr N F G σ Γ τ) (es : IExprs N F G σ Γ tys) : IExprs N F G σ Γ (τ :: tys)

  /-- Conditions (the propositions of `if` and `assert`, with their decidability) -/
  inductive ICond (N F G : Type) [TypeNames N] [FunNames F N] [GlobalNames G N] (σ : TyEnv) :
      List (Ty N) → Type 1 where
    | bool {Γ : List (Ty N)} (b : IExpr N F G σ Γ .bool) : ICond N F G σ Γ
    | not {Γ : List (Ty N)} (c : ICond N F G σ Γ) : ICond N F G σ Γ
    | eq {Γ : List (Ty N)} {α : Ty N} [inst : DecidableEq (α.denote σ)]
        (a b : IExpr N F G σ Γ α) : ICond N F G σ Γ
    | lt {Γ : List (Ty N)} {α : Ty N} [ord : LT (α.denote σ)]
        [inst : DecidableRel (· < · : α.denote σ → α.denote σ → Prop)]
        (a b : IExpr N F G σ Γ α) : ICond N F G σ Γ
    | le {Γ : List (Ty N)} {α : Ty N} [ord : LE (α.denote σ)]
        [inst : DecidableRel (· ≤ · : α.denote σ → α.denote σ → Prop)]
        (a b : IExpr N F G σ Γ α) : ICond N F G σ Γ
    | gt {Γ : List (Ty N)} {α : Ty N} [ord : LT (α.denote σ)]
        [inst : DecidableRel (· < · : α.denote σ → α.denote σ → Prop)]
        (a b : IExpr N F G σ Γ α) : ICond N F G σ Γ
    | ge {Γ : List (Ty N)} {α : Ty N} [ord : LE (α.denote σ)]
        [inst : DecidableRel (· ≤ · : α.denote σ → α.denote σ → Prop)]
        (a b : IExpr N F G σ Γ α) : ICond N F G σ Γ
end

mutual
  /-- Statements. `Stmt N F G σ Γ τ` computes a value of type `τ` (a `Result` for the
  fallible ones) in the context `Γ`. -/
  inductive Stmt (N F G : Type) [TypeNames N] [FunNames F N] [GlobalNames G N] (σ : TyEnv) :
      List (Ty N) → Ty N → Type 1 where
    /-- The value of a pure expression -/
    | pure {Γ : List (Ty N)} {τ : Ty N} (e : IExpr N F G σ Γ τ) : Stmt N F G σ Γ τ
    /-- `return e` -/
    | ret {Γ : List (Ty N)} {τ : Ty N} (e : IExpr N F G σ Γ τ) : Stmt N F G σ Γ (.result τ)
    | fail {Γ : List (Ty N)} (τ : Ty N) (err : Error) : Stmt N F G σ Γ (.result τ)
    /-- `let p := e; k` -/
    | letVal {Γ : List (Ty N)} {α τ : Ty N} {Δ : List (Ty N)}
        (e : IExpr N F G σ Γ α) (p : Pat N α Δ) (k : Stmt N F G σ (Δ ++ Γ) τ) :
        Stmt N F G σ Γ τ
    /-- `let p := s; k`, where `s` is a statement computing a value (an `if` or a
    `switch` whose branches return) -/
    | letStmt {Γ : List (Ty N)} {α τ : Ty N} {Δ : List (Ty N)}
        (s : Stmt N F G σ Γ α) (p : Pat N α Δ) (k : Stmt N F G σ (Δ ++ Γ) τ) :
        Stmt N F G σ Γ τ
    /-- `let p ← s; k`: the monadic bind of a fallible statement (a call, a checked
    operation, an `if`, …); the failure of `s` is the failure of the whole -/
    | bindStmt {Γ : List (Ty N)} {α τ : Ty N} {Δ : List (Ty N)}
        (s : Stmt N F G σ Γ (.result α)) (p : Pat N α Δ)
        (k : Stmt N F G σ (Δ ++ Γ) (.result τ)) : Stmt N F G σ Γ (.result τ)
    /-- A fallible call -/
    | call {Γ : List (Ty N)} (f : FunRef F) (targs : List (Ty N)) (cargs : List CArg)
        (inputs : List (Ty N)) (τ : Ty N)
        (h₁ : Tys.denote σ inputs = Tys.denote (Ty.argEnv σ targs cargs) (FunRef.sig (N := N) f).inputs)
        (h₂ : Ty.denote (Ty.argEnv σ targs cargs) (FunRef.sig (N := N) f).output =
          Ty.denote σ (.result τ))
        (args : IExprs N F G σ Γ inputs) : Stmt N F G σ Γ (.result τ)
    /-- A global whose type is in `Result` -/
    | global {Γ : List (Ty N)} (g : G) (targs : List (Ty N)) (cargs : List CArg) (τ : Ty N)
        (h : Ty.denote (Ty.argEnv σ targs cargs) (GlobalNames.ty (N := N) g) =
          Ty.denote σ (.result τ)) :
        Stmt N F G σ Γ (.result τ)
    /-- A checked scalar operation (`+ - * / % <<< >>>`) -/
    | scalarBinop {Γ : List (Ty N)} (op : ScalarBinop) (ty : ScalarTy)
        (a : IExpr N F G σ Γ (.scalar ty)) (b : IExpr N F G σ Γ (.scalar (op.rhsTy ty))) :
        Stmt N F G σ Γ (.result (.scalar ty))
    /-- The checked negation -/
    | neg {Γ : List (Ty N)} (ty : IScalarTy) (a : IExpr N F G σ Γ (.scalar (.i ty))) :
        Stmt N F G σ Γ (.result (.scalar (.i ty)))
    | assert {Γ : List (Ty N)} (c : ICond N F G σ Γ) : Stmt N F G σ Γ (.result .unit)
    | ite {Γ : List (Ty N)} {τ : Ty N} (c : ICond N F G σ Γ) (t e : Stmt N F G σ Γ τ) :
        Stmt N F G σ Γ τ
    | switch {Γ : List (Ty N)} {τ : Ty N} (T : TypeRef N) [inst : ElimFn N T]
        (targs : List (Ty N)) (cargs : List CArg) (shape : List (List (Ty N)))
        (h : shape.map (Tys.denote σ) =
          (TypeRef.variants T).map (Tys.denote (Ty.argEnv σ targs cargs)))
        (scrut : IExpr N F G σ Γ (.adt T targs cargs)) (brs : SBranches N F G σ Γ shape τ) :
        Stmt N F G σ Γ τ
    /-- `loop`: the state `p` is initialised with `init`; the body returns `continue_ x`
    to iterate with the new state `x`, or `break_ y` to exit with the result `y` -/
    | loop {Γ : List (Ty N)} {α β : Ty N} {Δ : List (Ty N)}
        (p : Pat N α Δ) (init : IExpr N F G σ Γ α)
        (body : Stmt N F G σ (Δ ++ Γ) (.result (.controlFlow α β))) :
        Stmt N F G σ Γ (.result β)
    /-- `let p ← index_mut v i; k` for the array, slice and vector primitives: `p` binds the
    element and its backward function, the setter at the index (`MutIndex.borrow`). A C
    realisation reads `v[i]` and renders the application of the backward function
    (`IExpr.appVar`) as the store `v[i] = x'`. The arguments and the proofs are those of the
    `call` node. -/
    | borrow {Γ : List (Ty N)} {Δ : List (Ty N)} {α τ : Ty N} (m : MutIndex)
        (targs : List (Ty N)) (cargs : List CArg) (inputs : List (Ty N))
        (h₁ : Tys.denote σ inputs =
          Tys.denote (Ty.argEnv σ targs cargs) (Prim.def (N := N) m.prim).sig.inputs)
        (h₂ : Ty.denote (Ty.argEnv σ targs cargs) (Prim.def (N := N) m.prim).sig.output =
          Ty.denote σ (.result α))
        (args : IExprs N F G σ Γ inputs) (p : Pat N α Δ)
        (k : Stmt N F G σ (Δ ++ Γ) (.result τ)) : Stmt N F G σ Γ (.result τ)

  inductive SBranches (N F G : Type) [TypeNames N] [FunNames F N] [GlobalNames G N]
      (σ : TyEnv) : List (Ty N) → List (List (Ty N)) → Ty N → Type 1 where
    | nil {Γ : List (Ty N)} {τ : Ty N} : SBranches N F G σ Γ [] τ
    | cons {Γ : List (Ty N)} {Δ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N}
        (b : Stmt N F G σ (Δ ++ Γ) τ) (bs : SBranches N F G σ Γ shape τ) :
        SBranches N F G σ Γ (Δ :: shape) τ
end

/-! ## Semantics -/

mutual
  def IExpr.denote {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv} :
      {Γ : List (Ty N)} → {τ : Ty N} → IExpr N F G σ Γ τ → Env N σ Γ → τ.denote σ
    | _, _, .var v, env => v.get env
    | _, _, .appVar f a, env => (f.get env) (a.denote env)
    | _, _, .uscalarLit _ n h, _ => UScalar.ofNat n h
    | _, _, .iscalarLit _ n h, _ => IScalar.ofInt n h
    | _, _, .boolLit b, _ => b
    | _, _, .unitLit, _ => ()
    | _, _, .scalarBitop op ty a b, env => op.denote ty (a.denote env) (b.denote env)
    | _, _, .bitNot ty a, env => ty.bitNot (a.denote env)
    | _, _, .cast src tgt a, env => ScalarTy.cast src tgt (a.denote env)
    | _, _, .castFromBool tgt a, env => ScalarTy.castFromBool tgt (a.denote env)
    | _, _, .boolBinop op a b, env => op.denote (a.denote env) (b.denote env)
    | _, _, .boolNot a, env => (¬ (a.denote env) : Bool)
    | _, _, .bne (inst := inst) a b, env => @bne _ inst (a.denote env) (b.denote env)
    | _, _, .decide c, env => @Decidable.decide (c.denote env).prop (c.denote env).dec
    | _, _, .ite c t e, env =>
      @ite _ (c.denote env).prop (c.denote env).dec (t.denote env) (e.denote env)
    | _, _, .tuple es, env => (es.denote env).toTuple
    | _, _, .ctor _ _ (inst := inst) targs cargs _ h args, env =>
      Fn.apply (inst.ctor (Ty.argEnv σ targs cargs)) (h ▸ (args.denote env).toHList)
    | _, _, .proj _ _ (inst := inst) targs cargs _ h e, env =>
      h ▸ inst.proj (Ty.argEnv σ targs cargs) (e.denote env)
    | _, _, .global g targs cargs _ h, _ => h ▸ GlobalNames.impl (N := N) g (Ty.argEnv σ targs cargs)
    | _, _, .call f targs cargs _ _ h₁ h₂ args, env =>
      h₂ ▸ Fn.apply (FunRef.impl (N := N) f (Ty.argEnv σ targs cargs)) (h₁ ▸ (args.denote env).toHList)
    | _, _, .continue_ _ _ e, env => ControlFlow.cont (e.denote env)
    | _, _, .break_ _ _ e, env => ControlFlow.done (e.denote env)

  def IExprs.denote {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv} :
      {Γ : List (Ty N)} → {tys : List (Ty N)} → IExprs N F G σ Γ tys → Env N σ Γ → Env N σ tys
    | _, _, .nil, _ => .nil
    | _, _, .cons e es, env => .cons (e.denote env) (es.denote env)

  def ICond.denote {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv} :
      {Γ : List (Ty N)} → ICond N F G σ Γ → Env N σ Γ → DecProp
    | _, .bool b, env => ⟨b.denote env = true, inferInstance⟩
    | _, .not c, env => ⟨¬ (c.denote env).prop, @instDecidableNot _ (c.denote env).dec⟩
    | _, .eq (inst := inst) a b, env => ⟨a.denote env = b.denote env, inst _ _⟩
    | _, .lt (ord := ord) (inst := inst) a b, env =>
      ⟨@LT.lt _ ord (a.denote env) (b.denote env), inst _ _⟩
    | _, .le (ord := ord) (inst := inst) a b, env =>
      ⟨@LE.le _ ord (a.denote env) (b.denote env), inst _ _⟩
    | _, .gt (ord := ord) (inst := inst) a b, env =>
      ⟨@GT.gt _ ord (a.denote env) (b.denote env), inst _ _⟩
    | _, .ge (ord := ord) (inst := inst) a b, env =>
      ⟨@GE.ge _ ord (a.denote env) (b.denote env), inst _ _⟩
end

mutual
  /-- The interpreter: the value computed by a statement. For the fallible statements this
  is a `Result`. -/
  def Stmt.exec {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv} :
      {Γ : List (Ty N)} → {τ : Ty N} → Stmt N F G σ Γ τ → Env N σ Γ → τ.denote σ
    | _, _, .pure e, env => e.denote env
    | _, _, .ret e, env => Result.ok (e.denote env)
    | _, _, .fail _ err, _ => Result.fail err
    | _, _, .letVal e p k, env =>
      let x := e.denote env
      k.exec ((p.bindEnv x).append env)
    | _, _, .letStmt s p k, env =>
      let x := s.exec env
      k.exec ((p.bindEnv x).append env)
    | _, _, .bindStmt s p k, env =>
      Std.bind (s.exec env) (fun x => k.exec ((p.bindEnv x).append env))
    | _, _, .call f targs cargs _ _ h₁ h₂ args, env =>
      h₂ ▸ Fn.apply (FunRef.impl (N := N) f (Ty.argEnv σ targs cargs)) (h₁ ▸ (args.denote env).toHList)
    | _, _, .global g targs cargs _ h, _ => h ▸ GlobalNames.impl (N := N) g (Ty.argEnv σ targs cargs)
    | _, _, .scalarBinop op ty a b, env => op.denote ty (a.denote env) (b.denote env)
    | _, _, .neg _ a, env => -. (a.denote env)
    | _, _, .assert c, env => @Std.massert (c.denote env).prop (c.denote env).dec
    | _, _, .ite c t e, env =>
      @ite _ (c.denote env).prop (c.denote env).dec (t.exec env) (e.exec env)
    | _, _, .switch _ (inst := inst) targs cargs _ h s brs, env =>
      inst.elim (Ty.argEnv σ targs cargs) (s.denote env) (h ▸ brs.exec env)
    | _, _, .loop p init body, env =>
      Std.loop (fun x => body.exec ((p.bindEnv x).append env)) (init.denote env)
    | _, _, .borrow (α := α) m targs cargs _ h₁ h₂ args p k, env =>
      Std.bind
        (h₂ ▸ m.borrow (Ty.argEnv σ targs cargs) (h₁ ▸ (args.denote env).toHList) :
          Ty.denote σ (.result α))
        (fun x => k.exec ((p.bindEnv x).append env))

  def SBranches.exec {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv} :
      {Γ : List (Ty N)} → {shape : List (List (Ty N))} → {τ : Ty N} →
      SBranches N F G σ Γ shape τ → Env N σ Γ → Alts (shape.map (Tys.denote σ)) (τ.denote σ)
    | _, _, _, .nil, _ => ()
    | _, _, _, .cons (Δ := Δ) b bs, env =>
      (HList.curry (Tys.denote σ Δ) (fun fields => b.exec ((Env.ofHList Δ fields).append env)),
       bs.exec env)
end

/-! ## The functions called by a program

The instances to print: the callees with their type and const-generic arguments (as
descriptors over the parameters of the enclosing function). -/

/-- A reference to a function instance -/
structure CallSite (N F : Type) where
  f : FunRef F
  targs : List (Ty N)
  cargs : List CArg

mutual
  def IExpr.calls {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {τ : Ty N} : IExpr N F G σ Γ τ → List (CallSite N F)
    | .appVar _ a => a.calls
    | .scalarBitop _ _ a b => a.calls ++ b.calls
    | .bitNot _ a => a.calls
    | .cast _ _ a => a.calls
    | .castFromBool _ a => a.calls
    | .boolBinop _ a b => a.calls ++ b.calls
    | .boolNot a => a.calls
    | .bne (inst := _) a b => a.calls ++ b.calls
    | .decide c => c.calls
    | .ite c t e => c.calls ++ t.calls ++ e.calls
    | .tuple es => es.calls
    | .ctor _ _ (inst := _) _ _ _ _ args => args.calls
    | .proj _ _ (inst := _) _ _ _ _ e => e.calls
    | .call f targs cargs _ _ _ _ args => ⟨f, targs, cargs⟩ :: args.calls
    | .continue_ _ _ e => e.calls
    | .break_ _ _ e => e.calls
    | _ => []
  termination_by structural e => e
  def IExprs.calls {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {tys : List (Ty N)} : IExprs N F G σ Γ tys → List (CallSite N F)
    | .nil => []
    | .cons e es => e.calls ++ es.calls
  termination_by structural es => es
  def ICond.calls {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} : ICond N F G σ Γ → List (CallSite N F)
    | .bool b => b.calls
    | .not c => c.calls
    | .eq (inst := _) a b => a.calls ++ b.calls
    | .lt (ord := _) (inst := _) a b => a.calls ++ b.calls
    | .le (ord := _) (inst := _) a b => a.calls ++ b.calls
    | .gt (ord := _) (inst := _) a b => a.calls ++ b.calls
    | .ge (ord := _) (inst := _) a b => a.calls ++ b.calls
  termination_by structural c => c
end

mutual
  def Stmt.calls {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {τ : Ty N} : Stmt N F G σ Γ τ → List (CallSite N F)
    | .pure e => e.calls
    | .ret e => e.calls
    | .fail _ _ => []
    | .letVal e _ k => e.calls ++ k.calls
    | .letStmt s _ k => s.calls ++ k.calls
    | .bindStmt s _ k => s.calls ++ k.calls
    | .call f targs cargs _ _ _ _ args => ⟨f, targs, cargs⟩ :: args.calls
    | .global _ _ _ _ _ => []
    | .scalarBinop _ _ a b => a.calls ++ b.calls
    | .neg _ a => a.calls
    | .assert c => c.calls
    | .ite c t e => c.calls ++ t.calls ++ e.calls
    | .switch _ (inst := _) _ _ _ _ s brs => s.calls ++ brs.calls
    | .loop _ init body => init.calls ++ body.calls
    | .borrow m targs cargs _ _ _ args _ k => ⟨.prim m.prim, targs, cargs⟩ :: args.calls ++ k.calls
  termination_by structural s => s
  def SBranches.calls {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N} :
      SBranches N F G σ Γ shape τ → List (CallSite N F)
    | .nil => []
    | .cons b bs => b.calls ++ bs.calls
  termination_by structural bs => bs
end

/-! ## The discipline of the closures

The only closures of a program are the backward functions bound by `borrow`, and their only
use is their application (`appVar`) to the new value of the element: `borrowsOk` checks it
(the printer renders a `borrow` as a read and the applications as stores, and could not
print a closure value). The check is context-dependent and is not needed for the
correctness of the compiler: the compiler runs it after compiling a body, and reports the
bodies which fail it. -/

/-- The marks of the variables bound by the pattern of a `borrow`: the second component of
the pair is the backward function (a variable bound to the whole pair, or any other pattern,
is marked as a closure too) -/
def _root_.Aeneas.Deep.Pat.borrowMarks {N : Type} :
    {α : Ty N} → {Δ : List (Ty N)} → Pat N α Δ → List Bool
  | _, _, .tuple (.cons (Δ₁ := Δ₁) _ (.cons (Δ₁ := Δ₂) _ .nil)) =>
    List.replicate Δ₁.length false ++ List.replicate Δ₂.length true
  | _, Δ, _ => List.replicate Δ.length true

mutual
  /-- Are the closures of the context (marked in `bs`, innermost first) only applied? -/
  def IExpr.borrowsOk {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {τ : Ty N} (bs : List Bool) : IExpr N F G σ Γ τ → Bool
    | .var v => !(bs.getD v.toNat false)
    | .appVar f a => bs.getD f.toNat false && a.borrowsOk bs
    | .scalarBitop _ _ a b => a.borrowsOk bs && b.borrowsOk bs
    | .bitNot _ a => a.borrowsOk bs
    | .cast _ _ a => a.borrowsOk bs
    | .castFromBool _ a => a.borrowsOk bs
    | .boolBinop _ a b => a.borrowsOk bs && b.borrowsOk bs
    | .boolNot a => a.borrowsOk bs
    | .bne (inst := _) a b => a.borrowsOk bs && b.borrowsOk bs
    | .decide c => c.borrowsOk bs
    | .ite c t e => c.borrowsOk bs && t.borrowsOk bs && e.borrowsOk bs
    | .tuple es => es.borrowsOk bs
    | .ctor _ _ (inst := _) _ _ _ _ args => args.borrowsOk bs
    | .proj _ _ (inst := _) _ _ _ _ e => e.borrowsOk bs
    | .call _ _ _ _ _ _ _ args => args.borrowsOk bs
    | .continue_ _ _ e => e.borrowsOk bs
    | .break_ _ _ e => e.borrowsOk bs
    | _ => true
  termination_by structural e => e
  def IExprs.borrowsOk {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {tys : List (Ty N)} (bs : List Bool) : IExprs N F G σ Γ tys → Bool
    | .nil => true
    | .cons e es => e.borrowsOk bs && es.borrowsOk bs
  termination_by structural es => es
  def ICond.borrowsOk {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} (bs : List Bool) : ICond N F G σ Γ → Bool
    | .bool b => b.borrowsOk bs
    | .not c => c.borrowsOk bs
    | .eq (inst := _) a b => a.borrowsOk bs && b.borrowsOk bs
    | .lt (ord := _) (inst := _) a b => a.borrowsOk bs && b.borrowsOk bs
    | .le (ord := _) (inst := _) a b => a.borrowsOk bs && b.borrowsOk bs
    | .gt (ord := _) (inst := _) a b => a.borrowsOk bs && b.borrowsOk bs
    | .ge (ord := _) (inst := _) a b => a.borrowsOk bs && b.borrowsOk bs
  termination_by structural c => c
end

mutual
  /-- Are the closures only the backward functions of the borrows, and only applied? The
  result of an `index_mut` primitive must be bound by a `borrow`. -/
  def Stmt.borrowsOk {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
      {Γ : List (Ty N)} {τ : Ty N} (bs : List Bool) : Stmt N F G σ Γ τ → Bool
    | .pure e => e.borrowsOk bs
    | .ret e => e.borrowsOk bs
    | .fail _ _ => true
    | .letVal (Δ := Δ) e _ k => e.borrowsOk bs && k.borrowsOk (List.replicate Δ.length false ++ bs)
    | .letStmt (Δ := Δ) s _ k => s.borrowsOk bs && k.borrowsOk (List.replicate Δ.length false ++ bs)
    | .bindStmt (Δ := Δ) s _ k => s.borrowsOk bs && k.borrowsOk (List.replicate Δ.length false ++ bs)
    | .call f _ _ _ _ _ _ args => !f.isIndexMut && args.borrowsOk bs
    | .global _ _ _ _ _ => true
    | .scalarBinop _ _ a b => a.borrowsOk bs && b.borrowsOk bs
    | .neg _ a => a.borrowsOk bs
    | .assert c => c.borrowsOk bs
    | .ite c t e => c.borrowsOk bs && t.borrowsOk bs && e.borrowsOk bs
    | .switch _ (inst := _) _ _ _ _ s brs => s.borrowsOk bs && brs.borrowsOk bs
    | .loop (Δ := Δ) _ init body =>
      init.borrowsOk bs && body.borrowsOk (List.replicate Δ.length false ++ bs)
    | .borrow _ _ _ _ _ _ args p k => args.borrowsOk bs && k.borrowsOk (p.borrowMarks ++ bs)
  termination_by structural s => s
  def SBranches.borrowsOk {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N]
      {σ : TyEnv} {Γ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N} (bs : List Bool) :
      SBranches N F G σ Γ shape τ → Bool
    | .nil => true
    | .cons (Δ := Δ) b brs =>
      b.borrowsOk (List.replicate Δ.length false ++ bs) && brs.borrowsOk bs
  termination_by structural brs => brs
end

end Aeneas.Deep.IR
