module
public import Aeneas.Deep.Basic
public import Aeneas.Deep.IR
@[expose] public section

/-! # The compiler from the deep terms to the IR

The compiler recognises the first-order fragment of the deep terms and restructures it into
the A-normal form of the IR: pure sub-terms become `IExpr`s, the monadic spine becomes
statements, a `bind`/`let` of a non-trivial computation (an `if` or a `match` computing a
value) becomes a `bindStmt`/`letStmt`, and the `loop` combinator applied to a lambda becomes
the `loop` statement. Everything the IR can not express (shallow leaves, lambdas and
applications, the escape hatch) is reported as `Unsupported`, which the coverage report
(`#deep_report`) aggregates.

The compiler is total and structural; its correctness (`Stmt.exec (compile e) = e.denote`)
is the object of phase D of `PLAN-compiler.md`. -/

namespace Aeneas.Deep.Compile

open Aeneas.Std Aeneas.Deep.IR

/-- Why a deep term is not compiled -/
inductive Unsupported where
  /-- A shallow leaf (a call to a function outside the closed world, …) -/
  | leaf (tag : Leaf)
  | lambda
  | application
  /-- The escape hatch -/
  | shallow
  /-- A `loop` whose body is not a lambda -/
  | loopBody
  /-- A binder (`let`, `bind`, `match`, `ok`, …) in a position where a pure expression is
  expected -/
  | effectInExpr
  /-- A fallible call or global in a position where a pure expression is expected -/
  | fallibleInExpr
  deriving Repr, Inhabited

/-- Is this a `Result` type? -/
def _root_.Aeneas.Deep.Ty.isResult {N : Type} : Ty N → Bool
  | .result _ => true
  | _ => false

variable {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}

/-! ## The pure fragment -/

mutual
  def compileExpr {Γ : List (Ty N)} {τ : Ty N} : Expr N F G σ Γ τ →
      Except Unsupported (IExpr N F G σ Γ τ)
    | .var v => pure (.var v)
    | .uscalarLit ty n h => pure (.uscalarLit ty n h)
    | .iscalarLit ty n h => pure (.iscalarLit ty n h)
    | .boolLit b => pure (.boolLit b)
    | .unitLit => pure .unitLit
    | .scalarBitop op ty a b => do
      pure (.scalarBitop op ty (← compileExpr a) (← compileExpr b))
    | .bitNot ty a => do pure (.bitNot ty (← compileExpr a))
    | .cast src tgt a => do pure (.cast src tgt (← compileExpr a))
    | .castFromBool tgt a => do pure (.castFromBool tgt (← compileExpr a))
    | .boolBinop op a b => do pure (.boolBinop op (← compileExpr a) (← compileExpr b))
    | .boolNot a => do pure (.boolNot (← compileExpr a))
    | .bne (inst := inst) a b => do
      pure (.bne (inst := inst) (← compileExpr a) (← compileExpr b))
    | .decide c => do pure (.decide (← compileCond c))
    | .ite c t e => do pure (.ite (← compileCond c) (← compileExpr t) (← compileExpr e))
    | .tuple es => do pure (.tuple (← compileExprs es))
    | @Expr.ctor _ _ _ _ _ _ _ _ T v inst targs cargs fields h args => do
      pure (@IExpr.ctor _ _ _ _ _ _ _ _ T v inst targs cargs fields h (← compileExprs args))
    | @Expr.proj _ _ _ _ _ _ _ _ T f inst targs cargs τ h e => do
      pure (@IExpr.proj _ _ _ _ _ _ _ _ T f inst targs cargs τ h (← compileExpr e))
    | .global g targs cargs τ h =>
      if τ.isResult then throw .fallibleInExpr else pure (.global g targs cargs τ h)
    | .call f targs cargs inputs output h₁ h₂ args =>
      if output.isResult then throw .fallibleInExpr
      else do pure (.call f targs cargs inputs output h₁ h₂ (← compileExprs args))
    | .continue_ α β e => do pure (.continue_ α β (← compileExpr e))
    | .break_ α β e => do pure (.break_ α β (← compileExpr e))
    | .leaf tag _ _ => throw (.leaf tag)
    | .app f _ => do
      -- Report the head of the application when it is a leaf (a call to a function
      -- outside the closed world); an application of a variable is a closure call
      let _ ← compileExpr f
      throw .application
    | .lam _ _ _ => throw .lambda
    | .shallow _ _ => throw .shallow
    | .let_ _ _ _ => throw .effectInExpr
    | .bind _ _ _ => throw .effectInExpr
    | .scalarBinop _ _ _ _ => throw .effectInExpr
    | .neg _ _ => throw .effectInExpr
    | .assert _ => throw .effectInExpr
    | .ok _ => throw .effectInExpr
    | .fail _ _ => throw .effectInExpr
    | @Expr.match_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => throw .effectInExpr
    | .loop _ _ => throw .effectInExpr
  termination_by structural e => e

  def compileExprs {Γ : List (Ty N)} {tys : List (Ty N)} : Exprs N F G σ Γ tys →
      Except Unsupported (IExprs N F G σ Γ tys)
    | .nil => pure .nil
    | .cons e es => do pure (.cons (← compileExpr e) (← compileExprs es))
  termination_by structural es => es

  def compileCond {Γ : List (Ty N)} : Cond N F G σ Γ → Except Unsupported (ICond N F G σ Γ)
    | .bool b => do pure (.bool (← compileExpr b))
    | .not c => do pure (.not (← compileCond c))
    | .eq (inst := inst) a b => do pure (.eq (inst := inst) (← compileExpr a) (← compileExpr b))
    | .lt (ord := ord) (inst := inst) a b => do
      pure (.lt (ord := ord) (inst := inst) (← compileExpr a) (← compileExpr b))
    | .le (ord := ord) (inst := inst) a b => do
      pure (.le (ord := ord) (inst := inst) (← compileExpr a) (← compileExpr b))
    | .gt (ord := ord) (inst := inst) a b => do
      pure (.gt (ord := ord) (inst := inst) (← compileExpr a) (← compileExpr b))
    | .ge (ord := ord) (inst := inst) a b => do
      pure (.ge (ord := ord) (inst := inst) (← compileExpr a) (← compileExpr b))
  termination_by structural c => c
end

/-! ## Statements -/

mutual
  def compileStmt {Γ : List (Ty N)} {τ : Ty N} : Expr N F G σ Γ τ →
      Except Unsupported (Stmt N F G σ Γ τ)
    | .bind e p k => do pure (.bindStmt (← compileStmt e) p (← compileStmt k))
    | .let_ e p k => do
      let k' ← compileStmt k
      match compileExpr e with
      | .ok e' => pure (.letVal e' p k')
      | .error _ => do pure (.letStmt (← compileStmt e) p k')
    | .ite c t e => do pure (.ite (← compileCond c) (← compileStmt t) (← compileStmt e))
    | @Expr.match_ _ _ _ _ _ _ _ _ _ T inst targs cargs shape h s brs => do
      pure (@Stmt.switch _ _ _ _ _ _ _ _ _ T inst targs cargs shape h (← compileExpr s)
        (← compileBranches brs))
    | .loop (.lam _ p b) init => do pure (.loop p (← compileExpr init) (← compileStmt b))
    | .loop _ _ => throw .loopBody
    | .ok e =>
      match compileExpr e with
      | .ok e' => pure (.ret e')
      | .error _ => do pure (.letStmt (← compileStmt e) .var (.ret (.var .zero)))
    | .fail τ err => pure (.fail τ err)
    | .assert c => do pure (.assert (← compileCond c))
    | .scalarBinop op ty a b => do
      pure (.scalarBinop op ty (← compileExpr a) (← compileExpr b))
    | .neg ty a => do pure (.neg ty (← compileExpr a))
    | .call f targs cargs inputs output h₁ h₂ args =>
      match output, h₂ with
      | .result τ, h₂ => do pure (.call f targs cargs inputs τ h₁ h₂ (← compileExprs args))
      | output, h₂ => do
        pure (.pure (.call f targs cargs inputs output h₁ h₂ (← compileExprs args)))
    | .global g targs cargs τ h =>
      match τ, h with
      | .result τ, h => pure (.global g targs cargs τ h)
      | τ, h => pure (.pure (.global g targs cargs τ h))
    | e => do pure (.pure (← compileExpr e))
  termination_by structural e => e

  def compileBranches {Γ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N} :
      Branches N F G σ Γ shape τ → Except Unsupported (SBranches N F G σ Γ shape τ)
    | .nil => pure .nil
    | .cons b bs => do pure (.cons (← compileStmt b) (← compileBranches bs))
  termination_by structural bs => bs
end

/-- Compile the body of a function -/
def compile {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ) :
    Except Unsupported (Stmt N F G σ Γ τ) :=
  compileStmt e

end Aeneas.Deep.Compile
