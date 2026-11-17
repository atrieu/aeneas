module
public import Aeneas.Deep.Basic
public import Aeneas.Deep.IR
public import Aeneas.Deep.Compile
public section

/-! # Correctness of the compiler

`Stmt.exec (compile e) env = e.denote env`: the interpreter of the IR, on the compiled
body, computes the denotation of the deep term, hence (by the `f.deep_eq` theorem) the
translated Rust function. The interpreter mirrors the denotation node for node (loops reuse
`Std.loop`), so the proof is an induction on the deep term; it is carried out as a strong
induction on the size (`sizeOf`) of the term (the structural recursion of theorems over the
mutual inductive families is not supported). -/

namespace Aeneas.Deep

open Aeneas.Std Aeneas.Deep.IR

variable {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}

namespace Compile

-- The equation lemmas of the compiler (generated on first use, with the inner matches of
-- the `app` and `bind` arms) are costly to generate
set_option maxHeartbeats 1000000

/-- Unfold the compiler at a node and case on the results of the recursive calls: the
hypothesis `h : compileX e = .ok e'` becomes `h : .ok (node …) = .ok e'` with one
hypothesis `compileX sub = .ok sub'` per sub-term (or a contradiction) -/
macro "deep_compile_cases" h:ident : tactic => `(tactic| (
    simp only [compileExpr, compileExprs, compileCond, compileStmt, compileBranches,
      Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      reduceCtorEq] at $h:ident
    repeat (any_goals (first
      | (split at $h:ident <;> try contradiction)
      | simp only [Bind.bind, Except.bind, Pure.pure, Except.pure, throw, throwThe,
          MonadExceptOf.throw, reduceCtorEq] at $h:ident))
    all_goals try (simp only [Except.ok.injEq] at $h:ident; first | subst $h:ident | rw [← $h:ident])))

/-- Unfold the two denotations at the head node -/
macro "deep_denote" : tactic =>
  `(tactic| simp only [IExpr.denote, Expr.denote, IExprs.denote, Exprs.denote, ICond.denote,
      Cond.denote])

/-! ## The pure fragment -/

theorem pure_correct : ∀ n : Nat,
    (∀ {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ), sizeOf e ≤ n →
      ∀ (e' : IExpr N F G σ Γ τ), compileExpr e = .ok e' →
        ∀ env : Env N σ Γ, e'.denote env = e.denote env) ∧
    (∀ {Γ : List (Ty N)} {tys : List (Ty N)} (es : Exprs N F G σ Γ tys), sizeOf es ≤ n →
      ∀ (es' : IExprs N F G σ Γ tys), compileExprs es = .ok es' →
        ∀ env : Env N σ Γ, es'.denote env = es.denote env) ∧
    (∀ {Γ : List (Ty N)} (c : Cond N F G σ Γ), sizeOf c ≤ n →
      ∀ (c' : ICond N F G σ Γ), compileCond c = .ok c' →
        ∀ env : Env N σ Γ, c'.denote env = c.denote env)
  | 0 => by
    refine ⟨?_, ?_, ?_⟩
    · intro Γ τ e hn; cases e <;> simp at hn
    · intro Γ tys es hn; cases es <;> simp at hn
    · intro Γ c hn; cases c <;> simp at hn
  | n + 1 => by
    obtain ⟨ihE, ihEs, ihC⟩ := pure_correct n
    refine ⟨?_, ?_, ?_⟩
    · intro Γ τ e hn e' h env
      cases e
      case var => deep_compile_cases h; deep_denote
      case uscalarLit => deep_compile_cases h; deep_denote
      case iscalarLit => deep_compile_cases h; deep_denote
      case boolLit => deep_compile_cases h; deep_denote
      case unitLit => deep_compile_cases h; deep_denote
      case scalarBitop =>
        rename_i op ty a b; simp only [Expr.scalarBitop.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x₁ a' ha x₂ b' hb; deep_denote
        rw [ihE a (by omega) a' ha env, ihE b (by omega) b' hb env]
      case bitNot =>
        rename_i ty a; simp only [Expr.bitNot.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x a' ha; deep_denote
        rw [ihE a (by omega) a' ha env]
      case cast =>
        rename_i src tgt a; simp only [Expr.cast.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x a' ha; deep_denote
        rw [ihE a (by omega) a' ha env]
      case castFromBool =>
        rename_i tgt a; simp only [Expr.castFromBool.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x a' ha; deep_denote
        rw [ihE a (by omega) a' ha env]
      case boolBinop =>
        rename_i op a b; simp only [Expr.boolBinop.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x₁ a' ha x₂ b' hb; deep_denote
        rw [ihE a (by omega) a' ha env, ihE b (by omega) b' hb env]
      case boolNot =>
        rename_i a; simp only [Expr.boolNot.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x a' ha; deep_denote
        rw [ihE a (by omega) a' ha env]
      case bne =>
        rename_i α inst a b; simp only [Expr.bne.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x₁ a' ha x₂ b' hb; deep_denote
        rw [ihE a (by omega) a' ha env, ihE b (by omega) b' hb env]
      case decide =>
        rename_i c; simp only [Expr.decide.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x c' hc; deep_denote
        rw [ihC c (by omega) c' hc env]
      case ite =>
        rename_i c t e; simp only [Expr.ite.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x₁ c' hc x₂ t' ht x₃ e' he; deep_denote
        rw [ihC c (by omega) c' hc env, ihE t (by omega) t' ht env, ihE e (by omega) e' he env]
      case tuple =>
        rename_i tys es; simp only [Expr.tuple.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x es' hes; deep_denote
        rw [ihEs es (by omega) es' hes env]
      case array =>
        rename_i τ n hb es; simp only [Expr.array.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x es' hes; deep_denote
        rw [ihEs es (by omega) es' hes env]
      case ctor =>
        rename_i T v inst targs cargs fields hf args; simp only [Expr.ctor.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x args' hargs; deep_denote
        rw [ihEs args (by omega) args' hargs env]
      case proj =>
        rename_i T f inst targs cargs e hf; simp only [Expr.proj.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x e' he; deep_denote
        rw [ihE e (by omega) e' he env]
      case global => deep_compile_cases h; deep_denote
      case call =>
        rename_i f targs cargs inputs h₁ args h₂; simp only [Expr.call.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x args' hargs; deep_denote
        rw [ihEs args (by omega) args' hargs env]
      case continue_ =>
        rename_i α β e; simp only [Expr.continue_.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x e' he; deep_denote
        rw [ihE e (by omega) e' he env]
      case break_ =>
        rename_i α β e; simp only [Expr.break_.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x e' he; deep_denote
        rw [ihE e (by omega) e' he env]
      case app =>
        -- the application of a variable (the backward function of a borrow)
        rename_i α f a; simp only [Expr.app.sizeOf_spec] at hn
        deep_compile_cases h
        -- (the split on the head generalises it: unify with the goal rather than name it)
        all_goals (deep_denote; exact congrArg _ (ihE _ (by omega) _ (by assumption) env))
      all_goals deep_compile_cases h
    · intro Γ tys es hn es' h env
      cases es
      case nil => deep_compile_cases h; deep_denote
      case cons =>
        rename_i τ tys e es; simp only [Exprs.cons.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x₁ e' he x₂ es' hes; deep_denote
        rw [ihE e (by omega) e' he env, ihEs es (by omega) es' hes env]
    · intro Γ c hn c' h env
      cases c
      case bool =>
        rename_i b; simp only [Cond.bool.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x b' hb; deep_denote
        rw [ihE b (by omega) b' hb env]
      case not =>
        rename_i c; simp only [Cond.not.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x c' hc; deep_denote
        rw [ihC c (by omega) c' hc env]
      all_goals
        rename_i a b; simp at hn
        deep_compile_cases h; rename_i x₁ a' ha x₂ b' hb; deep_denote
        rw [ihE a (by omega) a' ha env, ihE b (by omega) b' hb env]

theorem compileExpr_correct {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ)
    (e' : IExpr N F G σ Γ τ) (h : compileExpr e = .ok e') (env : Env N σ Γ) :
    e'.denote env = e.denote env :=
  (pure_correct (sizeOf e)).1 e (Nat.le_refl _) e' h env

theorem compileExprs_correct {Γ : List (Ty N)} {tys : List (Ty N)} (es : Exprs N F G σ Γ tys)
    (es' : IExprs N F G σ Γ tys) (h : compileExprs es = .ok es') (env : Env N σ Γ) :
    es'.denote env = es.denote env :=
  (pure_correct (sizeOf es)).2.1 es (Nat.le_refl _) es' h env

theorem compileCond_correct {Γ : List (Ty N)} (c : Cond N F G σ Γ) (c' : ICond N F G σ Γ)
    (h : compileCond c = .ok c') (env : Env N σ Γ) : c'.denote env = c.denote env :=
  (pure_correct (sizeOf c)).2.2 c (Nat.le_refl _) c' h env

/-! ## Statements -/

theorem stmt_correct : ∀ n : Nat,
    (∀ {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ), sizeOf e ≤ n →
      ∀ (s : Stmt N F G σ Γ τ), compileStmt e = .ok s →
        ∀ env : Env N σ Γ, s.exec env = e.denote env) ∧
    (∀ {Γ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N}
      (brs : Branches N F G σ Γ shape τ), sizeOf brs ≤ n →
      ∀ (brs' : SBranches N F G σ Γ shape τ), compileBranches brs = .ok brs' →
        ∀ env : Env N σ Γ, brs'.exec env = brs.denote env)
  | 0 => by
    refine ⟨?_, ?_⟩
    · intro Γ τ e hn; cases e <;> simp at hn
    · intro Γ shape τ brs hn; cases brs <;> simp at hn
  | n + 1 => by
    obtain ⟨ihS, ihB⟩ := stmt_correct n
    refine ⟨?_, ?_⟩
    · intro Γ τ e hn s h env
      cases e
      case bind =>
        rename_i p e k; simp only [Expr.bind.sizeOf_spec] at hn
        deep_compile_cases h
        -- (the split on the bound term generalises it: unify with the goal rather than name it)
        all_goals first
          | -- the generic bind
            (simp only [Stmt.exec, Expr.denote]
             refine congrArg₂ Std.bind (ihS _ (by omega) _ (by assumption) env) ?_
             funext x
             exact ihS k (by omega) _ (by assumption : compileStmt k = .ok _) _)
          | -- a borrow: `MutIndex.borrow_eq`, the borrow is the `index_mut` primitive
            (simp only [Stmt.exec, Expr.denote, MutIndex.borrow_eq, FunRef.impl, MutIndex.prim]
             refine congrArg₂ Std.bind ?_ ?_
             · rw [compileExprs_correct _ _ (by assumption : compileExprs _ = .ok _) env]
             · funext x
               exact ihS k (by omega) _ (by assumption : compileStmt k = .ok _) _)
      case let_ =>
        rename_i p e k; simp only [Expr.let_.sizeOf_spec] at hn
        deep_compile_cases h
        all_goals
          simp only [Stmt.exec, Expr.denote]
          first
          | (obtain ⟨_, he⟩ : ∃ y, compileExpr e = .ok y := ⟨_, by assumption⟩
             rw [compileExpr_correct e _ (by assumption : compileExpr e = .ok _) env])
          | (obtain ⟨_, hs⟩ : ∃ y, compileStmt e = .ok y := ⟨_, by assumption⟩
             rw [ihS e (by omega) _ (by assumption : compileStmt e = .ok _) env])
          exact ihS k (by omega) _ (by assumption : compileStmt k = .ok _) _
      case ite =>
        rename_i c t e; simp only [Expr.ite.sizeOf_spec] at hn
        deep_compile_cases h
        simp only [Stmt.exec, Expr.denote]
        rw [compileCond_correct c _ (by assumption : compileCond c = .ok _) env, ihS t (by omega) _ (by assumption : compileStmt t = .ok _) env, ihS e (by omega) _ (by assumption : compileStmt e = .ok _) env]
      case match_ =>
        rename_i T inst targs cargs shape hs s brs; simp only [Expr.match_.sizeOf_spec] at hn
        deep_compile_cases h
        simp only [Stmt.exec, Expr.denote]
        rw [compileExpr_correct s _ (by assumption : compileExpr s = .ok _) env, ihB brs (by omega) _ (by assumption : compileBranches brs = .ok _) env]
      case loop =>
        rename_i body init
        cases body
        case lam =>
          rename_i α p b; simp only [Expr.loop.sizeOf_spec, Expr.lam.sizeOf_spec] at hn
          deep_compile_cases h
          simp only [Stmt.exec, Expr.denote]
          rw [compileExpr_correct init _ (by assumption : compileExpr init = .ok _) env]
          congr 1; funext x
          exact ihS b (by omega) _ (by assumption : compileStmt b = .ok _) _
        all_goals deep_compile_cases h
      case ok =>
        rename_i e; simp only [Expr.ok.sizeOf_spec] at hn
        deep_compile_cases h
        all_goals
          simp only [Stmt.exec, Expr.denote, IExpr.denote, Pat.bindEnv, Env.append, Var.get]
          first
          | (obtain ⟨_, he⟩ : ∃ y, compileExpr e = .ok y := ⟨_, by assumption⟩
             rw [compileExpr_correct e _ (by assumption : compileExpr e = .ok _) env])
          | (obtain ⟨_, hs⟩ : ∃ y, compileStmt e = .ok y := ⟨_, by assumption⟩
             rw [ihS e (by omega) _ (by assumption : compileStmt e = .ok _) env])
      case fail => deep_compile_cases h; simp only [Stmt.exec, Expr.denote]
      case assert =>
        rename_i c
        deep_compile_cases h
        simp only [Stmt.exec, Expr.denote]
        rw [compileCond_correct c _ (by assumption : compileCond c = .ok _) env]
      case scalarBinop =>
        rename_i op ty a b
        deep_compile_cases h
        simp only [Stmt.exec, Expr.denote]
        rw [compileExpr_correct a _ (by assumption : compileExpr a = .ok _) env, compileExpr_correct b _ (by assumption : compileExpr b = .ok _) env]
      case neg =>
        rename_i ty a
        deep_compile_cases h
        simp only [Stmt.exec, Expr.denote]
        rw [compileExpr_correct a _ (by assumption : compileExpr a = .ok _) env]
      case call =>
        rename_i f targs cargs inputs h₁ args h₂
        deep_compile_cases h
        all_goals
          simp only [Stmt.exec, IExpr.denote, Expr.denote]
          rw [compileExprs_correct args _ (by assumption : compileExprs args = .ok _) env]
      case global =>
        deep_compile_cases h
        all_goals simp only [Stmt.exec, IExpr.denote, Expr.denote]
      -- the pure nodes: `compileStmt` wraps `compileExpr` in `Stmt.pure`
      all_goals deep_compile_cases h
      all_goals first
        | (simp only [Stmt.exec, IExpr.denote, Expr.denote]; done)
        | (rename_i x e' he
           simp only [Stmt.exec]
           exact compileExpr_correct _ e'
             (by simpa [compileExpr, Bind.bind, Except.bind, Pure.pure, Except.pure, throw,
               throwThe, MonadExceptOf.throw, reduceCtorEq] using he) env)
    · intro Γ shape τ brs hn brs' h env
      cases brs
      case nil => deep_compile_cases h; simp only [SBranches.exec, Branches.denote]
      case cons =>
        rename_i Δ shape b bs; simp only [Branches.cons.sizeOf_spec] at hn
        deep_compile_cases h; rename_i x₁ b' hb x₂ bs' hbs
        simp only [SBranches.exec, Branches.denote]
        rw [ihB bs (by omega) bs' hbs env]
        congr 1
        congr 1; funext fields
        exact ihS b (by omega) b' hb _

theorem compileStmt_correct {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ)
    (s : Stmt N F G σ Γ τ) (h : compileStmt e = .ok s) (env : Env N σ Γ) :
    s.exec env = e.denote env :=
  (stmt_correct (sizeOf e)).1 e (Nat.le_refl _) s h env

/-- The correctness of the compiler: the interpreter of the IR, on the compiled body, computes
the denotation of the deep term -/
theorem compile_correct {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ)
    (s : Stmt N F G σ Γ τ) (h : compile e = .ok s) (env : Env N σ Γ) :
    s.exec env = e.denote env := by
  apply compileStmt_correct e s _ env
  unfold compile at h
  revert h
  cases compileStmt e with
  | error u => intro h; simp [Bind.bind, Except.bind] at h
  | ok s' =>
    intro h
    simp only [Bind.bind, Except.bind] at h
    split at h
    · simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; rw [h]
    · simp [throw, throwThe, MonadExceptOf.throw] at h

end Compile

end Aeneas.Deep
