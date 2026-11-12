module
public import Aeneas.Deep.Basic
public import Aeneas.Deep.Tactic
public import Aeneas.Deep.Tests.Shallow
public section

/-! # Tests for the deep embedding

Hand-written deep terms, in the shape the printer generates them, with their denotation
theorems proved by reflexivity. The first section is what the printer generates once per
crate: the enumerations of the type, function and global names and their instances. -/

open Aeneas Aeneas.Std Result Error
open Aeneas.Deep.Tests.Shallow

namespace Aeneas.Deep.Tests

/-! ## The closed world of the crate -/

inductive TypeName where
  | CList
  | Pair

instance : TypeNames TypeName where
  denote
    | .CList, ρ => CList (tyAt ρ.types 0)
    | .Pair, ρ => Pair (tyAt ρ.types 0) (tyAt ρ.types 1)
  variants
    | .CList => [[.var 0, .adt (.crate .CList) [.var 0] []], []]
    | .Pair => [[.var 0, .var 1]]

instance : CtorFn TypeName (.crate .CList) 0 := ⟨fun _ => fun x tl => CList.CCons x tl⟩
instance : CtorFn TypeName (.crate .CList) 1 := ⟨fun _ => CList.CNil⟩
instance : ElimFn TypeName (.crate .CList) := ⟨fun _ => fun l alts => CList.casesOn l alts.1 alts.2.1⟩

instance : CtorFn TypeName (.crate .Pair) 0 := ⟨fun _ => fun x y => Pair.mk x y⟩
instance : ProjFn TypeName (.crate .Pair) 0 := ⟨fun _ => fun p => p.x⟩
instance : ProjFn TypeName (.crate .Pair) 1 := ⟨fun _ => fun p => p.y⟩
instance : ElimFn TypeName (.crate .Pair) := ⟨fun _ => fun p alts => Pair.casesOn p alts.1⟩

local notation "U32T" => Ty.scalar (ScalarTy.u UScalarTy.U32)
local notation "I32T" => Ty.scalar (ScalarTy.i IScalarTy.I32)

inductive FunName where
  | mul2_add1
  | incr
  | i32_id
  | list_nth
  | list_nth_mut
  | sum_loop_body
  | sum_loop

instance : FunNames FunName TypeName where
  defs
    | .mul2_add1 => ⟨⟨[U32T], .result U32T⟩, fun _ => mul2_add1⟩
    | .incr => ⟨⟨[U32T], .result U32T⟩, fun _ => incr⟩
    | .i32_id => ⟨⟨[I32T], .result I32T⟩, fun _ => i32_id⟩
    | .list_nth =>
      ⟨⟨[.adt (.crate TypeName.CList) [.var 0] [], U32T], .result (.var 0)⟩,
       fun ρ => @list_nth (tyAt ρ.types 0)⟩
    | .list_nth_mut =>
      ⟨⟨[.adt (.crate TypeName.CList) [.var 0] [], U32T],
        .result (.tuple [.var 0, .arrow (.var 0) (.adt (.crate TypeName.CList) [.var 0] [])])⟩,
       fun ρ => @list_nth_mut (tyAt ρ.types 0)⟩
    | .sum_loop_body =>
      ⟨⟨[U32T, U32T, U32T], .result (.controlFlow (.tuple [U32T, U32T]) U32T)⟩, fun _ => sum_loop.body⟩
    | .sum_loop => ⟨⟨[U32T, U32T, U32T], .result U32T⟩, fun _ => sum_loop⟩

inductive GlobalName where

instance : GlobalNames GlobalName TypeName where
  defs g := nomatch g

local notation "DeepExpr" => Expr TypeName FunName GlobalName

/-! ## Scalars, binds, calls -/

def mul2_add1.deep : DeepExpr ⟨[], []⟩ [U32T] (.result U32T) :=
  .bind (.scalarBinop .add (.u .U32) (.var .zero) (.var .zero)) .var
    (.scalarBinop .add (.u .U32) (.var .zero) (.uscalarLit .U32 1 (by decide)))

theorem mul2_add1.deep_eq (x : Std.U32) :
    mul2_add1 x = mul2_add1.deep.denote (x ::ₑ .nil) := by rfl

def use_mul2_add1.deep : DeepExpr ⟨[], []⟩ [U32T, U32T] (.result U32T) :=
  .bind (.call (.crate FunName.mul2_add1) [] [] [U32T] (.result U32T) rfl rfl (.cons (.var .zero) .nil)) .var
    (.scalarBinop .add (.u .U32) (.var .zero) (.var (.succ (.succ .zero))))

theorem use_mul2_add1.deep_eq (x y : Std.U32) :
    use_mul2_add1 x y = use_mul2_add1.deep.denote (x ::ₑ y ::ₑ .nil) := by rfl

def use_incr.deep : DeepExpr ⟨[], []⟩ [] (.result .unit) :=
  .bind (.call (.crate FunName.incr) [] [] [U32T] (.result U32T) rfl rfl
          (.cons (.uscalarLit .U32 0 (by decide)) .nil)) .var
    (.bind (.call (.crate FunName.incr) [] [] [U32T] (.result U32T) rfl rfl (.cons (.var .zero) .nil)) .var
      (.bind (.call (.crate FunName.incr) [] [] [U32T] (.result U32T) rfl rfl (.cons (.var .zero) .nil)) .ignore
        (.ok .unitLit)))

theorem use_incr.deep_eq : use_incr = use_incr.deep.denote .nil := by rfl

/-! ## Generics, booleans, lambdas, tuples -/

def choose.deep {T : Type} : DeepExpr ⟨[T], []⟩ [.bool, .var 0, .var 0]
    (.result (.tuple [.var 0, .arrow (.var 0) (.tuple [.var 0, .var 0])])) :=
  -- b=0, x=1, y=2
  .ite (.bool (.var .zero))
    (.let_ (.lam (.var 0) .var
        -- x1=0, b=1, x=2, y=3
        (.pair (.var .zero) (.var (.succ (.succ (.succ .zero)))))) .var
      -- back=0, b=1, x=2, y=3
      (.ok (.pair (.var (.succ (.succ .zero))) (.var .zero))))
    (.let_ (.lam (.var 0) .var
        -- y1=0, b=1, x=2, y=3
        (.pair (.var (.succ (.succ .zero))) (.var .zero))) .var
      (.ok (.pair (.var (.succ (.succ (.succ .zero)))) (.var .zero))))

theorem choose.deep_eq {T : Type} (b : Bool) (x y : T) :
    choose b x y = choose.deep.denote (b ::ₑ x ::ₑ y ::ₑ .nil) := by rfl

/-! ## Recursion, signed scalars: `unfold` then `rfl` -/

def i32_id.deep : DeepExpr ⟨[], []⟩ [I32T] (.result I32T) :=
  .ite (.eq (.var .zero) (.iscalarLit .I32 0 (by decide)))
    (.ok (.iscalarLit .I32 0 (by decide)))
    (.bind (.scalarBinop .sub (.i .I32) (.var .zero) (.iscalarLit .I32 1 (by decide))) .var
      (.bind (.call (.crate FunName.i32_id) [] [] [I32T] (.result I32T) rfl rfl (.cons (.var .zero) .nil)) .var
        (.scalarBinop .add (.i .I32) (.var .zero) (.iscalarLit .I32 1 (by decide)))))

theorem i32_id.deep_eq (i : Std.I32) :
    i32_id i = i32_id.deep.denote (i ::ₑ .nil) := by
  unfold i32_id; deep_rfl

/-! ## Matches, constructors and calls of the closed world, at type arguments -/

def list_nth.deep {T : Type} :
    DeepExpr ⟨[T], []⟩ [.adt (.crate TypeName.CList) [.var 0] [], U32T] (.result (.var 0)) :=
  .match_ (.crate TypeName.CList) [.var 0] [] [[.var 0, .adt (.crate TypeName.CList) [.var 0] []], []] rfl (.var .zero)
    (.cons -- x=0, tl=1, l=2, i=3
      (.ite (.eq (.var (.succ (.succ (.succ .zero)))) (.uscalarLit .U32 0 (by decide)))
        (.ok (.var .zero))
        (.bind (.scalarBinop .sub (.u .U32) (.var (.succ (.succ (.succ .zero))))
                 (.uscalarLit .U32 1 (by decide))) .var
          -- i1=0, x=1, tl=2, l=3, i=4
          (.call (.crate FunName.list_nth) [.var 0] [] [.adt (.crate TypeName.CList) [.var 0] [], U32T] (.result (.var 0))
            rfl rfl (.cons (.var (.succ (.succ .zero))) (.cons (.var .zero) .nil)))))
      (.cons (.fail (.var 0) panic) .nil))

theorem list_nth.deep_eq {T : Type} (l : CList T) (i : Std.U32) :
    list_nth l i = list_nth.deep.denote (l ::ₑ i ::ₑ .nil) := by
  unfold list_nth; deep_rfl

theorem list_nth.deep_eq_meta {T : Type} (l : CList T) (i : Std.U32) :
    list_nth l i = list_nth.deep.denote (l ::ₑ i ::ₑ .nil) := by
  unfold list_nth; deep_rfl_meta

def list_nth_mut.deep {T : Type} :
    DeepExpr ⟨[T], []⟩ [.adt (.crate TypeName.CList) [.var 0] [], U32T]
      (.result (.tuple [.var 0, .arrow (.var 0) (.adt (.crate TypeName.CList) [.var 0] [])])) :=
  .match_ (.crate TypeName.CList) [.var 0] [] [[.var 0, .adt (.crate TypeName.CList) [.var 0] []], []] rfl (.var .zero)
    (.cons -- x=0, tl=1, l=2, i=3
      (.ite (.eq (.var (.succ (.succ (.succ .zero)))) (.uscalarLit .U32 0 (by decide)))
        (.let_ (.lam (.var 0) .var
            -- t=0, x=1, tl=2, l=3, i=4
            (.ctor (.crate TypeName.CList) 0 [.var 0] [] [.var 0, .adt (.crate TypeName.CList) [.var 0] []] rfl
              (.cons (.var .zero) (.cons (.var (.succ (.succ .zero))) .nil)))) .var
          -- back=0, x=1, tl=2, l=3, i=4
          (.ok (.pair (.var (.succ .zero)) (.var .zero))))
        (.bind (.scalarBinop .sub (.u .U32) (.var (.succ (.succ (.succ .zero))))
                 (.uscalarLit .U32 1 (by decide))) .var
          -- i1=0, x=1, tl=2, l=3, i=4
          (.bind (.call (.crate FunName.list_nth_mut) [.var 0] [] [.adt (.crate TypeName.CList) [.var 0] [], U32T]
                    (.result (.tuple [.var 0, .arrow (.var 0) (.adt (.crate TypeName.CList) [.var 0] [])]))
                    rfl rfl (.cons (.var (.succ (.succ .zero))) (.cons (.var .zero) .nil)))
            (.tuple (.cons .var (.cons .var .nil)))
            -- x1=0, back'=1, i1=2, x=3, tl=4, l=5, i=6
            (.let_ (.lam (.var 0) .var
                -- t=0, x1=1, back'=2, i1=3, x=4, tl=5, l=6, i=7
                (.let_ (.app (.var (.succ (.succ .zero))) (.var .zero)) .var
                  -- tl1=0, t=1, x1=2, back'=3, i1=4, x=5, tl=6, l=7, i=8
                  (.ctor (.crate TypeName.CList) 0 [.var 0] [] [.var 0, .adt (.crate TypeName.CList) [.var 0] []] rfl
                    (.cons (.var (.succ (.succ (.succ (.succ (.succ .zero))))))
                      (.cons (.var .zero) .nil))))) .var
              -- back=0, x1=1, back'=2, i1=3, x=4, tl=5, l=6, i=7
              (.ok (.pair (.var (.succ .zero)) (.var .zero)))))))
      (.cons (.fail (.tuple [.var 0, .arrow (.var 0) (.adt (.crate TypeName.CList) [.var 0] [])]) panic) .nil))

theorem list_nth_mut.deep_eq {T : Type} (l : CList T) (i : Std.U32) :
    list_nth_mut l i = list_nth_mut.deep.denote (l ::ₑ i ::ₑ .nil) := by
  unfold list_nth_mut; deep_rfl

theorem list_nth_mut.deep_eq_meta {T : Type} (l : CList T) (i : Std.U32) :
    list_nth_mut l i = list_nth_mut.deep.denote (l ::ₑ i ::ₑ .nil) := by
  unfold list_nth_mut; deep_rfl_meta

def mk_cons.deep {T : Type} :
    DeepExpr ⟨[T], []⟩ [.var 0, .adt (.crate TypeName.CList) [.var 0] []] (.adt (.crate TypeName.CList) [.var 0] []) :=
  .ctor (.crate TypeName.CList) 0 [.var 0] [] [.var 0, .adt (.crate TypeName.CList) [.var 0] []] rfl
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem mk_cons.deep_eq {T : Type} (x : T) (tl : CList T) :
    mk_cons x tl = mk_cons.deep.denote (x ::ₑ tl ::ₑ .nil) := by deep_rfl

/-! ## Loops: `<` on scalars, control flow constructors, tuple lambda, `loop` -/

def sum_loop.body.deep :
    DeepExpr ⟨[], []⟩ [U32T, U32T, U32T] (.result (.controlFlow (.tuple [U32T, U32T]) U32T)) :=
  -- max=0, i=1, s=2
  .ite (.lt (.var (.succ .zero)) (.var .zero))
    (.bind (.scalarBinop .add (.u .U32) (.var (.succ (.succ .zero))) (.var (.succ .zero))) .var
      -- s1=0, max=1, i=2, s=3
      (.bind (.scalarBinop .add (.u .U32) (.var (.succ (.succ .zero))) (.uscalarLit .U32 1 (by decide))) .var
        -- i1=0, s1=1, max=2, i=3, s=4
        (.ok (.continue_ (.tuple [U32T, U32T]) U32T (.pair (.var .zero) (.var (.succ .zero)))))))
    (.ok (.break_ (.tuple [U32T, U32T]) U32T (.var (.succ (.succ .zero)))))

theorem sum_loop.body.deep_eq (max i s : Std.U32) :
    sum_loop.body max i s = sum_loop.body.deep.denote (max ::ₑ i ::ₑ s ::ₑ .nil) := by rfl

def sum_loop.deep : DeepExpr ⟨[], []⟩ [U32T, U32T, U32T] (.result U32T) :=
  .loop
    (.lam (.tuple [U32T, U32T]) (.tuple (.cons .var (.cons .var .nil)))
      -- i1=0, s1=1, max=2, i=3, s=4
      (.call (.crate FunName.sum_loop_body) [] [] [U32T, U32T, U32T]
        (.result (.controlFlow (.tuple [U32T, U32T]) U32T)) rfl rfl
        (.cons (.var (.succ (.succ .zero))) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))))
    (.pair (.var (.succ .zero)) (.var (.succ (.succ .zero))))

theorem sum_loop.deep_eq (max i s : Std.U32) :
    sum_loop max i s = sum_loop.deep.denote (max ::ₑ i ::ₑ s ::ₑ .nil) := by rfl

def sum.deep : DeepExpr ⟨[], []⟩ [U32T] (.result U32T) :=
  .bind (.call (.crate FunName.sum_loop) [] [] [U32T, U32T, U32T] (.result U32T) rfl rfl
          (.cons (.var .zero) (.cons (.uscalarLit .U32 0 (by decide))
            (.cons (.uscalarLit .U32 0 (by decide)) .nil)))) .var
    (.scalarBinop .mul (.u .U32) (.var .zero) (.uscalarLit .U32 2 (by decide)))

theorem sum.deep_eq (max : Std.U32) :
    sum max = sum.deep.denote (max ::ₑ .nil) := by rfl

/-! ## Structures: patterns (single-branch matches), projections, constructors

Matches with a default branch (`| _ => ...`) are *not* supported: Lean compiles them to an
auxiliary `_sparseCasesOn` definition built on `T.rec` with a non-constant motive, which is not
definitionally equal to the `T.casesOn` of a deep eliminator. The printer uses the escape hatch
for them. -/

def pair_sum.deep : DeepExpr ⟨[], []⟩ [.adt (.crate TypeName.Pair) [U32T, U32T] []] (.result U32T) :=
  .match_ (.crate TypeName.Pair) [U32T, U32T] [] [[U32T, U32T]] rfl (.var .zero)
    (.cons (.scalarBinop .add (.u .U32) (.var .zero) (.var (.succ .zero))) .nil)

theorem pair_sum.deep_eq (p : Pair Std.U32 Std.U32) :
    pair_sum p = pair_sum.deep.denote (p ::ₑ .nil) := by deep_rfl

def pair_sum_mono.deep : DeepExpr ⟨[], []⟩ [.adt (.crate TypeName.Pair) [U32T, U32T] []] (.result U32T) :=
  .bind (.ok (.var .zero)) .var
    (.match_ (.crate TypeName.Pair) [U32T, U32T] [] [[U32T, U32T]] rfl (.var .zero)
      (.cons (.scalarBinop .add (.u .U32) (.var .zero) (.var (.succ .zero))) .nil))

theorem pair_sum_mono.deep_eq (p : Pair Std.U32 Std.U32) :
    pair_sum_mono p = pair_sum_mono.deep.denote (p ::ₑ .nil) := by deep_rfl

def pair_fst.deep : DeepExpr ⟨[], []⟩ [.adt (.crate TypeName.Pair) [U32T, U32T] []] U32T :=
  .proj (.crate TypeName.Pair) 0 [U32T, U32T] [] U32T rfl (.var .zero)

theorem pair_fst.deep_eq (p : Pair Std.U32 Std.U32) :
    pair_fst p = pair_fst.deep.denote (p ::ₑ .nil) := by deep_rfl

def mk_pair.deep : DeepExpr ⟨[], []⟩ [U32T, U32T] (.adt (.crate TypeName.Pair) [U32T, U32T] []) :=
  .ctor (.crate TypeName.Pair) 0 [U32T, U32T] [] [U32T, U32T] rfl (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem mk_pair.deep_eq (x y : Std.U32) :
    mk_pair x y = mk_pair.deep.denote (x ::ₑ y ::ₑ .nil) := by deep_rfl

/-! ## Primitives and builtin types -/

def arr_get.deep : DeepExpr ⟨[], []⟩ [.array U32T (.lit 4 (by decide)), .scalar (.u .Usize)] (.result U32T) :=
  .call (.prim .arrayIndex) [U32T] [.lit 4 (by decide)]
    [.array U32T (.lit 4 (by decide)), .scalar (.u .Usize)] (.result U32T) rfl rfl
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem arr_get.deep_eq (a : Array Std.U32 4#usize) (i : Std.Usize) :
    arr_get a i = arr_get.deep.denote (a ::ₑ i ::ₑ .nil) := by deep_rfl

def lift_add.deep : DeepExpr ⟨[], []⟩ [U32T, U32T] (.result U32T) :=
  .call (.prim .lift) [U32T] [] [U32T] (.result U32T) rfl rfl
    (.cons (.scalarBitop .and (.u .U32) (.var .zero) (.var (.succ .zero))) .nil)

theorem lift_add.deep_eq (x y : Std.U32) :
    lift_add x y = lift_add.deep.denote (x ::ₑ y ::ₑ .nil) := by deep_rfl

def opt_or.deep : DeepExpr ⟨[], []⟩ [.adt (.builtin .option) [U32T] [], U32T] U32T :=
  .match_ (.builtin .option) [U32T] [] [[], [U32T]] rfl (.var .zero)
    (.cons (.var (.succ .zero))
    (.cons (.var .zero)
    .nil))

theorem opt_or.deep_eq (o : Option Std.U32) (d : Std.U32) :
    opt_or o d = opt_or.deep.denote (o ::ₑ d ::ₑ .nil) := by deep_rfl

def mk_some.deep {T : Type} : DeepExpr ⟨[T], []⟩ [.var 0] (.adt (.builtin .option) [.var 0] []) :=
  .ctor (.builtin .option) 1 [.var 0] [] [.var 0] rfl (.cons (.var .zero) .nil)

theorem mk_some.deep_eq {T : Type} (x : T) :
    mk_some x = mk_some.deep.denote (x ::ₑ .nil) := by deep_rfl

def vec_len.deep {T : Type} : DeepExpr ⟨[T], []⟩ [.adt (.builtin .vec) [.var 0] []] (.scalar (.u .Usize)) :=
  .call (.prim .vecLen) [.var 0] [] [.adt (.builtin .vec) [.var 0] []] (.scalar (.u .Usize)) rfl rfl
    (.cons (.var .zero) .nil)

theorem vec_len.deep_eq {T : Type} (v : alloc.vec.Vec T) :
    vec_len v = vec_len.deep.denote (v ::ₑ .nil) := by deep_rfl

/-! ## Deep terms are inspectable: a trivial structural function -/

mutual
  def _root_.Aeneas.Deep.Expr.numBinds {N F G : Type} [TypeNames N] [FunNames F N]
      [GlobalNames G N] {σ : TyEnv} {Γ : List (Ty N)} {τ : Ty N} (e : Expr N F G σ Γ τ) : Nat :=
    match e with
    | .bind _ _ k => 1 + k.numBinds
    | .let_ e _ k => e.numBinds + k.numBinds
    | .app f a => f.numBinds + a.numBinds
    | .lam _ _ b => b.numBinds
    | .ite c t e => c.numBinds + t.numBinds + e.numBinds
    | .match_ _ (inst := _) _ _ _ _ s brs => s.numBinds + brs.numBinds
    | .ctor _ _ (inst := _) _ _ _ _ args => args.numBinds
    | .call _ _ _ _ _ _ _ args => args.numBinds
    | .tuple es => es.numBinds
    | .loop b i => b.numBinds + i.numBinds
    | _ => 0
  termination_by structural e
  def _root_.Aeneas.Deep.Exprs.numBinds {N F G : Type} [TypeNames N] [FunNames F N]
      [GlobalNames G N] {σ : TyEnv} {Γ : List (Ty N)} {tys : List (Ty N)}
      (es : Exprs N F G σ Γ tys) : Nat :=
    match es with
    | .nil => 0
    | .cons e es => e.numBinds + es.numBinds
  termination_by structural es
  def _root_.Aeneas.Deep.Cond.numBinds {N F G : Type} [TypeNames N] [FunNames F N]
      [GlobalNames G N] {σ : TyEnv} {Γ : List (Ty N)} (c : Cond N F G σ Γ) : Nat :=
    match c with
    | .bool b => b.numBinds
    | .not c => c.numBinds
    | .eq (inst := _inst) a b => a.numBinds + b.numBinds
    | .lt (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
    | .le (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
    | .gt (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
    | .ge (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
  termination_by structural c
  def _root_.Aeneas.Deep.Branches.numBinds {N F G : Type} [TypeNames N] [FunNames F N]
      [GlobalNames G N] {σ : TyEnv} {Γ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N}
      (brs : Branches N F G σ Γ shape τ) : Nat :=
    match brs with
    | .nil => 0
    | .cons b bs => b.numBinds + bs.numBinds
  termination_by structural brs
end

example : (list_nth_mut.deep (T := Unit)).numBinds = 2 := by rfl
example : sum_loop.body.deep.numBinds = 2 := by rfl

end Aeneas.Deep.Tests
