module
import Aeneas.Deep.Basic
import Aeneas.Deep.Tactic
import Aeneas.Deep.Tests.Shallow

/-! Hand-written deep terms for the definitions of `Aeneas.Deep.Tests.Shallow`, with the
denotation theorems. This is the phase 1 spike of the deep printing mode: it checks that
the denotation of every construct reduces to what the elaborator produces for the shallow
code, across a module boundary. -/

open Aeneas Aeneas.Std Result ControlFlow Error
open Aeneas.Deep

namespace Aeneas.Deep.Tests
open Shallow

/- Shallow operators, written the way the deep printer would print them -/
abbrev addU32 : Std.U32 → Std.U32 → Result Std.U32 := HAdd.hAdd
abbrev subU32 : Std.U32 → Std.U32 → Result Std.U32 := HSub.hSub
abbrev mulU32 : Std.U32 → Std.U32 → Result Std.U32 := HMul.hMul
abbrev addI32 : Std.I32 → Std.I32 → Result Std.I32 := HAdd.hAdd
abbrev subI32 : Std.I32 → Std.I32 → Result Std.I32 := HSub.hSub

/-! ## Contract checks

To look at the elaborated shallow terms, uncomment:
```
set_option pp.explicit true in #print sum_loop.body
set_option pp.explicit true in #print list_nth_mut
```
-/

/-! ## Bind chain -/

def mul2_add1.deep : Expr [Std.U32] (Result Std.U32) :=
  .bind (.binop "add" addU32 (.var .zero) (.var .zero)) .var
    (.binop "add" addU32 (.var .zero) (.lit 1#u32))

theorem mul2_add1.deep_eq (x : Std.U32) :
    mul2_add1 x = mul2_add1.deep.denote (x ::ₕ .nil) := by rfl

def use_mul2_add1.deep : Expr [Std.U32, Std.U32] (Result Std.U32) :=
  .bind (.app (.call "mul2_add1" mul2_add1) (.var .zero)) .var
    (.binop "add" addU32 (.var .zero) (.var (.succ (.succ .zero))))

theorem use_mul2_add1.deep_eq (x y : Std.U32) :
    use_mul2_add1 x y = use_mul2_add1.deep.denote (x ::ₕ y ::ₕ .nil) := by rfl

/-! ## Ignored unit binds -/

def use_incr.deep : Expr [] (Result Unit) :=
  .bind (.app (.call "incr" incr) (.lit 0#u32)) .var
    (.bind (.app (.call "incr" incr) (.var .zero)) .var
      (.bind (.app (.call "incr" incr) (.var .zero)) .ignore
        (.ok (.lit ()))))

theorem use_incr.deep_eq : use_incr = use_incr.deep.denote .nil := by rfl

/-! ## If on a boolean, pure let, lambda, backward function -/

def choose.deep {T : Type} : Expr [Bool, T, T] (Result (T × (T → (T × T)))) :=
  .ite (.bool (.var .zero))
    (.let_ (.lam .var (.pair (.var .zero) (.var (.succ (.succ (.succ .zero)))))) .var
      (.ok (.pair (.var (.succ (.succ .zero))) (.var .zero))))
    (.let_ (.lam .var (.pair (.var (.succ (.succ .zero))) (.var .zero))) .var
      (.ok (.pair (.var (.succ (.succ (.succ .zero)))) (.var .zero))))

theorem choose.deep_eq {T : Type} (b : Bool) (x y : T) :
    choose b x y = choose.deep.denote (b ::ₕ x ::ₕ y ::ₕ .nil) := by rfl

/-! ## Recursive function with an `if` on scalar equality -/

def i32_id.deep : Expr [Std.I32] (Result Std.I32) :=
  .ite (.eq (.var .zero) (.lit 0#i32))
    (.ok (.lit 0#i32))
    (.bind (.binop "sub" subI32 (.var .zero) (.lit 1#i32)) .var
      (.bind (.app (.call "i32_id" i32_id) (.var .zero)) .var
        (.binop "add" addI32 (.var .zero) (.lit 1#i32))))

theorem i32_id.deep_eq (i : Std.I32) :
    i32_id i = i32_id.deep.denote (i ::ₕ .nil) := by
  unfold i32_id; rfl

/-! ## Match on a user ADT, recursion -/

@[reducible] def CList.deepElim {T : Type} : Elim (CList T) [[T, CList T], []] :=
  fun l alts => CList.casesOn l alts.1 alts.2.1

def list_nth.deep {T : Type} : Expr [CList T, Std.U32] (Result T) :=
  .match_ (.var .zero) CList.deepElim
    (.cons -- CCons x tl: x=0, tl=1, l=2, i=3
      (.ite (.eq (.var (.succ (.succ (.succ .zero)))) (.lit 0#u32))
        (.ok (.var .zero))
        (.bind (.binop "sub" subU32 (.var (.succ (.succ (.succ .zero)))) (.lit 1#u32)) .var
          -- i1=0, x=1, tl=2, l=3, i=4
          (.app2 (.call "list_nth" list_nth) (.var (.succ (.succ .zero))) (.var .zero))))
      (.cons -- CNil
        (.fail panic)
        .nil))

theorem list_nth.deep_eq {T : Type} (l : CList T) (i : Std.U32) :
    list_nth l i = list_nth.deep.denote (l ::ₕ i ::ₕ .nil) := by
  unfold list_nth; deep_rfl

theorem list_nth.deep_eq_meta {T : Type} (l : CList T) (i : Std.U32) :
    list_nth l i = list_nth.deep.denote (l ::ₕ i ::ₕ .nil) := by
  unfold list_nth; deep_rfl_meta

/-! ## Match, tuple pattern in a monadic let, nested lets under a lambda -/

def list_nth_mut.deep {T : Type} : Expr [CList T, Std.U32] (Result (T × (T → CList T))) :=
  .match_ (.var .zero) CList.deepElim
    (.cons -- CCons x tl: x=0, tl=1, l=2, i=3
      (.ite (.eq (.var (.succ (.succ (.succ .zero)))) (.lit 0#u32))
        -- let back := fun t => CList.CCons t tl   (t=0, x=1, tl=2, l=3, i=4)
        (.let_ (.lam .var (.app2 (.ctor "CList.CCons" CList.CCons) (.var .zero) (.var (.succ (.succ .zero))))) .var
          -- back=0, x=1, tl=2, l=3, i=4
          (.ok (.pair (.var (.succ .zero)) (.var .zero))))
        (.bind (.binop "sub" subU32 (.var (.succ (.succ (.succ .zero)))) (.lit 1#u32)) .var
          -- i1=0, x=1, tl=2, l=3, i=4
          (.bind (.app2 (.call "list_nth_mut" list_nth_mut) (.var (.succ (.succ .zero))) (.var .zero))
            (.pair .var .var)
            -- x1=0, back'=1, i1=2, x=3, tl=4, l=5, i=6
            (.let_
              (.lam .var
                -- t=0, x1=1, back'=2, i1=3, x=4, tl=5, l=6, i=7
                (.let_ (.app (.var (.succ (.succ .zero))) (.var .zero)) .var
                  -- tl1=0, t=1, x1=2, back'=3, i1=4, x=5, tl=6, l=7, i=8
                  (.app2 (.ctor "CList.CCons" CList.CCons)
                    (.var (.succ (.succ (.succ (.succ (.succ .zero)))))) (.var .zero))))
              .var
              -- back=0, x1=1, back'=2, i1=3, x=4, tl=5, l=6, i=7
              (.ok (.pair (.var (.succ .zero)) (.var .zero)))))))
      (.cons (.fail panic) .nil))

theorem list_nth_mut.deep_eq {T : Type} (l : CList T) (i : Std.U32) :
    list_nth_mut l i = list_nth_mut.deep.denote (l ::ₕ i ::ₕ .nil) := by
  unfold list_nth_mut; deep_rfl

theorem list_nth_mut.deep_eq_meta {T : Type} (l : CList T) (i : Std.U32) :
    list_nth_mut l i = list_nth_mut.deep.denote (l ::ₕ i ::ₕ .nil) := by
  unfold list_nth_mut; deep_rfl_meta

/-! ## Loops: `<` on scalars, control flow constructors, tuple lambda, `loop` -/

def sum_loop.body.deep :
    Expr [Std.U32, Std.U32, Std.U32] (Result (ControlFlow (Std.U32 × Std.U32) Std.U32)) :=
  -- max=0, i=1, s=2
  .ite (.lt (.var (.succ .zero)) (.var .zero))
    (.bind (.binop "add" addU32 (.var (.succ (.succ .zero))) (.var (.succ .zero))) .var
      -- s1=0, max=1, i=2, s=3
      (.bind (.binop "add" addU32 (.var (.succ (.succ .zero))) (.lit 1#u32)) .var
        -- i1=0, s1=1, max=2, i=3, s=4
        (.ok (.app (.ctor "cont" ControlFlow.cont) (.pair (.var .zero) (.var (.succ .zero)))))))
    (.ok (.app (.ctor "done" ControlFlow.done) (.var (.succ (.succ .zero)))))

theorem sum_loop.body.deep_eq (max i s : Std.U32) :
    sum_loop.body max i s = sum_loop.body.deep.denote (max ::ₕ i ::ₕ s ::ₕ .nil) := by rfl

def sum_loop.deep : Expr [Std.U32, Std.U32, Std.U32] (Result Std.U32) :=
  .loop
    (.lam (.pair .var .var)
      -- i1=0, s1=1, max=2, i=3, s=4
      (.app3 (.call "sum_loop.body" sum_loop.body) (.var (.succ (.succ .zero))) (.var .zero) (.var (.succ .zero))))
    (.pair (.var (.succ .zero)) (.var (.succ (.succ .zero))))

theorem sum_loop.deep_eq (max i s : Std.U32) :
    sum_loop max i s = sum_loop.deep.denote (max ::ₕ i ::ₕ s ::ₕ .nil) := by rfl

def sum.deep : Expr [Std.U32] (Result Std.U32) :=
  .bind (.app3 (.call "sum_loop" sum_loop) (.var .zero) (.lit 0#u32) (.lit 0#u32)) .var
    (.binop "mul" mulU32 (.var .zero) (.lit 2#u32))

theorem sum.deep_eq (max : Std.U32) :
    sum max = sum.deep.denote (max ::ₕ .nil) := by rfl

/-! ## Deep terms are inspectable: a trivial structural function -/

mutual
  def _root_.Aeneas.Deep.Expr.numBinds {Γ : List Type} {τ : Type} (e : Expr Γ τ) : Nat :=
    match e with
    | .bind _ _ k => 1 + k.numBinds
    | .let_ e _ k => e.numBinds + k.numBinds
    | .app f a => f.numBinds + a.numBinds
    | .lam _ b => b.numBinds
    | .ite c t e => c.numBinds + t.numBinds + e.numBinds
    | .match_ s _ brs => s.numBinds + brs.numBinds
    | .loop b i => b.numBinds + i.numBinds
    | _ => 0
  termination_by structural e
  def _root_.Aeneas.Deep.Cond.numBinds {Γ : List Type} (c : Cond Γ) : Nat :=
    match c with
    | .bool b => b.numBinds
    | .eq (inst := _inst) a b => a.numBinds + b.numBinds
    | .lt (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
    | .le (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
    | .gt (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
    | .ge (ord := _ord) (inst := _inst) a b => a.numBinds + b.numBinds
  termination_by structural c
  def _root_.Aeneas.Deep.Branches.numBinds {Γ : List Type} {shape : List (List Type)} {τ : Type}
      (brs : Branches Γ shape τ) : Nat :=
    match brs with
    | .nil => 0
    | .cons b bs => b.numBinds + bs.numBinds
  termination_by structural brs
end

set_option linter.hashCommand false in
#guard (list_nth_mut.deep (T := Unit)).numBinds == 2
set_option linter.hashCommand false in
#guard sum_loop.body.deep.numBinds == 2
example : (list_nth_mut.deep (T := Unit)).numBinds = 2 := by rfl


/-! ## Struct patterns (printed as single-branch matches)

Matches with a default branch (`| _ => ...`) are *not* supported: Lean compiles them to an
auxiliary `_sparseCasesOn` definition built on `T.rec` with a non-constant motive, which is not
definitionally equal to the `T.casesOn` of a deep eliminator. The printer uses the escape hatch
for them. -/

@[reducible] def Pair.deepElim {T1 T2 : Type} : Elim (Pair T1 T2) [[T1, T2]] :=
  fun p alts => Pair.casesOn p alts.1

def pair_sum.deep : Expr [Pair Std.U32 Std.U32] (Result Std.U32) :=
  .match_ (.var .zero) Pair.deepElim
    (.cons (.binop "add" addU32 (.var .zero) (.var (.succ .zero))) .nil)

theorem pair_sum.deep_eq (p : Pair Std.U32 Std.U32) :
    pair_sum p = pair_sum.deep.denote (p ::ₕ .nil) := by deep_rfl

def pair_sum_mono.deep : Expr [Pair Std.U32 Std.U32] (Result Std.U32) :=
  .bind (.ok (.var .zero)) .var
    (.match_ (.var .zero) Pair.deepElim
      (.cons (.binop "add" addU32 (.var .zero) (.var (.succ .zero))) .nil))

theorem pair_sum_mono.deep_eq (p : Pair Std.U32 Std.U32) :
    pair_sum_mono p = pair_sum_mono.deep.denote (p ::ₕ .nil) := by deep_rfl

end Aeneas.Deep.Tests
