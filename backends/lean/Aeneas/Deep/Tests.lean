module
public import Aeneas.Deep.Basic
public import Aeneas.Deep.Tactic
public import Aeneas.Deep.IR
public import Aeneas.Deep.Compile
public import Aeneas.Deep.Tests.Shallow
public meta import Aeneas.Std
public meta import Aeneas.Deep.Basic
public meta import Aeneas.Deep.IR
public meta import Aeneas.Deep.Compile
public meta import Aeneas.Deep.Tests.Shallow
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
  deriving Repr

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
  | pair_swap
  deriving DecidableEq, Repr

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
    | .pair_swap =>
      ⟨⟨[.adt (.crate TypeName.Pair) [.var 0, .var 0] []], .adt (.crate TypeName.Pair) [.var 0, .var 0] []⟩,
       fun ρ => @pair_swap (tyAt ρ.types 0)⟩

inductive GlobalName where
  deriving Repr

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

/-! ## A generic function and its use at an instance -/

def pair_swap.deep {T : Type} :
    DeepExpr ⟨[T], []⟩ [.adt (.crate TypeName.Pair) [.var 0, .var 0] []]
      (.adt (.crate TypeName.Pair) [.var 0, .var 0] []) :=
  .ctor (.crate TypeName.Pair) 0 [.var 0, .var 0] [] [.var 0, .var 0] rfl
    (.cons (.proj (.crate TypeName.Pair) 1 [.var 0, .var 0] [] (.var 0) rfl (.var .zero))
      (.cons (.proj (.crate TypeName.Pair) 0 [.var 0, .var 0] [] (.var 0) rfl (.var .zero)) .nil))

theorem pair_swap.deep_eq {T : Type} (p : Pair T T) :
    pair_swap p = pair_swap.deep.denote (p ::ₑ .nil) := by deep_rfl

def use_pair_swap.deep : DeepExpr ⟨[], []⟩ [.adt (.crate TypeName.Pair) [U32T, U32T] []] U32T :=
  .proj (.crate TypeName.Pair) 0 [U32T, U32T] [] U32T rfl
    (.call (.crate FunName.pair_swap) [U32T] [] [.adt (.crate TypeName.Pair) [U32T, U32T] []]
      (.adt (.crate TypeName.Pair) [U32T, U32T] []) rfl rfl (.cons (.var .zero) .nil))

theorem use_pair_swap.deep_eq (p : Pair Std.U32 Std.U32) :
    use_pair_swap p = use_pair_swap.deep.denote (p ::ₑ .nil) := by deep_rfl

/-! ## Array literals -/

def arr_lit.deep : DeepExpr ⟨[], []⟩ [U32T, U32T] (.array U32T (.lit 2 (by decide))) :=
  .array U32T 2 (by decide) (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem arr_lit.deep_eq (x y : Std.U32) :
    arr_lit x y = arr_lit.deep.denote (x ::ₑ y ::ₑ .nil) := by deep_rfl

/-! ## The iterators over ranges -/

local notation "RangeU" =>
  Ty.adt (TypeRef.builtin BuiltinTy.range) [Ty.scalar (ScalarTy.u UScalarTy.Usize)] []
local notation "OptionU" =>
  Ty.adt (TypeRef.builtin BuiltinTy.option) [Ty.scalar (ScalarTy.u UScalarTy.Usize)] []
local notation "RevU" => Ty.adt (TypeRef.builtin BuiltinTy.rev) [RangeU] []
local notation "StepByU" => Ty.adt (TypeRef.builtin BuiltinTy.stepBy) [RangeU] []

def range_next.deep : DeepExpr ⟨[], []⟩ [RangeU] (.result (.tuple [OptionU, RangeU])) :=
  .call (.prim .rangeNextUsize) [] [] [RangeU] (.result (.tuple [OptionU, RangeU])) rfl rfl
    (.cons (.var .zero) .nil)

theorem range_next.deep_eq (r : core.ops.range.Range Std.Usize) :
    range_next r = range_next.deep.denote (r ::ₑ .nil) := by deep_rfl

def range_rev.deep : DeepExpr ⟨[], []⟩ [RangeU] (.result RevU) :=
  .call (.prim .rangeRevUsize) [] [] [RangeU] (.result RevU) rfl rfl (.cons (.var .zero) .nil)

theorem range_rev.deep_eq (r : core.ops.range.Range Std.Usize) :
    range_rev r = range_rev.deep.denote (r ::ₑ .nil) := by deep_rfl

def rev_next.deep : DeepExpr ⟨[], []⟩ [RevU] (.result (.tuple [OptionU, RevU])) :=
  .call (.prim .revRangeNextUsize) [] [] [RevU] (.result (.tuple [OptionU, RevU])) rfl rfl
    (.cons (.var .zero) .nil)

theorem rev_next.deep_eq (r : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) :
    rev_next r = rev_next.deep.denote (r ::ₑ .nil) := by deep_rfl

def range_step_by.deep : DeepExpr ⟨[], []⟩ [RangeU, .scalar (.u .Usize)] (.result StepByU) :=
  .call (.prim .rangeStepByUsize) [] [] [RangeU, .scalar (.u .Usize)] (.result StepByU) rfl rfl
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem range_step_by.deep_eq (r : core.ops.range.Range Std.Usize) (n : Std.Usize) :
    range_step_by r n = range_step_by.deep.denote (r ::ₑ n ::ₑ .nil) := by deep_rfl

def step_by_next.deep : DeepExpr ⟨[], []⟩ [StepByU] (.result (.tuple [OptionU, StepByU])) :=
  .call (.prim .stepByRangeNextUsize) [] [] [StepByU] (.result (.tuple [OptionU, StepByU])) rfl rfl
    (.cons (.var .zero) .nil)

theorem step_by_next.deep_eq
    (s : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize)) :
    step_by_next s = step_by_next.deep.denote (s ::ₑ .nil) := by deep_rfl

/-! ## The slice iterators -/

local notation "SliceU32" => Ty.slice (Ty.scalar (ScalarTy.u UScalarTy.U32))
local notation "IterU32" =>
  Ty.adt (TypeRef.builtin BuiltinTy.sliceIter) [Ty.scalar (ScalarTy.u UScalarTy.U32)] []
local notation "OptionU32" =>
  Ty.adt (TypeRef.builtin BuiltinTy.option) [Ty.scalar (ScalarTy.u UScalarTy.U32)] []

def slice_iter.deep : DeepExpr ⟨[], []⟩ [SliceU32] (.result IterU32) :=
  .call (.prim .sliceIter) [U32T] [] [SliceU32] (.result IterU32) rfl rfl (.cons (.var .zero) .nil)

theorem slice_iter.deep_eq (s : Slice Std.U32) :
    slice_iter s = slice_iter.deep.denote (s ::ₑ .nil) := by deep_rfl

def slice_into_iter.deep : DeepExpr ⟨[], []⟩ [SliceU32] (.result IterU32) :=
  .call (.prim .sliceIntoIter) [U32T] [] [SliceU32] (.result IterU32) rfl rfl
    (.cons (.var .zero) .nil)

theorem slice_into_iter.deep_eq (s : Slice Std.U32) :
    slice_into_iter s = slice_into_iter.deep.denote (s ::ₑ .nil) := by deep_rfl

def array_into_iter.deep : DeepExpr ⟨[], []⟩ [.array U32T (.lit 2 (by decide))] (.result IterU32) :=
  .call (.prim .arrayIntoIter) [U32T] [.lit 2 (by decide)] [.array U32T (.lit 2 (by decide))]
    (.result IterU32) rfl rfl (.cons (.var .zero) .nil)

theorem array_into_iter.deep_eq (a : Array Std.U32 2#usize) :
    array_into_iter a = array_into_iter.deep.denote (a ::ₑ .nil) := by deep_rfl

def slice_iter_next.deep : DeepExpr ⟨[], []⟩ [IterU32] (.result (.tuple [OptionU32, IterU32])) :=
  .call (.prim .sliceIterNext) [U32T] [] [IterU32] (.result (.tuple [OptionU32, IterU32])) rfl rfl
    (.cons (.var .zero) .nil)

theorem slice_iter_next.deep_eq (it : core.slice.iter.Iter Std.U32) :
    slice_iter_next it = slice_iter_next.deep.denote (it ::ₑ .nil) := by deep_rfl

/-! ## Mutable borrows: `let (x, back) ← index_mut v i; …; back x'` -/

def arr_incr.deep : DeepExpr ⟨[], []⟩ [.array U32T (.lit 4 (by decide)), .scalar (.u .Usize)]
    (.result (.array U32T (.lit 4 (by decide)))) :=
  .bind (.call (.prim .arrayIndexMut) [U32T] [.lit 4 (by decide)]
          [.array U32T (.lit 4 (by decide)), .scalar (.u .Usize)]
          (.result (.tuple [U32T, .arrow U32T (.array U32T (.lit 4 (by decide)))])) rfl rfl
          (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
    (.tuple (.cons .var (.cons .var .nil)))
    -- x=0, back=1, a=2, i=3
    (.bind (.scalarBinop .add (.u .U32) (.var .zero) (.uscalarLit .U32 1 (by decide))) .var
      -- x1=0, x=1, back=2, a=3, i=4
      (.ok (.app (.var (.succ (.succ .zero))) (.var .zero))))

theorem arr_incr.deep_eq (a : Array Std.U32 4#usize) (i : Std.Usize) :
    arr_incr a i = arr_incr.deep.denote (a ::ₑ i ::ₑ .nil) := by deep_rfl

def vec_set.deep : DeepExpr ⟨[], []⟩ [.adt (.builtin .vec) [U32T] [], .scalar (.u .Usize), U32T]
    (.result (.adt (.builtin .vec) [U32T] [])) :=
  .bind (.call (.prim .vecIndexMut) [U32T] [] [.adt (.builtin .vec) [U32T] [], .scalar (.u .Usize)]
          (.result (.tuple [U32T, .arrow U32T (.adt (.builtin .vec) [U32T] [])])) rfl rfl
          (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil)))
    (.tuple (.cons .ignore (.cons .var .nil)))
    -- back=0, v=1, i=2, x=3
    (.ok (.app (.var .zero) (.var (.succ (.succ (.succ .zero))))))

theorem vec_set.deep_eq (v : alloc.vec.Vec Std.U32) (i : Std.Usize) (x : Std.U32) :
    vec_set v i x = vec_set.deep.denote (v ::ₑ i ::ₑ x ::ₑ .nil) := by deep_rfl

def arr_borrow.deep : DeepExpr ⟨[], []⟩ [.array U32T (.lit 4 (by decide)), .scalar (.u .Usize)]
    (.result (.tuple [U32T, .arrow U32T (.array U32T (.lit 4 (by decide)))])) :=
  .call (.prim .arrayIndexMut) [U32T] [.lit 4 (by decide)]
    [.array U32T (.lit 4 (by decide)), .scalar (.u .Usize)]
    (.result (.tuple [U32T, .arrow U32T (.array U32T (.lit 4 (by decide)))])) rfl rfl
    (.cons (.var .zero) (.cons (.var (.succ .zero)) .nil))

theorem arr_borrow.deep_eq (a : Array Std.U32 4#usize) (i : Std.Usize) :
    arr_borrow a i = arr_borrow.deep.denote (a ::ₑ i ::ₑ .nil) := by deep_rfl

/-! ## Compilation to the IR

The hand-written terms are all in the first-order fragment: they compile, and the
interpreter of the IR agrees with the shallow functions on sample inputs. -/

open Compile in
/-- The result of running the compiled body of `e` on `env` -/
def execOn {Γ : List (Ty TypeName)} {τ : Ty TypeName} (e : DeepExpr ⟨[], []⟩ Γ τ)
    (env : Env TypeName ⟨[], []⟩ Γ) : Option (τ.denote ⟨[], []⟩) :=
  (compile e).toOption.map (fun s => s.exec env)

/-- Does the compiled body of `e` reduce to `expected` on `env` (`Result` is an interaction
tree: we observe it with `Result.reducesTo`)? -/
def reducesOn {Γ : List (Ty TypeName)} {ρ : Ty TypeName} [BEq (ρ.denote ⟨[], []⟩)]
    (e : DeepExpr ⟨[], []⟩ Γ (.result ρ)) (env : Env TypeName ⟨[], []⟩ Γ)
    (expected : ρ.denote ⟨[], []⟩) : Bool :=
  match execOn e env with
  | some r => Result.reducesTo r expected
  | none => false

example : (Compile.compile mul2_add1.deep).toBool = true := by decide
example : (Compile.compile use_incr.deep).toBool = true := by decide
/-- `choose` and `list_nth_mut` return closures: outside the first-order fragment -/
example : (Compile.compile (choose.deep (T := Unit))).toBool = false := by decide
example : (Compile.compile i32_id.deep).toBool = true := by decide
example : (Compile.compile (list_nth.deep (T := Unit))).toBool = true := by decide
example : (Compile.compile (list_nth_mut.deep (T := Unit))).toBool = false := by decide
example : (Compile.compile sum_loop.body.deep).toBool = true := by decide
example : (Compile.compile sum_loop.deep).toBool = true := by decide
example : (Compile.compile sum.deep).toBool = true := by decide
example : (Compile.compile pair_sum.deep).toBool = true := by decide
example : (Compile.compile pair_fst.deep).toBool = true := by decide
example : (Compile.compile mk_pair.deep).toBool = true := by decide
example : (Compile.compile arr_get.deep).toBool = true := by decide
example : (Compile.compile opt_or.deep).toBool = true := by decide
example : (Compile.compile (vec_len.deep (T := Unit))).toBool = true := by decide
example : (Compile.compile arr_incr.deep).toBool = true := by decide
example : (Compile.compile range_next.deep).toBool = true := by decide
example : (Compile.compile arr_lit.deep).toBool = true := by decide
example : (Compile.compile slice_iter.deep).toBool = true := by decide
example : (Compile.compile slice_into_iter.deep).toBool = true := by decide
example : (Compile.compile array_into_iter.deep).toBool = true := by decide
example : (Compile.compile slice_iter_next.deep).toBool = true := by decide
example : (Compile.compile range_rev.deep).toBool = true := by decide
example : (Compile.compile rev_next.deep).toBool = true := by decide
example : (Compile.compile range_step_by.deep).toBool = true := by decide
example : (Compile.compile step_by_next.deep).toBool = true := by decide
example : (Compile.compile (pair_swap.deep (T := Unit))).toBool = true := by decide
example : (Compile.compile use_pair_swap.deep).toBool = true := by decide
example : (Compile.compile vec_set.deep).toBool = true := by decide
/-- The backward function of the borrow escapes: rejected by the closure check -/
example : (match Compile.compile arr_borrow.deep with
    | .error .closureVar => true
    | _ => false) = true := by decide

example : reducesOn mul2_add1.deep (3#u32 ::ₑ .nil) 7#u32 := by native_decide
example : reducesOn i32_id.deep (2#i32 ::ₑ .nil) 2#i32 := by native_decide
example : reducesOn sum.deep (4#u32 ::ₑ .nil) 12#u32 := by native_decide
example : reducesOn pair_sum.deep (⟨1#u32, 2#u32⟩ ::ₑ .nil) 3#u32 := by native_decide
example : execOn opt_or.deep (none ::ₑ 5#u32 ::ₑ .nil) = some 5#u32 := by decide +kernel
example : execOn opt_or.deep (some 1#u32 ::ₑ 5#u32 ::ₑ .nil) = some 1#u32 := by decide +kernel
example : reducesOn arr_incr.deep (Array.repeat 4#usize 0#u32 ::ₑ 1#usize ::ₑ .nil)
    (Std.Array.set (Array.repeat 4#usize 0#u32) 1#usize 1#u32) := by native_decide
example : (execOn arr_lit.deep (1#u32 ::ₑ 2#u32 ::ₑ .nil)).map (·.val) = some [1#u32, 2#u32] := by
  decide +kernel

/-- The calls of a compiled body -/
example : (Compile.compile sum.deep).toOption.map (fun s => s.calls.map (·.f)) =
    some [.crate .sum_loop] := by decide

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
