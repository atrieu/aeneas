module
public import Aeneas.Std
public import Aeneas.Do.Elab
@[expose] public section

/-! Shallow definitions copied from the generated tests (`tests/lean/Demo/Demo.lean` and
`tests/lean/Loops.lean`), in a module of their own so that the deep terms and theorems in
`Aeneas.Deep.Tests` exercise the cross-module situation of the real generated code. -/

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace Aeneas.Deep.Tests.Shallow

def choose
  {T : Type _} (b : Bool) (x : T) (y : T) :
  Result (T × (T → (T × T)))
  := do
  if b
  then let back := fun x1 => (x1, y)
       ok (x, back)
  else let back := fun y1 => (x, y1)
       ok (y, back)

def mul2_add1 (x : Std.U32) : Result Std.U32 := do
  let i ← x + x
  i + 1#u32

def use_mul2_add1 (x : Std.U32) (y : Std.U32) : Result Std.U32 := do
  let i ← mul2_add1 x
  i + y

def incr (x : Std.U32) : Result Std.U32 := do
  x + 1#u32

def use_incr : Result Unit := do
  let x ← incr 0#u32
  let x1 ← incr x
  let _ ← incr x1
  ok ()

inductive CList (T : Type _) where
| CCons : T → CList T → CList T
| CNil : CList T

def list_nth {T : Type _} (l : CList T) (i : Std.U32) : Result T := do
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then ok x
    else let i1 ← i - 1#u32
         list_nth tl i1
  | CList.CNil => fail panic
partial_fixpoint

def list_nth_mut
  {T : Type _} (l : CList T) (i : Std.U32) :
  Result (T × (T → CList T))
  := do
  match l with
  | CList.CCons x tl =>
    if i = 0#u32
    then let back := fun t => CList.CCons t tl
         ok (x, back)
    else
      let i1 ← i - 1#u32
      let (x1, list_nth_mut_back) ← list_nth_mut tl i1
      let back := fun t => let tl1 := list_nth_mut_back t
                           CList.CCons x tl1
      ok (x1, back)
  | CList.CNil => fail panic
partial_fixpoint

def i32_id (i : Std.I32) : Result Std.I32 := do
  if i = 0#i32
  then ok 0#i32
  else let i1 ← i - 1#i32
       let i2 ← i32_id i1
       i2 + 1#i32
partial_fixpoint

def sum_loop.body
  (max : Std.U32) (i : Std.U32) (s : Std.U32) :
  Result (ControlFlow (Std.U32 × Std.U32) Std.U32)
  := do
  if i < max
  then let s1 ← s + i
       let i1 ← i + 1#u32
       ok (cont (i1, s1))
  else ok (done s)

def sum_loop (max : Std.U32) (i : Std.U32) (s : Std.U32) : Result Std.U32 := do
  loop
    (fun (i1, s1) => sum_loop.body max i1 s1)
    (i, s)

def sum (max : Std.U32) : Result Std.U32 := do
  let s ← sum_loop max 0#u32 0#u32
  s * 2#u32

/-! Struct patterns -/

structure Pair (T1 : Type _) (T2 : Type _) where
  x : T1
  y : T2

def pair_sum (p : Pair Std.U32 Std.U32) : Result Std.U32 := do
  let ⟨ a, b ⟩ := p
  a + b

def pair_sum_mono (p : Pair Std.U32 Std.U32) : Result Std.U32 := do
  let ⟨ a, b ⟩ ← ok p
  a + b

/-! Constructors and projections -/

def pair_fst (p : Pair Std.U32 Std.U32) : Std.U32 := p.x

def mk_pair (x : Std.U32) (y : Std.U32) : Pair Std.U32 Std.U32 := { x := x, y := y }

def mk_cons {T : Type _} (x : T) (tl : CList T) : CList T := CList.CCons x tl

/-! Primitives and builtin types -/

def arr_get (a : Array Std.U32 4#usize) (i : Std.Usize) : Result Std.U32 :=
  Array.index_usize a i

def lift_add (x : Std.U32) (y : Std.U32) : Result Std.U32 := lift (x &&& y)

def opt_or (o : Option Std.U32) (d : Std.U32) : Std.U32 :=
  match o with
  | none => d
  | some x => x

def mk_some {T : Type _} (x : T) : Option T := some x

def vec_len {T : Type _} (v : alloc.vec.Vec T) : Std.Usize := alloc.vec.Vec.len v

/-- The borrow idiom of the translation: `a[i] += 1` -/
def arr_incr (a : Array Std.U32 4#usize) (i : Std.Usize) : Result (Array Std.U32 4#usize) := do
  let (x, index_mut_back) ← Array.index_mut_usize a i
  let x1 ← x + 1#u32
  ok (index_mut_back x1)

/-- `v[i] = x` on a vector -/
def vec_set (v : alloc.vec.Vec Std.U32) (i : Std.Usize) (x : Std.U32) :
    Result (alloc.vec.Vec Std.U32) := do
  let (_, index_mut_back) ←
    alloc.vec.Vec.index_mut (core.slice.index.SliceIndexUsizeSlice Std.U32) v i
  ok (index_mut_back x)

/-- A generic function, printed by the C printer at the instances reachable from the
closed functions (`use_pair_swap`) -/
def pair_swap {T : Type _} (p : Pair T T) : Pair T T := { x := p.y, y := p.x }

def use_pair_swap (p : Pair Std.U32 Std.U32) : Std.U32 := (pair_swap p).x

/-- An array literal, as the shallow printer prints it -/
def arr_lit (x y : Std.U32) : Array Std.U32 2#usize := Array.make 2#usize [ x, y ]

/-! The iterators over ranges: the primitives, as the shallow printer calls them -/

def range_next (r : core.ops.range.Range Std.Usize) :
    Result (Option Std.Usize × core.ops.range.Range Std.Usize) :=
  core.iter.range.IteratorRange.next core.iter.range.StepUsize r

def range_rev (r : core.ops.range.Range Std.Usize) :
    Result (core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) :=
  core.iter.traits.iterator.Iterator.rev.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r

def rev_next (r : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) :
    Result (Option Std.Usize × core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize)) :=
  core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
    (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r

def range_step_by (r : core.ops.range.Range Std.Usize) (n : Std.Usize) :
    Result (core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize)) :=
  core.iter.traits.iterator.Iterator.step_by.trait_default
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) r n

def step_by_next (s : core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize)) :
    Result (Option Std.Usize × core.iter.adapters.step_by.StepBy (core.ops.range.Range Std.Usize)) :=
  core.iter.adapters.step_by.IteratorStepBy.next
    (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize) s

/-! The slice iterators: the primitives, as the shallow printer calls them -/

def slice_iter (s : Slice Std.U32) : Result (core.slice.iter.Iter Std.U32) :=
  core.slice.Slice.iter s

def slice_into_iter (s : Slice Std.U32) : Result (core.slice.iter.Iter Std.U32) :=
  SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter s

def array_into_iter (a : Array Std.U32 2#usize) : Result (core.slice.iter.Iter Std.U32) :=
  SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter a

def slice_iter_next (it : core.slice.iter.Iter Std.U32) :
    Result (Option Std.U32 × core.slice.iter.Iter Std.U32) :=
  core.slice.iter.IteratorSliceIter.next it

/-- A borrow whose backward function escapes: not in the fragment of the compiler -/
def arr_borrow (a : Array Std.U32 4#usize) (i : Std.Usize) :
    Result (Std.U32 × (Std.U32 → Array Std.U32 4#usize)) :=
  Array.index_mut_usize a i

end Aeneas.Deep.Tests.Shallow
