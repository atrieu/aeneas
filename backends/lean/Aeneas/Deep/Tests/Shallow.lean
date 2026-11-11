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

end Aeneas.Deep.Tests.Shallow
