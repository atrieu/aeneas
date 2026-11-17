module
public import Aeneas.Deep.Basic
public import Aeneas.Deep.IR
public import Aeneas.Deep.Compile
@[expose] public section

/-! # The trusted C printer

A function from the IR (`Aeneas.Deep.IR`) to C text. Nothing here is verified: the printer
is the trusted part of the pipeline of `PLAN-compiler.md` (section 7), kept small and
written as plainly as possible so that it can be reviewed, and checked by differential
testing. What it decides, and is trusted for:

- **Types.** Scalars to the `<stdint.h>` types (`usize` to `size_t`, `isize` to
  `ptrdiff_t`, 128-bit scalars to the `__int128` extension); `Bool` to `bool`; `Unit` to
  `unit_t` (a byte); tuples and the ADTs of the closed world to `struct`s (a tag and a
  union of field structs for the types with several variants); `Array α n` to a struct
  holding a C array (so that assignment copies); `Slice α` and `Vec α` to a pointer and a
  length (and a capacity): **views**, updated in place; `ControlFlow` to a tagged union.
  The target is assumed 64-bit (`size_t` is 64 bits). The opaque types of the closed
  world (external types) are defined by the table `externals` given to the printer, or
  refused. Recursive types, strings and closures as values are not supported.
- **Instances.** A generic function is printed once per instance reachable from the
  closed functions (and the requested entries): the type and const-generic parameters
  (`Ty.var i`, `CArg.var i`) are resolved through the environment of the instance, and the
  instance is named after its arguments (`list_nth__u32`).
- **Calling convention.** A function returning `Result τ` returns an error code (`int`,
  `AENEAS_OK` is `0`) and writes its value to an out-parameter (none for `Result Unit`); a
  pure function returns its value. `fail` returns the code; `assert` checks and returns.
  Calls propagate the code. Globals are nullary functions.
- **Primitives.** The checked arithmetic uses `__builtin_*_overflow`; division and
  remainder check the divisor (and `MIN / -1`); shifts check the amount and are computed
  in the unsigned type; casts are C casts (two's complement); `index`/`update`/`push`
  check the bounds and copy the container (arrays) or write in place (slices, vectors);
  the iterators over ranges (`Range<usize>::next`, `rev`, `Rev::next`, `step_by`,
  `StepBy::next`) compare the bounds and step the start or the end; the slice iterators
  (`iter`, `into_iter`, `Iter::next`) are the slice view and an index.
- **Borrows.** A `borrow` reads the element (with its bounds check) and records the
  container and the index; the application of the backward function (`appVar`) copies
  the container (arrays) and stores the new element, or stores in place (slices and
  vectors, whose old value is then updated too: the realisation assumes, as Rust does,
  that the old value is dead).
- **Memory.** Vectors grow with `realloc` and are never freed.

The driver (`#deep_c`, `Aeneas.Deep.CDriver`) packages the deep terms of a crate
(`AnyDeep`) and runs `program`, which prints the reachable instances and assembles the
translation unit. -/

namespace Aeneas.Deep.CPrint

open Aeneas.Std Aeneas.Deep.IR Aeneas.Deep.Compile

instance {N : Type} : Inhabited (Ty N) := ⟨.unit⟩

/-! ## Names -/

/-- A C identifier from the name of a constructor of one of the generated enumerations
(`FunName.foo` → `foo`; the quote of Lean identifiers becomes `_q`) -/
def ctorName {α : Type} [Repr α] (x : α) : String :=
  let s := reprStr x
  let s := (s.splitOn ".").getLastD s
  String.join (s.toList.map fun c => if c == '\'' then "_q" else c.toString)

def mangleU : UScalarTy → String
  | .U8 => "u8" | .U16 => "u16" | .U32 => "u32" | .U64 => "u64" | .U128 => "u128"
  | .Usize => "usize"

def mangleI : IScalarTy → String
  | .I8 => "i8" | .I16 => "i16" | .I32 => "i32" | .I64 => "i64" | .I128 => "i128"
  | .Isize => "isize"

def mangleScalar : ScalarTy → String
  | .u t => mangleU t
  | .i t => mangleI t

def mangleBuiltin : BuiltinTy → String
  | .option => "option" | .vec => "vec" | .range => "range" | .ordering => "ordering"
  | .rev => "rev" | .stepBy => "stepBy" | .sliceIter => "sliceIter"

def mangleCArg : CArg → String
  | .lit n _ => toString n
  | .var i => s!"N{i}"

/-- The C name of a type (and of its `struct`) -/
partial def mangle {N : Type} [Repr N] : Ty N → String
  | .var i => s!"T{i}"
  | .scalar t => mangleScalar t
  | .bool => "bool"
  | .char => "char32"
  | .unit => "unit"
  | .str => "str"
  | .tuple tys => s!"tup{tys.length}_" ++ "_".intercalate (tys.map mangle)
  | .adt T targs cargs =>
    let base := match T with
      | .builtin b => mangleBuiltin b
      | .crate n => ctorName n
    if targs.isEmpty && cargs.isEmpty then base
    else base ++ "__" ++ "_".intercalate (targs.map mangle ++ cargs.map mangleCArg)
  | .array τ n => s!"arr_{mangle τ}_{mangleCArg n}"
  | .slice τ => s!"slice_{mangle τ}"
  | .result τ => s!"res_{mangle τ}"
  | .controlFlow a b => s!"cf_{mangle a}_{mangle b}"
  | .arrow a b => s!"fn_{mangle a}_{mangle b}"

/-- The C name of a function instance -/
def funName {N : Type} [Repr N] (base : String) (targs : List (Ty N)) (cargs : List CArg) :
    String :=
  if targs.isEmpty && cargs.isEmpty then base
  else base ++ "__" ++ "_".intercalate (targs.map mangle ++ cargs.map mangleCArg)

/-! ## Scalars -/

def cNameU : UScalarTy → String
  | .U8 => "uint8_t" | .U16 => "uint16_t" | .U32 => "uint32_t" | .U64 => "uint64_t"
  | .U128 => "u128_t" | .Usize => "size_t"

def cNameI : IScalarTy → String
  | .I8 => "int8_t" | .I16 => "int16_t" | .I32 => "int32_t" | .I64 => "int64_t"
  | .I128 => "i128_t" | .Isize => "ptrdiff_t"

def cNameScalar : ScalarTy → String
  | .u t => cNameU t
  | .i t => cNameI t

def bitsU : UScalarTy → Nat
  | .U8 => 8 | .U16 => 16 | .U32 => 32 | .U64 => 64 | .U128 => 128 | .Usize => 64

def bitsI : IScalarTy → Nat
  | .I8 => 8 | .I16 => 16 | .I32 => 32 | .I64 => 64 | .I128 => 128 | .Isize => 64

def bits : ScalarTy → Nat
  | .u t => bitsU t
  | .i t => bitsI t

/-- The unsigned type of the same width -/
def unsignedOf : ScalarTy → UScalarTy
  | .u t => t
  | .i .I8 => .U8 | .i .I16 => .U16 | .i .I32 => .U32 | .i .I64 => .U64 | .i .I128 => .U128
  | .i .Isize => .Usize

/-- The C expression of the minimum of a signed type -/
def minI : IScalarTy → String
  | .I8 => "INT8_MIN" | .I16 => "INT16_MIN" | .I32 => "INT32_MIN" | .I64 => "INT64_MIN"
  | .I128 => "AENEAS_I128_MIN" | .Isize => "PTRDIFF_MIN"

def uLit (ty : UScalarTy) (n : Nat) : String :=
  match ty with
  | .U128 =>
    if n < 2 ^ 64 then s!"((u128_t)UINT64_C({n}))"
    else s!"((((u128_t)UINT64_C({n / 2 ^ 64})) << 64) | (u128_t)UINT64_C({n % 2 ^ 64}))"
  | .U64 => s!"UINT64_C({n})"
  | .Usize => s!"((size_t)UINT64_C({n}))"
  | t => s!"(({cNameU t}){n})"

def iLit (ty : IScalarTy) (n : Int) : String :=
  if n < 0 && n == IScalar.cMin ty then minI ty
  else
    let m := n.natAbs
    let pos := match ty with
      | .I128 =>
        if m < 2 ^ 64 then s!"((i128_t)INT64_C({m}))"
        else s!"((i128_t)((((u128_t)UINT64_C({m / 2 ^ 64})) << 64) | (u128_t)UINT64_C({m % 2 ^ 64})))"
      | .I64 => s!"INT64_C({m})"
      | .Isize => s!"((ptrdiff_t)INT64_C({m}))"
      | t => s!"(({cNameI t}){m})"
    if n < 0 then s!"(-{pos})" else pos

def errCode : Error → String
  | .assertionFailure => "AENEAS_ASSERTION_FAILURE"
  | .integerOverflow => "AENEAS_INTEGER_OVERFLOW"
  | .divisionByZero => "AENEAS_DIVISION_BY_ZERO"
  | .arrayOutOfBounds => "AENEAS_ARRAY_OUT_OF_BOUNDS"
  | .maximumSizeExceeded => "AENEAS_MAXIMUM_SIZE_EXCEEDED"
  | .panic => "AENEAS_PANIC"
  | .undef => "AENEAS_UNDEF"

/-- The prelude of every translation unit -/
def prelude : String := "\
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

typedef uint8_t unit_t;
typedef unsigned __int128 u128_t;
typedef __int128 i128_t;
#define AENEAS_I128_MIN (-(i128_t)(((u128_t)1 << 127) - 1) - 1)

enum aeneas_error {
  AENEAS_OK = 0,
  AENEAS_ASSERTION_FAILURE,
  AENEAS_INTEGER_OVERFLOW,
  AENEAS_DIVISION_BY_ZERO,
  AENEAS_ARRAY_OUT_OF_BOUNDS,
  AENEAS_MAXIMUM_SIZE_EXCEEDED,
  AENEAS_PANIC,
  AENEAS_UNDEF
};
"

/-! ## Type descriptors -/

def substCArg (cargs : List CArg) : CArg → CArg
  | .var i => cargs.getD i (.var i)
  | c => c

/-- The instantiation of a descriptor over the parameters of a declaration -/
partial def subst {N : Type} (targs : List (Ty N)) (cargs : List CArg) : Ty N → Ty N
  | .var i => targs.getD i (.var i)
  | .tuple tys => .tuple (tys.map (subst targs cargs))
  | .adt T ts cs => .adt T (ts.map (subst targs cargs)) (cs.map (substCArg cargs))
  | .array τ n => .array (subst targs cargs τ) (substCArg cargs n)
  | .slice τ => .slice (subst targs cargs τ)
  | .result τ => .result (subst targs cargs τ)
  | .controlFlow a b => .controlFlow (subst targs cargs a) (subst targs cargs b)
  | .arrow a b => .arrow (subst targs cargs a) (subst targs cargs b)
  | t => t

def isUnit {N : Type} : Ty N → Bool
  | .unit => true
  | _ => false

/-- The types C compares with `==` -/
def isComparable {N : Type} : Ty N → Bool
  | .scalar _ | .bool | .char => true
  | _ => false

/-! ## The printing monad -/

/-- What a closure variable stands for: the backward function of a borrow -/
structure BorrowInfo where
  kind : MutIndex
  /-- The C variable holding the container at the borrow -/
  cont : String
  /-- The C variable holding the index -/
  idx : String
  /-- The C type of the container -/
  contTy : String

structure VarInfo where
  name : String
  borrow : Option BorrowInfo := none

/-- The naming context: one entry per variable of `Γ`, innermost first -/
structure Ctx where
  vars : List VarInfo := []

def Ctx.extend (ctx : Ctx) (vs : List VarInfo) : Ctx := { vars := vs ++ ctx.vars }

/-- A function instance: the base name and the arguments -/
structure Instance (N : Type) where
  base : String
  targs : List (Ty N)
  cargs : List CArg

structure PState (N : Type) where
  fresh : Nat := 0
  /-- The instance being printed: the interpretation of `Ty.var i` and `CArg.var i` -/
  tenv : List (Ty N) := []
  cenv : List CArg := []
  /-- The C definitions of the opaque types (by C name) -/
  externals : List (String × String) := []
  /-- The type definitions needed so far, in dependency order (C name, definition) -/
  types : Array (String × String) := #[]
  /-- The names of the types defined so far, and of those being defined -/
  defined : List String := []
  inProgress : List String := []
  /-- The prototypes of the callees (C name, prototype) -/
  protos : Array (String × String) := #[]
  /-- The instances of the functions of the crate called by the body -/
  instances : Array (Instance N) := #[]
  /-- The lines of the body being printed -/
  lines : Array String := #[]
  indent : Nat := 1

abbrev M (N : Type) := StateT (PState N) (Except String)

section
variable {N : Type}

def fresh (base : String) : M N String :=
  modifyGet fun s => (s!"{base}{s.fresh}", { s with fresh := s.fresh + 1 })

def emit (l : String) : M N Unit :=
  modify fun s => { s with lines := s.lines.push ("".pushn ' ' (2 * s.indent) ++ l) }

def indented {α : Type} (x : M N α) : M N α := do
  modify fun s => { s with indent := s.indent + 1 }
  let r ← x
  modify fun s => { s with indent := s.indent - 1 }
  pure r

/-- Run `x`, returning the lines it emits instead of emitting them -/
def capture {α : Type} (x : M N α) : M N (Array String × α) := do
  let saved := (← get).lines
  modify fun s => { s with lines := #[] }
  let r ← x
  let ls := (← get).lines
  modify fun s => { s with lines := saved }
  pure (ls, r)

def replay (ls : Array String) : M N Unit :=
  modify fun s => { s with lines := s.lines ++ ls }

/-- A descriptor at the instance being printed -/
def resolve (t : Ty N) : M N (Ty N) := do
  let s ← get
  pure (subst s.tenv s.cenv t)

def resolveCArg (c : CArg) : M N CArg := do
  pure (substCArg (← get).cenv c)

end

/-- Is this C expression a plain identifier (safe to duplicate)? -/
def isIdent (e : String) : Bool :=
  !e.isEmpty && e.all fun c => c.isAlphanum || c == '_'

/-! ## Types -/

section
variable {N : Type} [TypeNames N] [Repr N]

mutual
  /-- The C type of a descriptor (resolved at the instance); the struct types are defined
  on demand -/
  partial def cType (t : Ty N) : M N String := do
    match ← resolve t with
    | .scalar s => pure (cNameScalar s)
    | .bool => pure "bool"
    | .unit => pure "unit_t"
    | .char => pure "uint32_t"
    | .var i => throw s!"unresolved type variable T{i}"
    | .str => throw "strings are not supported"
    | .result _ => throw "a Result as a value is not supported"
    | .arrow _ _ => throw "a closure as a value is not supported"
    | t => do needType t; pure (mangle t)

  /-- Define the struct of a (resolved) composite type, after the types of its
  components -/
  partial def needType (t : Ty N) : M N Unit := do
    let m := mangle t
    if (← get).defined.contains m then return
    if (← get).inProgress.contains m then throw s!"recursive type {m} is not supported"
    modify fun s => { s with inProgress := m :: s.inProgress }
    let body ← match t with
      | .tuple tys => do pure s!"struct {m} \{ {← fields tys} };"
      | .adt T targs cargs =>
        match T with
        | .builtin .vec => do
          let e ← cType (targs.getD 0 .unit)
          pure s!"struct {m} \{ {e} *ptr; size_t len; size_t cap; };"
        | _ => do
          let variants := (TypeRef.variants T).map (·.map (subst targs cargs))
          match variants with
          | [] =>
            match (← get).externals.lookup m with
            | some d => pure d
            | none => throw s!"opaque type {m} is not supported (no external definition)"
          | [fs] => do pure s!"struct {m} \{ {← fields fs} };"
          | _ => do
            let mut vs := #[]
            for h : i in [0:variants.length] do
              vs := vs.push s!"struct \{ {← fields variants[i]} } v{i};"
            pure s!"struct {m} \{ uint32_t tag; union \{ {" ".intercalate vs.toList} } u; };"
      | .array τ n => do
        let e ← cType τ
        match n with
        | .lit k _ => pure s!"struct {m} \{ {e} data[{max k 1}]; };"
        | .var i => throw s!"unresolved const-generic variable N{i}"
      | .slice τ => do
        let e ← cType τ
        pure s!"struct {m} \{ {e} *ptr; size_t len; };"
      | .controlFlow a b => do
        let a ← cType a
        let b ← cType b
        pure s!"struct {m} \{ uint32_t tag; union \{ {a} cont; {b} done; } u; };"
      | _ => throw s!"unexpected type {m}"
    modify fun s => { s with
      inProgress := s.inProgress.erase m, defined := m :: s.defined,
      types := s.types.push (m, s!"typedef struct {m} {m};\n{body}") }

  /-- The members `f0 …` of a struct (a dummy member for an empty one) -/
  partial def fields (tys : List (Ty N)) : M N String := do
    if tys.isEmpty then return "unit_t _dummy;"
    let mut out := #[]
    for h : i in [0:tys.length] do
      out := out.push s!"{← cType tys[i]} f{i};"
    pure (" ".intercalate out.toList)
end

end

/-! ## Expressions and statements -/

section
variable {N F G : Type} [TypeNames N] [FunNames F N] [GlobalNames G N] {σ : TyEnv}
  [Repr N] [Repr F] [Repr G]

/-- The prototype of a function instance (registered for the translation unit) -/
def protoOf (name : String) (inputs : List (Ty N)) (output : Ty N) : M N String := do
  let mut ps := #[]
  for h : i in [0:inputs.length] do
    ps := ps.push s!"{← cType inputs[i]} p{i}"
  match ← resolve output with
  | .result .unit => pure s!"int {name}({if ps.isEmpty then "void" else ", ".intercalate ps.toList});"
  | .result ρ => do
    pure s!"int {name}({", ".intercalate (ps.push s!"{← cType ρ} *out").toList});"
  | ρ => do pure s!"{← cType ρ} {name}({if ps.isEmpty then "void" else ", ".intercalate ps.toList});"

def needProto (name : String) (inputs : List (Ty N)) (output : Ty N) : M N Unit := do
  if (← get).protos.any (·.1 == name) then return
  let p ← protoOf name inputs output
  modify fun s => { s with protos := s.protos.push (name, p) }

/-- Record an instance of a function of the crate for the worklist of `program` -/
def needInstance (base : String) (targs : List (Ty N)) (cargs : List CArg) : M N Unit := do
  let name := funName base targs cargs
  unless (← get).instances.any (fun i => funName i.base i.targs i.cargs == name) do
    modify fun s => { s with instances := s.instances.push ⟨base, targs, cargs⟩ }

/-- The C name of a function of the crate at an instance, with its prototype. The
signature comes from the call node (the instantiated `inputs` and `output`), not from
the `FunNames` table: the printer never evaluates the tables of the crate, whose
implementations may be noncomputable. -/
def crateFun (f : F) (targs : List (Ty N)) (cargs : List CArg) (inputs : List (Ty N))
    (output : Ty N) : M N String := do
  let targs ← targs.mapM resolve
  let cargs ← cargs.mapM resolveCArg
  let base := ctorName f
  needProto (funName base targs cargs) inputs output
  needInstance base targs cargs
  pure (funName base targs cargs)

def crateGlobal (g : G) (targs : List (Ty N)) (cargs : List CArg) (τ : Ty N) : M N String := do
  let targs ← targs.mapM resolve
  let cargs ← cargs.mapM resolveCArg
  let base := ctorName g
  needProto (funName base targs cargs) [] τ
  needInstance base targs cargs
  pure (funName base targs cargs)

/-- Bind a C expression to a fresh variable unless it is an identifier -/
def atom (ty : Ty N) (e : String) : M N String := do
  if isIdent e then pure e
  else
    let x ← fresh "a"
    emit s!"{← cType ty} {x} = {e};"
    pure x

def lookup (ctx : Ctx) {Γ : List (Ty N)} {τ : Ty N} (v : Var N Γ τ) : M N VarInfo :=
  match ctx.vars[v.toNat]? with
  | some i => pure i
  | none => throw "unbound variable"

/-- The element type of a container -/
def elemOf (t : Ty N) : M N (Ty N) := do
  match ← resolve t with
  | .array e _ | .slice e | .adt (.builtin .vec) [e] [] => pure e
  | _ => throw "not a container"

/-- The element type of a slice iterator -/
def iterElemOf (t : Ty N) : M N (Ty N) := do
  match ← resolve t with
  | .adt (.builtin .sliceIter) [e] [] => pure e
  | _ => throw "not a slice iterator"

/-- The C expression of the length of a container held in `c` -/
def lenOf (t : Ty N) (c : String) : M N String := do
  match ← resolve t with
  | .array _ (.lit n _) => pure (toString n)
  | .array _ (.var i) => throw s!"unresolved const-generic variable N{i}"
  | .slice _ | .adt (.builtin .vec) _ _ => pure s!"{c}.len"
  | _ => throw "not a container"

/-- The member holding the elements of a container -/
def dataOf (t : Ty N) : M N String := do
  match ← resolve t with
  | .array _ _ => pure "data"
  | _ => pure "ptr"

/-- The destination of the value of a statement -/
inductive Dest where
  /-- The result of a `Result` function: written to `*out` (unless unit), `AENEAS_OK` returned -/
  | retRes (unit : Bool)
  /-- The result of a pure function -/
  | retPure
  | assign (x : String)
  | discard

def yield (d : Dest) (v : String) : M N Unit :=
  match d with
  | .retRes true => emit "return AENEAS_OK;"
  | .retRes false => do emit s!"*out = {v};"; emit "return AENEAS_OK;"
  | .retPure => emit s!"return {v};"
  | .assign x => emit s!"{x} = {v};"
  | .discard => pure ()

/-- A checked scalar operation: `r` receives the result, or the function returns the
error -/
def checkedOp (op : ScalarBinop) (ty : ScalarTy) (a b r : String) : M N Unit := do
  let T := cNameScalar ty
  let U := cNameU (unsignedOf ty)
  let signed := match ty with | .i _ => true | .u _ => false
  match op with
  | .add => emit s!"{T} {r}; if (__builtin_add_overflow({a}, {b}, &{r})) return AENEAS_INTEGER_OVERFLOW;"
  | .sub => emit s!"{T} {r}; if (__builtin_sub_overflow({a}, {b}, &{r})) return AENEAS_INTEGER_OVERFLOW;"
  | .mul => emit s!"{T} {r}; if (__builtin_mul_overflow({a}, {b}, &{r})) return AENEAS_INTEGER_OVERFLOW;"
  | .div => do
    emit s!"if ({b} == 0) return AENEAS_DIVISION_BY_ZERO;"
    if let .i it := ty then
      emit s!"if ({a} == {minI it} && {b} == -1) return AENEAS_INTEGER_OVERFLOW;"
    emit s!"{T} {r} = {a} / {b};"
  | .rem => do
    emit s!"if ({b} == 0) return AENEAS_DIVISION_BY_ZERO;"
    if signed then emit s!"{T} {r} = ({b} == -1) ? 0 : {a} % {b};"
    else emit s!"{T} {r} = {a} % {b};"
  | .shl rhs => do
    if let .i _ := rhs then emit s!"if ({b} < 0) return AENEAS_INTEGER_OVERFLOW;"
    emit s!"if ({b} >= {bits ty}) return AENEAS_INTEGER_OVERFLOW;"
    emit s!"{T} {r} = ({T})(({U}){a} << {b});"
  | .shr rhs => do
    if let .i _ := rhs then emit s!"if ({b} < 0) return AENEAS_INTEGER_OVERFLOW;"
    emit s!"if ({b} >= {bits ty}) return AENEAS_INTEGER_OVERFLOW;"
    emit s!"{T} {r} = {a} >> {b};"

mutual
  /-- The C expression of a pure expression; the statements it needs are emitted first -/
  partial def expr {Γ : List (Ty N)} {τ : Ty N} (ctx : Ctx) : IExpr N F G σ Γ τ → M N String
    | .var v => do
      let i ← lookup ctx v
      if i.borrow.isSome then throw "a closure used as a value"
      pure i.name
    | .appVar f a => do
      let i ← lookup ctx f
      let some b := i.borrow | throw "application of a variable which is not a borrow"
      let x ← expr ctx a
      let r ← fresh "r"
      emit s!"{b.contTy} {r} = {b.cont};"
      emit s!"{r}.{if b.kind == .array then "data" else "ptr"}[{b.idx}] = {x};"
      pure r
    | .uscalarLit ty n _ => pure (uLit ty n)
    | .iscalarLit ty n _ => pure (iLit ty n)
    | .boolLit b => pure (if b then "true" else "false")
    | .unitLit => pure "((unit_t)0)"
    | .scalarBitop op ty a b => do
      let a ← expr ctx a
      let b ← expr ctx b
      let sym := match op with | .and => "&" | .or => "|" | .xor => "^"
      pure s!"(({cNameScalar ty})({a} {sym} {b}))"
    | .bitNot ty a => do pure s!"(({cNameScalar ty})(~{← expr ctx a}))"
    | .cast _ tgt a => do pure s!"(({cNameScalar tgt}){← expr ctx a})"
    | .castFromBool tgt a => do pure s!"(({cNameScalar tgt})({← expr ctx a} ? 1 : 0))"
    | .boolBinop op a b => do
      let a ← expr ctx a
      let b ← expr ctx b
      pure (match op with
        | .and => s!"({a} && {b})"
        | .or => s!"({a} || {b})"
        | .xor => s!"({a} != {b})")
    | .boolNot a => do pure s!"(!{← expr ctx a})"
    | .bne (α := α) (inst := _) a b => do
      unless isComparable (← resolve α) do throw "`!=` on a non-scalar type"
      pure s!"({← expr ctx a} != {← expr ctx b})"
    | .decide c => cond ctx c
    | .ite (τ := τ) c t e => do
      let c ← cond ctx c
      let (lt, t) ← indented (capture (expr ctx t))
      let (le, e) ← indented (capture (expr ctx e))
      if lt.isEmpty && le.isEmpty then pure s!"({c} ? {t} : {e})"
      else
        let r ← fresh "r"
        emit s!"{← cType τ} {r};"
        emit s!"if ({c}) \{"
        replay lt
        emit s!"  {r} = {t};"
        emit "} else {"
        replay le
        emit s!"  {r} = {e};"
        emit "}"
        pure r
    | .tuple (tys := tys) es => do
      let ty ← cType (.tuple tys)
      let as ← exprs ctx es
      pure s!"(({ty})\{ {if as.isEmpty then "0" else ", ".intercalate as} })"
    | .array τ n h es => do
      let ty ← cType (.array τ (.lit n h))
      let as ← exprs ctx es
      pure s!"(({ty})\{ \{ {if as.isEmpty then "0" else ", ".intercalate as} } })"
    | .ctor T v (inst := _) targs cargs _ _ args => do
      let ty ← cType (.adt T targs cargs)
      let as ← exprs ctx args
      if (TypeRef.variants T).length == 1 then
        pure s!"(({ty})\{ {if as.isEmpty then "0" else ", ".intercalate as} })"
      else if as.isEmpty then pure s!"(({ty})\{ .tag = {v} })"
      else pure s!"(({ty})\{ .tag = {v}, .u.v{v} = \{ {", ".intercalate as} } })"
    | .proj _ f (inst := _) _ _ _ _ e => do pure s!"({← expr ctx e}).f{f}"
    | .global g targs cargs τ _ => do pure s!"{← crateGlobal g targs cargs τ}()"
    | .call f targs cargs inputs output _ _ args => do
      let as ← exprs ctx args
      match f with
      | .crate fn => do
        pure s!"{← crateFun fn targs cargs inputs output}({", ".intercalate as})"
      | .prim p => purePrim p inputs output as
    | .continue_ α β e => do
      let ty ← cType (.controlFlow α β)
      pure s!"(({ty})\{ .tag = 0, .u.cont = {← expr ctx e} })"
    | .break_ α β e => do
      let ty ← cType (.controlFlow α β)
      pure s!"(({ty})\{ .tag = 1, .u.done = {← expr ctx e} })"

  partial def exprs {Γ : List (Ty N)} {tys : List (Ty N)} (ctx : Ctx) :
      IExprs N F G σ Γ tys → M N (List String)
    | .nil => pure []
    | .cons e es => do
      let e ← expr ctx e
      let es ← exprs ctx es
      pure (e :: es)

  partial def cond {Γ : List (Ty N)} (ctx : Ctx) : ICond N F G σ Γ → M N String
    | .bool b => expr ctx b
    | .not c => do pure s!"(!{← cond ctx c})"
    | .eq (α := α) (inst := _) a b => do
      unless isComparable (← resolve α) do throw "`==` on a non-scalar type"
      pure s!"({← expr ctx a} == {← expr ctx b})"
    | .lt (α := α) (ord := _) (inst := _) a b => do
      unless isComparable (← resolve α) do throw "`<` on a non-scalar type"
      pure s!"({← expr ctx a} < {← expr ctx b})"
    | .le (α := α) (ord := _) (inst := _) a b => do
      unless isComparable (← resolve α) do throw "`<=` on a non-scalar type"
      pure s!"({← expr ctx a} <= {← expr ctx b})"
    | .gt (α := α) (ord := _) (inst := _) a b => do
      unless isComparable (← resolve α) do throw "`>` on a non-scalar type"
      pure s!"({← expr ctx a} > {← expr ctx b})"
    | .ge (α := α) (ord := _) (inst := _) a b => do
      unless isComparable (← resolve α) do throw "`>=` on a non-scalar type"
      pure s!"({← expr ctx a} >= {← expr ctx b})"

  /-- The pure primitives -/
  partial def purePrim (p : Prim) (inputs : List (Ty N)) (output : Ty N) (as : List String) :
      M N String := do
    match p, as with
    | .arrayRepeat, [x] => do
      let ty ← cType output
      let n ← lenOf output ""
      let r ← fresh "r"
      emit s!"{ty} {r};"
      emit s!"for (size_t k = 0; k < {n}; k++) {r}.data[k] = {x};"
      pure r
    | .arrayToSlice, [a] => do
      let arrTy := inputs.getD 0 .unit
      let a ← atom arrTy a
      let ty ← cType output
      let n ← lenOf arrTy a
      pure s!"(({ty})\{ {a}.data, {n} })"
    | .sliceLen, [s] => pure s!"({s}).len"
    | .vecLen, [v] => pure s!"({v}).len"
    | .vecNew, [] => do pure s!"(({← cType output})\{ NULL, 0, 0 })"
    | _, _ => throw s!"the primitive {reprStr p} is not a pure expression"
end

/-- The fallible primitives, as statements -/
def fallPrim (d : Dest) (p : Prim) (inputs : List (Ty N)) (τ : Ty N) (as : List String) :
    M N Unit := do
  match p, as, inputs with
  | .lift, [x], _ => yield d x
  | .arrayIndex, [c, i], [ct, _] | .sliceIndex, [c, i], [ct, _] | .vecIndex, [c, i], [ct, _] => do
    let c ← atom ct c
    let i ← atom (.scalar (.u .Usize) : Ty N) i
    emit s!"if ({i} >= {← lenOf ct c}) return AENEAS_ARRAY_OUT_OF_BOUNDS;"
    yield d s!"{c}.{← dataOf ct}[{i}]"
  | .arrayUpdate, [c, i, x], [ct, _, _] | .sliceUpdate, [c, i, x], [ct, _, _] => do
    let c ← atom ct c
    let i ← atom (.scalar (.u .Usize) : Ty N) i
    emit s!"if ({i} >= {← lenOf ct c}) return AENEAS_ARRAY_OUT_OF_BOUNDS;"
    let r ← fresh "r"
    emit s!"{← cType ct} {r} = {c};"
    emit s!"{r}.{← dataOf ct}[{i}] = {x};"
    yield d r
  | .vecPush, [v, x], [vt, et] => do
    let r ← fresh "r"
    emit s!"{← cType vt} {r} = {v};"
    emit s!"if ({r}.len == {r}.cap) \{ size_t ncap = {r}.cap ? 2 * {r}.cap : 8; void *np = realloc({r}.ptr, ncap * sizeof({← cType et})); if (!np) return AENEAS_MAXIMUM_SIZE_EXCEEDED; {r}.ptr = np; {r}.cap = ncap; }"
    emit s!"{r}.ptr[{r}.len++] = {x};"
    yield d r
  | .rangeNextUsize, [r], [rt] => do
    -- `Range<usize>::next`: the start if it is below the end, stepping the start (the
    -- model only fails on a `Step` invariant, impossible for `usize`)
    let r ← atom rt r
    let rangeTy ← cType rt
    let outTy ← cType τ
    let optTy ← cType (.adt (.builtin .option) [.scalar (.u .Usize)] [] : Ty N)
    let res ← fresh "r"
    emit s!"{outTy} {res};"
    emit s!"if ({r}.f0 < {r}.f1) \{ {res} = (({outTy})\{ (({optTy})\{ .tag = 1, .u.v1 = \{ {r}.f0 } }), (({rangeTy})\{ {r}.f0 + 1, {r}.f1 }) }); }"
    emit s!"else \{ {res} = (({outTy})\{ (({optTy})\{ .tag = 0 }), {r} }); }"
    yield d res
  | .rangeRevUsize, [r], _ => do
    -- `Iterator::rev`: `Rev { iter: r }` (the model never fails)
    yield d s!"(({← cType τ})\{ {r} })"
  | .revRangeNextUsize, [rv], [rt] => do
    -- `Rev<Range<usize>>::next`: `next_back` of the range, the end stepped down
    let rv ← atom rt rv
    let revTy ← cType rt
    let rangeTy ← cType (.adt (.builtin .range) [.scalar (.u .Usize)] [] : Ty N)
    let outTy ← cType τ
    let optTy ← cType (.adt (.builtin .option) [.scalar (.u .Usize)] [] : Ty N)
    let res ← fresh "r"
    emit s!"{outTy} {res};"
    emit s!"if ({rv}.f0.f0 < {rv}.f0.f1) \{ size_t ae_e = {rv}.f0.f1 - 1; {res} = (({outTy})\{ (({optTy})\{ .tag = 1, .u.v1 = \{ ae_e } }), (({revTy})\{ (({rangeTy})\{ {rv}.f0.f0, ae_e }) }) }); }"
    emit s!"else \{ {res} = (({outTy})\{ (({optTy})\{ .tag = 0 }), {rv} }); }"
    yield d res
  | .rangeStepByUsize, [r, n], _ => do
    -- `Iterator::step_by`: `StepBy { iter: r, step }`, a panic on a zero step
    let n ← atom (.scalar (.u .Usize) : Ty N) n
    emit s!"if ({n} == 0) return AENEAS_PANIC;"
    yield d s!"(({← cType τ})\{ {r}, {n} })"
  | .stepByRangeNextUsize, [sb], [st] => do
    -- `StepBy<Range<usize>>::next`: the start, then the start advanced by the step
    -- (bounded by the end, as the repeated `next` of the model)
    let sb ← atom st sb
    let sbTy ← cType st
    let rangeTy ← cType (.adt (.builtin .range) [.scalar (.u .Usize)] [] : Ty N)
    let outTy ← cType τ
    let optTy ← cType (.adt (.builtin .option) [.scalar (.u .Usize)] [] : Ty N)
    let res ← fresh "r"
    emit s!"{outTy} {res};"
    emit s!"if ({sb}.f0.f0 < {sb}.f0.f1) \{ size_t ae_s = {sb}.f0.f0; size_t ae_e = {sb}.f0.f1; size_t ae_n = ({sb}.f1 >= ae_e - ae_s) ? ae_e : ae_s + {sb}.f1; {res} = (({outTy})\{ (({optTy})\{ .tag = 1, .u.v1 = \{ ae_s } }), (({sbTy})\{ (({rangeTy})\{ ae_n, ae_e }), {sb}.f1 }) }); }"
    emit s!"else \{ {res} = (({outTy})\{ (({optTy})\{ .tag = 0 }), {sb} }); }"
    yield d res
  | .sliceIter, [s], _ | .sliceIntoIter, [s], _ => do
    -- `[T]::iter` / `into_iter` on a slice: the slice and the index `0`
    yield d s!"(({← cType τ})\{ {s}, 0 })"
  | .arrayIntoIter, [a], [at_] => do
    -- `into_iter` on an array: the array viewed as a slice, and the index `0`
    let a ← atom at_ a
    let n ← lenOf at_ a
    let sliceTy ← cType (.slice (← elemOf at_))
    yield d s!"(({← cType τ})\{ (({sliceTy})\{ {a}.data, {n} }), 0 })"
  | .sliceIterNext, [it], [itTy] => do
    -- `Iter<T>::next`: the element at the index if below the length, the index stepped
    let it ← atom itTy it
    let iterTy ← cType itTy
    let outTy ← cType τ
    let optTy ← cType (.adt (.builtin .option) [← iterElemOf itTy] [] : Ty N)
    let res ← fresh "r"
    emit s!"{outTy} {res};"
    emit s!"if ({it}.f1 < {it}.f0.len) \{ {res} = (({outTy})\{ (({optTy})\{ .tag = 1, .u.v1 = \{ {it}.f0.ptr[{it}.f1] } }), (({iterTy})\{ {it}.f0, {it}.f1 + 1 }) }); }"
    emit s!"else \{ {res} = (({outTy})\{ (({optTy})\{ .tag = 0 }), {it} }); }"
    yield d res
  | .arrayIndexMut, _, _ | .sliceIndexMut, _, _ | .vecIndexMut, _, _ =>
    throw "an `index_mut` primitive outside a borrow"
  | _, _, _ => throw s!"the primitive {reprStr p} is not a fallible statement (type {reprStr τ})"

mutual
  /-- Bind the variables of a pattern to the components of the C value `v` -/
  partial def bindPat : {α : Ty N} → {Δ : List (Ty N)} → Pat N α Δ → String → M N (List VarInfo)
    | α, _, .var, v => do
      let x ← fresh "x"
      emit s!"{← cType α} {x} = {v};"
      pure [{ name := x }]
    | _, _, .ignore, _ => pure []
    | _, _, .tuple ps, v => bindPats ps v 0

  partial def bindPats : {tys : List (Ty N)} → {Δ : List (Ty N)} →
      Pats N tys Δ → String → Nat → M N (List VarInfo)
    | _, _, .nil, _, _ => pure []
    | _, _, .cons p ps, v, i => do
      let a ← bindPat p s!"{v}.f{i}"
      let b ← bindPats ps v (i + 1)
      pure (a ++ b)
end

/-- Bind the fields of a variant (`pre.f0 …`) to fresh variables -/
def bindFields (tys : List (Ty N)) (pre : String) : M N (List VarInfo) := do
  let mut out := []
  for h : i in [0:tys.length] do
    let x ← fresh "x"
    emit s!"{← cType tys[i]} {x} = {pre}.f{i};"
    out := out ++ [{ name := x }]
  pure out

/-- `some true` for `.var`, `some false` for `.ignore`, `none` for a tuple pattern -/
def patIsVar : {α : Ty N} → {Δ : List (Ty N)} → Pat N α Δ → Option Bool
  | _, _, .var => some true
  | _, _, .ignore => some false
  | _, _, .tuple _ => none

/-- Bind the pattern of a borrow: the element to `x`, the backward function to its
borrow information -/
def bindBorrowPat : {α : Ty N} → {Δ : List (Ty N)} → Pat N α Δ → String → BorrowInfo →
    M N (List VarInfo)
  | _, _, .tuple (.cons px (.cons pb .nil)), x, b => do
    let vs ← bindPat px x
    match patIsVar pb with
    | some true => pure (vs ++ [{ name := "<closure>", borrow := some b }])
    | some false => pure vs
    | none => throw "unexpected pattern for the backward function of a borrow"
  | _, _, .ignore, _, _ => pure []
  | _, _, _, _, _ => throw "unexpected pattern for a borrow"

mutual
  /-- Print a statement, its value going to `d` -/
  partial def stmt {Γ : List (Ty N)} {τ : Ty N} (ctx : Ctx) (d : Dest) :
      Stmt N F G σ Γ τ → M N Unit
    | .pure e => do yield d (← expr ctx e)
    | .ret e => do yield d (← expr ctx e)
    | .fail _ err => emit s!"return {errCode err};"
    | .letVal e p k => do
      let v ← expr ctx e
      let vs ← bindPat p v
      stmt (ctx.extend vs) d k
    | .letStmt (α := α) s p k => do
      let t ← fresh "t"
      emit s!"{← cType α} {t};"
      stmt ctx (.assign t) s
      let vs ← bindPat p t
      stmt (ctx.extend vs) d k
    | .bindStmt (α := α) s p k => do
      let t ← fresh "t"
      emit s!"{← cType α} {t};"
      stmt ctx (.assign t) s
      let vs ← bindPat p t
      stmt (ctx.extend vs) d k
    | .call f targs cargs inputs τ _ _ args => do
      let as ← exprs ctx args
      match f with
      | .crate fn => do
        let name ← crateFun fn targs cargs inputs (.result τ)
        fallibleCall d name τ as
      | .prim p => fallPrim d p inputs τ as
    | .global g targs cargs τ _ => do
      let name ← crateGlobal g targs cargs (.result τ)
      fallibleCall d name τ []
    | .scalarBinop op ty a b => do
      let a ← atom (.scalar ty : Ty N) (← expr ctx a)
      let b ← atom (.scalar (op.rhsTy ty) : Ty N) (← expr ctx b)
      let r ← fresh "r"
      checkedOp op ty a b r
      yield d r
    | .neg ty a => do
      let a ← atom (.scalar (.i ty) : Ty N) (← expr ctx a)
      emit s!"if ({a} == {minI ty}) return AENEAS_INTEGER_OVERFLOW;"
      yield d s!"(-{a})"
    | .assert c => do
      emit s!"if (!{← cond ctx c}) return AENEAS_ASSERTION_FAILURE;"
      yield d "((unit_t)0)"
    | .ite c t e => do
      let c ← cond ctx c
      emit s!"if ({c}) \{"
      indented (stmt ctx d t)
      emit "} else {"
      indented (stmt ctx d e)
      emit "}"
    | .switch T (inst := _) targs cargs shape _ scrut brs => do
      let s ← expr ctx scrut
      let t ← fresh "s"
      emit s!"{← cType (.adt T targs cargs)} {t} = {s};"
      if shape.length == 1 then
        branches ctx d t false 0 brs
      else
        emit s!"switch ({t}.tag) \{"
        branches ctx d t true 0 brs
        emit "default: abort();"
        emit "}"
    | .loop (α := α) (β := β) p init body => do
      let st ← fresh "st"
      emit s!"{← cType α} {st} = {← expr ctx init};"
      emit "for (;;) {"
      indented do
        let vs ← bindPat p st
        let cf ← fresh "cf"
        emit s!"{← cType (.controlFlow α β)} {cf};"
        stmt (ctx.extend vs) (.assign cf) body
        emit s!"if ({cf}.tag == 0) \{ {st} = {cf}.u.cont; } else \{"
        indented do
          yield d s!"{cf}.u.done"
          emit "break;"
        emit "}"
      emit "}"
    | .borrow m _ _ inputs _ _ args p k => do
      let as ← exprs ctx args
      match as, inputs with
      | [c, i], [ct, _] => do
        let contTy ← cType ct
        let cv ← fresh "c"
        emit s!"{contTy} {cv} = {c};"
        let iv ← fresh "i"
        emit s!"size_t {iv} = {i};"
        emit s!"if ({iv} >= {← lenOf ct cv}) return AENEAS_ARRAY_OUT_OF_BOUNDS;"
        let x ← fresh "x"
        emit s!"{← cType (← elemOf ct)} {x} = {cv}.{← dataOf ct}[{iv}];"
        let vs ← bindBorrowPat p x { kind := m, cont := cv, idx := iv, contTy }
        stmt (ctx.extend vs) d k
      | _, _ => throw "unexpected arguments of a borrow"

  /-- A call to a `Result` function: the error is propagated, the value goes to `d` -/
  partial def fallibleCall (d : Dest) (name : String) (τ : Ty N) (as : List String) :
      M N Unit := do
    let rc ← fresh "rc"
    if isUnit (← resolve τ) then
      emit s!"int {rc} = {name}({", ".intercalate as});"
      emit s!"if ({rc}) return {rc};"
      yield d "((unit_t)0)"
    else
      let t ← fresh "t"
      emit s!"{← cType τ} {t};"
      emit s!"int {rc} = {name}({", ".intercalate (as ++ [s!"&{t}"])});"
      emit s!"if ({rc}) return {rc};"
      yield d t

  partial def branches {Γ : List (Ty N)} {shape : List (List (Ty N))} {τ : Ty N}
      (ctx : Ctx) (d : Dest) (scrut : String) (tagged : Bool) (i : Nat) :
      SBranches N F G σ Γ shape τ → M N Unit
    | .nil => pure ()
    | .cons (Δ := Δ) b bs => do
      if tagged then emit s!"case {i}: \{"
      indented do
        let vs ← bindFields Δ (if tagged then s!"{scrut}.u.v{i}" else scrut)
        stmt (ctx.extend vs) d b
        if tagged then emit "break;"
      if tagged then emit "}"
      branches ctx d scrut tagged (i + 1) bs
end

/-! ## Functions and programs -/

/-- The output of the printer for one function instance -/
structure FnOut (N : Type) where
  name : String
  /-- The definition, or a comment when the function is not printed -/
  text : String
  proto : String := ""
  types : Array (String × String) := #[]
  protos : Array (String × String) := #[]
  /-- The instances of the functions of the crate called by the body -/
  instances : Array (Instance N) := #[]
  ok : Bool

/-- The definition of the function `name` with the compiled body `s` -/
def functionText {Γ : List (Ty N)} {τ : Ty N} (name : String) (s : Stmt N F G σ Γ τ) :
    M N (String × String) := do
  let mut ps := #[]
  let mut vars := []
  for h : i in [0:Γ.length] do
    ps := ps.push s!"{← cType Γ[i]} p{i}"
    vars := vars ++ [({ name := s!"p{i}" } : VarInfo)]
  let (retTy, dest, ps') ← match ← resolve τ with
    | .result .unit => pure ("int", Dest.retRes true, ps)
    | .result ρ => do pure ("int", Dest.retRes false, ps.push s!"{← cType ρ} *out")
    | ρ => do pure (← cType ρ, Dest.retPure, ps)
  let params := if ps'.isEmpty then "void" else ", ".intercalate ps'.toList
  let sig := s!"{retTy} {name}({params})"
  modify fun st => { st with lines := #[], indent := 1 }
  stmt { vars } dest s
  let body := (← get).lines
  pure (sig ++ " {\n" ++ "\n".intercalate body.toList ++ "\n}\n", sig ++ ";")

/-- Compile and print one function instance: `e` is the deep term, `tenv`/`cenv` the
interpretation of its type and const-generic parameters, `externals` the C definitions
of the opaque types -/
def printFunction {Γ : List (Ty N)} {τ : Ty N} (tenv : List (Ty N)) (cenv : List CArg)
    (externals : List (String × String)) (name : String) (e : Expr N F G σ Γ τ) : FnOut N :=
  match compile e with
  | .error u => { name, text := s!"/* {name}: not compiled ({reprStr u}) */", ok := false }
  | .ok s =>
    match (functionText name s).run { tenv, cenv, externals } with
    | .ok ((text, proto), st) =>
      { name, text, proto, types := st.types, protos := st.protos, instances := st.instances,
        ok := true }
    | .error msg => { name, text := s!"/* {name}: not printed ({msg}) */", ok := false }

/-- A deep term of the crate, packaged for `program`: its C base name, the numbers of its
type and const-generic parameters (the term is given at some interpretation of them,
which the printer ignores), and the term -/
structure AnyDeep (N F G : Type) [TypeNames N] [FunNames F N] [GlobalNames G N] where
  name : String
  nTypes : Nat
  nConsts : Nat
  σ : TyEnv
  Γ : List (Ty N)
  τ : Ty N
  e : Expr N F G σ Γ τ

/-- The output of `program` -/
structure Report where
  text : String
  printed : Nat
  total : Nat
  failures : Array String

/-- Print the instances of the functions of the crate reachable from the closed ones and
from `entries` (base name, arguments), with the external types `externals`, and
assemble the translation unit -/
partial def program (fns : List (AnyDeep N F G)) (externals : List (String × String))
    (entries : List (String × List (Ty N) × List CArg)) : Report := Id.run do
  let closed := fns.filter fun f => f.nTypes == 0 && f.nConsts == 0
  let mut work : List (Instance N) :=
    closed.map (fun f => ⟨f.name, [], []⟩) ++ entries.map (fun (n, ts, cs) => ⟨n, ts, cs⟩)
  let mut seen : List String := []
  let mut outs : Array (FnOut N) := #[]
  let mut failures : Array String := #[]
  repeat
    match work with
    | [] => break
    | inst :: rest =>
      work := rest
      let key := funName inst.base inst.targs inst.cargs
      if seen.contains key then continue
      seen := key :: seen
      -- a callee outside the deep terms of the crate gets a prototype only
      let some f := fns.find? (·.name == inst.base) | continue
      if inst.targs.length != f.nTypes || inst.cargs.length != f.nConsts then
        failures := failures.push s!"/* {key}: wrong number of arguments for {f.name} */"
        continue
      let o := printFunction inst.targs inst.cargs externals key f.e
      outs := outs.push o
      if o.ok then work := work ++ o.instances.toList
      else failures := failures.push o.text
  -- the translation unit
  let mut types : Array (String × String) := #[]
  let mut protos : Array (String × String) := #[]
  for o in outs do
    for t in o.types do
      unless types.any (·.1 == t.1) do types := types.push t
    for p in o.protos do
      unless protos.any (·.1 == p.1) do protos := protos.push p
  for o in outs do
    if o.ok then
      unless protos.any (·.1 == o.name) do protos := protos.push (o.name, o.proto)
  let mut text := prelude
  text := text ++ "\n/* Types */\n" ++ "\n".intercalate (types.map (·.2)).toList ++ "\n"
  text := text ++ "\n/* Prototypes */\n" ++ "\n".intercalate (protos.map (·.2)).toList ++ "\n"
  text := text ++ "\n/* Functions */\n" ++ "\n".intercalate (outs.map (·.text)).toList
  pure { text, printed := (outs.filter (·.ok)).size, total := outs.size, failures }

end

/-! Computable stand-ins for the tables of a crate, which the printer never consults: the
driver substitutes them for the instances of the deep terms, whose implementations may be
noncomputable (a crate with axiomatized external functions). -/

set_option warn.classDefReducibility false in
def dummyFunNames (F N : Type) [TypeNames N] : FunNames F N :=
  ⟨fun _ => ⟨⟨[], .unit⟩, fun _ => ()⟩⟩

set_option warn.classDefReducibility false in
def dummyGlobalNames (G N : Type) [TypeNames N] : GlobalNames G N :=
  ⟨fun _ => ⟨.unit, fun _ => ()⟩⟩

end Aeneas.Deep.CPrint
