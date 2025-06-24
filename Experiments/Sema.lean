import CTree.Basic
import CTree.EffectAlgebra
import CTree.Monad
import CTree.Euttc
import Mathlib.Logic.Function.Basic


/-!
# Source Language
-/

inductive Ty
  | unit
  | nat

inductive Expr : Ty → Type
  | const (n : Nat) : Expr .nat
  | add (e1 e2 : Expr .nat) : Expr .nat
  | mul (e1 e2 : Expr .nat) : Expr .nat
  | read (addr : Nat) : Expr .nat
  | write (addr : Nat) (val : Expr .nat) : Expr .unit
  | seq {α β : Ty} (e1 : Expr α) (e2 : Expr β) : Expr β

instance {n : Nat} : OfNat (Expr .nat) n where
  ofNat := .const n

instance : Add (Expr .nat) where
  add := Expr.add

instance : Mul (Expr .nat) where
  mul := Expr.mul

/-- Read from memory -/
notation:100 "mem[" addr "]" => Expr.read addr

/-- Write to memory -/
notation:60 "mem[" addr "]" " = " val:61 => Expr.write addr val

/-- Sequencing of expressions -/
infixr:30 "; " => Expr.seq

def Expr.example : Expr .nat :=
  mem[0] = 42;
  mem[1] = 32;
  mem[2] = mem[0] + mem[1];
  mem[3] = mem[1] * mem[2];
  mem[3] = mem[0] + mem[1] * mem[3];
  mem[3]

/-!
# Source Semantics
-/

/-- Memory is a map from Nat to Nat -/
def Memory := Nat → Nat

/-- Memory events -/
inductive MemoryE : Type → Type
  | read (addr : Nat) : MemoryE Nat
  | write (addr : Nat) (val : Nat) : MemoryE Unit

-- /-- Monad Transformer for Memory -/
-- abbrev MemoryT (m : Type → Type 1) (α : Type) := StateT Memory m α

-- /-- Handler for Memory events -/
-- def handleMemory {ε : Type → Type} : MemoryE ⟹ MemoryT (CTree ε) :=
--   fun e => do
--     match e with
--     | .read addr =>
--       let mem ← .get
--       return mem addr
--     | .write addr val =>
--       let mem ← .get
--       let newMem := Function.update mem addr val
--       .set newMem

@[reducible]
def Ty.denote : Ty → Type
  | .unit => Unit
  | .nat => Nat

def Expr.denote (e : Expr t) : CTree MemoryE (t.denote) := do
  match e with
  | .const n => return n
  | .add e1 e2 =>
    let e1 ← denote e1
    let e2 ← denote e2
    return e1 + e2
  | .mul e1 e2 =>
    let e1 ← denote e1
    let e2 ← denote e2
    return e1 * e2
  | .read addr =>
    .trigger (.read addr)
  | .write addr val =>
    let val ← denote val
    .trigger (.write addr val)
  | .seq e1 e2 =>
    let _ ← denote e1
    denote e2

/-!
# Target Language
-/

inductive Instrs
  | halt
  | push (val : Nat) : Instrs → Instrs
  | add : Instrs → Instrs
  | mult : Instrs → Instrs
  | read (addr : Nat) : Instrs → Instrs
  | write (addr : Nat) : Instrs → Instrs

inductive ExceptionE : Type → Type
  | exception {α : Type} : ExceptionE α

abbrev InstrsE := MemoryE + ExceptionE

abbrev Stack := List Nat

def Instrs.eval (prog : Instrs) (stack : Stack) : CTree InstrsE Stack := do
  match prog with
  | .halt => return stack
  | .push val c => eval c (val :: stack)
  | .add c =>
    match stack with
    | v1 :: v2 :: s => eval c ((v1 + v2) :: s)
    | _ => .trigger <| .inr .exception
  | .mult c =>
    match stack with
    | v1 :: v2 :: s => eval c ((v1 * v2) :: s)
    | _ => .trigger <| .inr .exception
  | .read addr c =>
    let val ← .trigger (.inl <| .read addr)
    eval c (val :: stack)
  | .write addr c =>
    match stack with
    | val :: s =>
      let _ ← .trigger (.inl <| .write addr val)
      eval c s
    | _ => .trigger <| .inr .exception


