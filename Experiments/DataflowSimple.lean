import Aesop
import ITree
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

inductive BinOp
  | add
  | mul

def BinOp.denote : BinOp → Nat → Nat → Nat
  | add => Nat.add
  | mul => Nat.mul

abbrev FIFO := Nat

inductive Node
  | binOp (op : BinOp) (x y out : FIFO)

abbrev DFG := List Node

abbrev FifoState := FIFO → List Nat

inductive ParE : Type → Type
  | par (numNodes : Nat) : ParE (Fin numNodes)

abbrev PTree (ε : Type → Type) (ρ : Type) :=
  ITree (ε + ParE) ρ

def PTree.par {ε ρ} (l : List (PTree ε ρ)) : PTree ε ρ :=
  .vis (ParE.par l.length) l.get

inductive FifoE : Type → Type
  | push (fifo : FIFO) (val : Nat) : FifoE Unit
  | pop (fifo : FIFO)              : FifoE (Option Nat)

def Node.denote : Node → PTree FifoE Unit
  | .binOp op x y out => ITree.iter (fun () => do
    let (some x : Option Nat) ← .trigger (FifoE.pop x)
      | return .done ()
    let (some y : Option Nat) ← .trigger (FifoE.pop y)
      | return .done ()
    .trigger (FifoE.push out (op.denote x y))
    return .recur ()
  ) ()

/-# ------Examples-------- -/

def A := 0
def B := 1
def C := 2
def D := 4

def tmp1 := 5
def tmp2 := 6

/-- D = (A + B) * C -/
def addMul : DFG := [
  .binOp .add A B tmp1,
  .binOp .mul tmp1 C D,
]

/-- D = A * C + B * C -/
def mulAdd : DFG := [
  .binOp .mul A C tmp1,
  .binOp .mul B C tmp2,
  .binOp .add tmp1 tmp2 D,
]

