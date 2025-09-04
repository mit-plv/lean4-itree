import Aesop
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

inductive BinOp
  | add
  | mul

abbrev Addr := Nat

abbrev FIFO := Nat

inductive Node
  | const (val : Nat) (out : FIFO)
  | binOp (op : BinOp) (x y out : FIFO)
  | store (addr : Addr) (val out : FIFO)
  | load (addr : Addr) (out : FIFO)

abbrev DFG := List Node

abbrev Mem := Nat → Nat

abbrev FifoState := FIFO → List Nat

structure State where
  mem   : Mem       := fun _ => 0
  fifos : FifoState := fun _ => []

def State.pop (port : FIFO) (s : State) (h : s.fifos port ≠ []) : (Nat × State) :=
  ((s.fifos port).head h, {s with fifos := Function.update s.fifos port (s.fifos port).tail})

def State.push (port : FIFO) (val : Nat) (s : State) : State :=
  {s with fifos := Function.update s.fifos port (val :: s.fifos port)}

def State.set (addr : Nat) (val : Nat) (s : State) : State :=
  {s with mem := Function.update s.mem addr val}

def State.get (addr : Nat) (s : State) : Nat :=
  s.mem addr

def BinOp.denote : BinOp → Nat → Nat → Nat
  | add => Nat.add
  | mul => Nat.mul

def Node.fire (s : State) (n : Node) : Option State :=
  match n with
  | .const v out =>
    if s.fifos out = [] then
      some {s with fifos := Function.update s.fifos out [v]}
    else
      none
  | .binOp op x y out =>
    if h : s.fifos x = [] then none else
    let (x, s) := s.pop x h
    if h : s.fifos y = [] then none else
    let (y, s) := s.pop y h
    let xy := op.denote x y
    s.push out xy
  | .store addr val out =>
    if h : s.fifos val = [] then none else
    let (val, s) := s.pop val h
    let s := s.set addr val
    s.push out 1
  | .load addr out =>
    if s.fifos out = [] then
      s.push out (s.get addr)
    else
      none

def DFG.Step (dfg : DFG) (s s' : State) : Prop :=
  ∃ node ∈ dfg, node.fire s = some s'

def DFG.MultiStep (dfg : DFG) : State → State → Prop :=
  Relation.ReflTransGen dfg.Step

def DFG.TerminatesAt (dfg : DFG) (init final : State) : Prop :=
  dfg.MultiStep init final ∧ ∀ s, dfg.MultiStep final s → s = final

def DFG.Terminates (dfg : DFG) (init : State) : Prop :=
  ∃ final, dfg.TerminatesAt init final

def DFG.Confluent (dfg : DFG) (init : State) : Prop :=
  ∀ final1 final2,
    dfg.TerminatesAt init final1
    → dfg.TerminatesAt init final2
    → final1 = final2

def DFG.Safe (dfg : DFG) (init : State) : Prop :=
  dfg.Terminates init ∧ dfg.Confluent init
