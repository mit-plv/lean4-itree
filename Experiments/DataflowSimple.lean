import Aesop
import ITree
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation
import Std.Do

inductive BinOp
  | add
  | mul

def BinOp.denote : BinOp → Nat → Nat → Nat
  | add => Nat.add
  | mul => Nat.mul

abbrev FIFO := Nat

inductive Node
  | binOp (op : BinOp) (x y out : FIFO)
  | broadcast (input : FIFO) (output : List FIFO)

abbrev DFG := List Node

abbrev FifoState := FIFO → List Nat

def FifoState.empty : FifoState :=
  fun _ => []

def FifoState.set (fifo : FIFO) (val : List Nat) (s : FifoState) : FifoState :=
  Function.update s fifo val

instance : EmptyCollection FifoState := ⟨.empty⟩

instance : Singleton (FIFO × List Nat) FifoState where
  singleton fifoVal := FifoState.empty.set fifoVal.1 fifoVal.2

instance : Insert (FIFO × List Nat) FifoState where
  insert fifoVal s := s.set fifoVal.1 fifoVal.2

/-# ------Examples-------- -/

def DFG.run (dfg : DFG) (inputs : List (FIFO × List Nat)) (output : FIFO) : IO (List Nat) := do
  let fifoIds : List FIFO :=
    dfg.map (fun node => match node with | .binOp _ x y out => [x, y, out] | .broadcast input outputs => [input] ++ outputs)
    |> List.flatten |> List.dedup
  let fifoMap : Std.TreeMap FIFO (Std.CloseableChannel Nat) ←
    fifoIds.foldlM (fun map fifo => return map.insert fifo (← Std.CloseableChannel.new)) {}
  let inputs : List (Std.CloseableChannel Nat × List Nat) :=
    inputs.filterMap fun (fifo, vals) => (fifoMap.get? fifo).map (·, vals)

  -- send inputs
  _ ← inputs.mapM fun (ch, vals) => IO.asTask do
    for val in vals do
      _ ← ch.send val
    ch.close

  _ ← dfg.mapM fun node => IO.asTask do
    match node with
    | .binOp op x y out =>
      let some x   := fifoMap.get? x   | return
      let some y   := fifoMap.get? y   | return
      let some out := fifoMap.get? out | return
      while true do
        match (← x.recv).get, (← y.recv).get with
        | some xVal, some yVal =>
          _ ← out.send (op.denote xVal yVal)
        | _, _ =>
          out.close
          return
    | .broadcast input outputs =>
      let some input := fifoMap.get? input | return
      let outputs := outputs.filterMap fifoMap.get?
      while true do
        match (← input.recv).get with
        | some val =>
          outputs.forM (fun ch => do _ ← ch.send val)
        | none =>
          outputs.forM (Std.CloseableChannel.close ·)
          return

  let some outputCh := fifoMap.get? output | IO.println "output not found"; return []
  let mut res := #[]

  while true do
    match (← outputCh.recv).get with
    | some val => res := res.push val
    | none => break

  return res.toList

def A := 0
def B := 1
def C := 2
def D := 4

def tmp1 := 5
def tmp2 := 6
def tmp3 := 7
def tmp4 := 8

/-- D = (A + B) * C -/
def addMul : DFG := [
  .binOp .add A B tmp1,
  .binOp .mul tmp1 C D,
]

/-- D = A * C + B * C -/
def mulAdd : DFG := [
  .broadcast C [tmp1, tmp2],
  .binOp .mul A tmp1 tmp3,
  .binOp .mul B tmp2 tmp4,
  .binOp .add tmp3 tmp4 D,
]

def initial (a b c : Nat) : FifoState := {
  (A, [a]),
  (B, [b]),
  (C, [c])
}

def final (d : Nat) : FifoState := {
  (D, [d])
}

def inputs := [(A, [1, 2, 3]), (B, [1, 2, 3]), (C, [1, 2, 3])]

#eval addMul.run inputs D
#eval mulAdd.run inputs D
