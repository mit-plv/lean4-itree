import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Vector.Basic

theorem Vector.get_append {xs : Vector α n} {ys : Vector α m} {i : Fin n}
  : (xs.append ys).get ⟨i, by apply Nat.lt_add_right; exact i.isLt⟩ = xs.get i := by
  apply List.get_append

def SDFNode := Node SimpleDataflow.Ty SimpleDataflow.Ops

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

def Step.Prim.toSDF : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .prim (.bitVec w)

def Step.Prim.toSDFOpt : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .option (.bitVec w)

structure SDFOneOutput (p : Step.Prim) where
  g : SimpleDataflow.DataflowMachine
  fifo : OutputFIFO g.outputs g.nodes
  idx : Member (FIFO.output fifo) g.fifos
  h_ty : fifo.t = p.toSDF

@[reducible]
def Step.Ty.toSDF (sty : Step.Ty) :=
  match sty with
    | .stream p => SDFOneOutput p

@[simp]
def binOpConstRightGraph {α β γ : Step.Prim} (op : SimpleDataflow.BinaryOp α.toSDF β.toSDF γ.toSDF) (c : β.denote) : SDFOneOutput γ :=
  let inputs := [α.toSDF]
  let outputs := [γ.toSDF]
  let constNode := ⟨[], [β.toSDF], [], []ₕ, .const c⟩
  let opNode := ⟨[α.toSDF, β.toSDF], [γ.toSDF], [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 2 := .cons constNode (.cons opNode .nil)
  have h_eq : (nodes.get 1).outputs = [γ.toSDF] := by aesop
  let outFifo : OutputFIFO outputs nodes := ⟨γ.toSDF, 1, h_eq ▸ .head, .head⟩
  let fifo := .output outFifo
  let fifos := [
    .input ⟨α.toSDF, .head, 1, .head⟩,
    .advancing ⟨β.toSDF, 0, 1, .head, .tail .head, _⟩,
    fifo
  ]
  let g : SimpleDataflow.DataflowMachine := ⟨inputs, outputs, 2, nodes, fifos⟩
  ⟨
    g,
    outFifo,
    .tail (.tail .head),
    by aesop
  ⟩

def binaryOpGraph {α β γ : Step.Prim} (op : SimpleDataflow.BinaryOp α.toSDF β.toSDF γ.toSDF) : SDFOneOutput γ :=
  let inputs := [α.toSDF, β.toSDF]
  let outputs := [γ.toSDF]
  let opNode : SDFNode := ⟨inputs, outputs, [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 1 := .cons opNode .nil
  let h_eq : (nodes.get 0).outputs = [γ.toSDF] := by aesop
  let outFifo : OutputFIFO outputs nodes := ⟨γ.toSDF, 0, h_eq ▸ .head, .head⟩
  let fifo := .output outFifo
  let fifos := [
    .input ⟨α.toSDF, .head, 0, .head⟩,
    .input ⟨β.toSDF, .tail .head, 0, .tail .head⟩,
    fifo
  ]
  let g := ⟨inputs, outputs, 1, nodes, fifos⟩
  ⟨
    g,
    (_ : outputs = g.outputs) ▸ outFifo,
    .tail (.tail .head),
    by aesop
  ⟩

def isOutputFifo {numNodes : Nat} {inputs outputs : List SimpleDataflow.Ty} {nodes : SDFNodeList numNodes}
  (outFifo : OutputFIFO outputs nodes) (fifo : FIFO inputs outputs nodes) : Bool :=
  match fifo with
    | .output f =>
      if h_t : f.t = outFifo.t then
        if h_p : f.producer = outFifo.producer then
          and (f.producerPort == (h_t ▸ h_p ▸ outFifo.producerPort)) (f.consumer == (h_t ▸ outFifo.consumer))
        else
          false
      else
        false
    | _ => false

def Step.UnaryOp.compile : Step.UnaryOp α β → SDFOneOutput β
  | .addConst c => binOpConstRightGraph .add c
  | .mulConst c => binOpConstRightGraph .mul c

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Ops [α.toSDF, β.toSDF] [γ.toSDF] []
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

def mergeGraphs (a : SDFOneOutput α) (b : SDFOneOutput β) (op : Step.BinaryOp α β γ) : SDFOneOutput γ :=
  let inputs := a.g.inputs ++ b.g.inputs
  let outputs := [γ.toSDF]
  let newNode : SDFNode := ⟨[α.toSDF, β.toSDF], [γ.toSDF], [], []ₕ, op.compile⟩
  let nodes := newNode ::ᵥ (a.g.nodes.append b.g.nodes)
  let aFifos := a.g.fifos.filter (isOutputFifo a.fifo)
  let bFifos := b.g.fifos.filter (isOutputFifo b.fifo)
  let aFifosUpdated : List (FIFO inputs outputs nodes) :=
    aFifos.map (
      λ fifo ↦ match fifo with
        | .input f =>
          let newConsumer : Fin nodes.length := ⟨f.consumer + 1, by
            have := f.consumer.isLt
            linarith
          ⟩
          have h_eq : nodes.get newConsumer = a.g.nodes.get f.consumer := by
            let consumerIdxApp : Fin (a.g.numNodes + b.g.numNodes) := ⟨f.consumer, by apply Nat.lt_add_right; exact f.consumer.isLt⟩
            rw [←nodes.get_tail consumerIdxApp]
            simp [nodes]
            apply Vector.get_append
          let fifo : InputFIFO inputs nodes := {
            producer := f.producer.append,
            consumer := newConsumer,
            consumerPort := h_eq ▸ f.consumerPort
          }
          .input fifo
        | .output f => sorry
        | .advancing f => sorry
        | .initialized f => sorry
    )
  sorry

def Step.Prog.compile {sty : Step.Ty} : Step.Prog sty → sty.toSDF
  | @Step.Prog.const α as => sorry
  | @Step.Prog.zip α β γ op as bs =>
    let asg := as.compile
    let bsg := bs.compile
    mergeGraphs asg bsg op
  | Step.Prog.map op as => sorry
  | @Step.Prog.reduce α β op len init bs => sorry
  decreasing_by (all_goals sorry)



-- def c : SimpleDataflow.Pipeline [] [SimpleDataflow.BoolTy] :=
--   .const 1

-- def g : SimpleDataflow.DataflowMachine :=
--   let inputs : List SimpleDataflow.Ty := []
--   let outputs : List SimpleDataflow.Ty := [SimpleDataflow.BoolTy]
--   let state : List SimpleDataflow.Ty := []
--   let pipeline : SimpleDataflow.Ops inputs outputs state := c
--   let node := ⟨inputs, outputs, state, []ₕ, pipeline⟩
--   let nodes : SDFNodeList 1 := .cons node .nil
--   let fifos := [
--     .output ⟨SimpleDataflow.BoolTy, 0, .head, .head⟩
--   ]
--   ⟨inputs, outputs, 1, nodes, fifos⟩

-- namespace _hidden
--   def w := 10
--   def add1 := binOpConstRight (.add (w := w)) 1
--   def mul1 := binOpConstRight (.mul (w := w)) 1
--   def s : Stream' (BitVec w) := λ n => ⟨n % (2 ^ w), by apply Nat.mod_lt; simp⟩
--   #eval ((add1.denote [s]ₕ).head 8).toNat
-- end _hidden
