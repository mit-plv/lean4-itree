import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.Vector.Basic

theorem Vector.get_append_left {xs : Vector α n} {ys : Vector α m} {i : Fin n}
  : (xs.append ys).get ⟨i, by apply Nat.lt_add_right; exact i.isLt⟩ = xs.get i := by
  apply List.get_append_left

theorem Vector.get_append_right {xs : Vector α n} {ys : Vector α m} {i : Fin m}
  : (xs.append ys).get ⟨i + n, by have := i.isLt; linarith⟩ = ys.get i := by
  simp_rw [Vector.get_eq_get]
  have := Vector.toList_append xs ys
  rw [List.get_of_eq this]
  simp [Fin.cast]
  have := List.get_append_right xs.toList ys.toList (i := i + n)
  have h_i_lt_append : ↑i + n < (xs.toList ++ ys.toList).length := by have := i.isLt; simp; linarith
  have h_i_sub_xs_lt_ys : ↑i + n - xs.toList.length < ys.toList.length := by simp
  have : List.get (xs.toList ++ ys.toList) ⟨↑i + n, h_i_lt_append⟩ = List.get ys.toList ⟨i + n - xs.toList.length, h_i_sub_xs_lt_ys⟩ := this (by rw [Vector.toList_length xs]; linarith)
  have h_eq : (⟨↑i + n - xs.toList.length, h_i_sub_xs_lt_ys⟩ : Fin ys.toList.length) = ⟨↑i, Fin.cast.proof_1 (toList_length ys).symm i⟩ := by simp
  rw [←h_eq]
  exact this

def SDFNode := Node SimpleDataflow.Ty SimpleDataflow.Ops

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

def Step.Prim.toSDF : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .prim (.bitVec w)

def Step.Prim.toSDFOpt : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .option (.bitVec w)

structure SDFOneOutput (p : Step.Prim) where
  g : SimpleDataflow.DataflowMachine
  fifo : OutputFIFO g.outputs g.nodes
  one_output : g.fifos.filter FIFO.isOutput = [.output fifo]
  ty_eq : fifo.t = p.toSDF

structure SDFOneInputOneOutput (α β : Step.Prim) where
  g : SimpleDataflow.DataflowMachine
  inpFifo : InputFIFO g.inputs g.nodes
  one_input : g.fifos.filter FIFO.isInput = [.input inpFifo]
  inp_ty_eq : inpFifo.t = α.toSDF
  outFifo : OutputFIFO g.outputs g.nodes
  one_output : g.fifos.filter FIFO.isOutput = [.output outFifo]
  out_ty_eq : outFifo.t = β.toSDF
  nodes_len : 0 < g.numNodes
  out_producer : outFifo.producer = ⟨0, nodes_len⟩
  consumerPort : Member α.toSDF (g.nodes.get ⟨0, nodes_len⟩).inputs
  output_eq : g.outputs = [β.toSDF]

@[reducible]
def Step.Ty.toSDF (sty : Step.Ty) :=
  match sty with
    | .stream p => SDFOneOutput p

/-- The node doing the operation is the first, and its first input port is the external input. -/
@[simp]
def binOpConstRightGraph {α β γ : Step.Prim} (op : SimpleDataflow.BinaryOp α.toSDF β.toSDF γ.toSDF) (c : β.denote) : SDFOneInputOneOutput α γ :=
  let inputs := [α.toSDF]
  let outputs := [γ.toSDF]
  let constNode := ⟨[], [β.toSDF], [], []ₕ, .const c⟩
  let opNode := ⟨[α.toSDF, β.toSDF], [γ.toSDF], [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 2 := .cons opNode (.cons constNode .nil)
  have h_in_eq : (nodes.get 0).inputs = [α.toSDF, β.toSDF] := by aesop
  have h_out_eq : (nodes.get 0).outputs = [γ.toSDF] := by aesop
  let inpFifo : InputFIFO inputs nodes := ⟨α.toSDF, .head, 0, h_in_eq ▸ .head⟩
  let outFifo : OutputFIFO outputs nodes := ⟨γ.toSDF, 0, h_out_eq ▸ .head, .head⟩
  let fifos := [
    .input inpFifo,
    .advancing ⟨β.toSDF, 1, 0, .head, .tail .head, by simp⟩,
    .output outFifo
  ]
  let g : SimpleDataflow.DataflowMachine := ⟨inputs, outputs, 2, nodes, fifos⟩
  ⟨
    g,
    inpFifo,
    by simp [fifos],
    by simp,
    outFifo,
    by simp [fifos, FIFO.isOutput],
    by simp,
    by simp,
    rfl,
    .head,
    rfl
  ⟩

def Step.UnaryOp.compile : Step.UnaryOp α β → SDFOneInputOneOutput α β
  | .addConst c => binOpConstRightGraph .add c
  | .mulConst c => binOpConstRightGraph .mul c

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Ops [α.toSDF, β.toSDF] [γ.toSDF] []
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

class IndexConverter {α : Type u} {n m : Nat} (xs : Vector α n) (ys : Vector α m) :=
  conv : Fin n → Fin m
  conv_congr : ∀ {i}, xs.get i = ys.get (conv i)
  conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j

class IndexConverterGtZero {α : Type u} {n m : Nat} (xs : Vector α n) (ys : Vector α m) extends IndexConverter xs ys :=
  conv_gt_zero: ∀ {i}, (h_m : 0 < m) → ⟨0, h_m⟩ < conv i

def appendIdConverter : IndexConverter xs (xs.append ys) :=
  let conv : Fin xs.length → Fin (xs.append ys).length := λ i ↦ ⟨i.val, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, xs.get i = (xs.append ys).get (conv i) := by
    intro i
    simp [conv]
    apply Vector.get_append_left.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by intro i j; simp [conv]
  ⟨conv, conv_congr, conv_lt⟩

def consConverter : IndexConverterGtZero xs (x ::ᵥ xs.append ys) :=
  let conv : Fin xs.length → Fin (x ::ᵥ xs.append ys).length := λ i ↦ ⟨i.val + 1, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, xs.get i = (x ::ᵥ xs.append ys).get (conv i) := by
    intro i
    rw [←(x ::ᵥ xs.append ys).get_tail ⟨i, Nat.lt_add_right _ i.isLt⟩]
    exact Vector.get_append_left.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, _ → 0 < conv i := by
    intro i
    simp [conv]
    apply Fin.mk_lt_mk.mpr
    rw [Nat.zero_mod]
    simp
  .mk conv_gt_zero (toIndexConverter := ⟨conv, conv_congr, conv_lt⟩)

def consAppendConverter {xs : Vector α n} {ys : Vector α m} : IndexConverterGtZero ys (x ::ᵥ xs.append ys) :=
  let conv : Fin m → Fin (n + m + 1) := λ i ↦ ⟨i.val + n + 1, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, ys.get i = (x ::ᵥ xs.append ys).get (conv i) := by
    intro i
    simp [conv]
    rw [←(x ::ᵥ xs.append ys).get_tail ⟨i + n, by simp; have := i.isLt; linarith⟩]
    simp
    exact Vector.get_append_right.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, _ → 0 < conv i := by
    intro i
    simp [conv]
    apply Fin.mk_lt_mk.mpr
    rw [Nat.zero_mod]
    simp
  .mk conv_gt_zero (toIndexConverter := ⟨conv, conv_congr, conv_lt⟩)

def appendConverter {xs : Vector α n} {ys : Vector α m} (h_n : 0 < n) : IndexConverterGtZero ys (xs.append ys) :=
  let conv : Fin m → Fin (n + m) := λ i ↦ ⟨i.val + n, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, ys.get i = (xs.append ys).get (conv i) := by
    intro i
    exact Vector.get_append_right.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, (h_m : 0 < n + m) → ⟨0, h_m⟩ < conv i := by
    intro i h_m
    simp [conv]
    apply Or.intro_right
    exact h_n
  .mk conv_gt_zero (toIndexConverter := ⟨conv, conv_congr, conv_lt⟩)

/-- Assume new consumer has index 0. -/
def convertFifosOutput {inputs outputs : List SimpleDataflow.Ty} {numNodes : Nat} {nodes : SDFNodeList numNodes}
  (h_len : 0 < numNodes) (a : SDFOneOutput α) (newConsumerPort : Member α.toSDF (nodes.get ⟨0, h_len⟩).inputs)
  (idxConv : IndexConverterGtZero a.g.nodes nodes)
  (memConv : {t : SimpleDataflow.Ty} → Member t a.g.inputs → Member t inputs)
  : List (FIFO inputs outputs nodes) :=
  a.g.fifos.attach.map (
    λ ⟨fifo, h_mem⟩ ↦ match fifo with
      | .input f =>
        let newConsumer := idxConv.conv f.consumer
        let fifo : InputFIFO inputs nodes := {
          t := f.t,
          producer := memConv f.producer,
          consumer := newConsumer,
          consumerPort := idxConv.conv_congr ▸ f.consumerPort
        }
        .input fifo
      | .output f =>
        let newProducer := idxConv.conv f.producer
        have h_ty_eq : f.t = α.toSDF := by
          have : FIFO.output f = .output a.fifo := by
            apply List.mem_singleton.mp
            rw [←a.one_output]
            apply List.mem_filter.mpr (And.intro h_mem (by rfl))
          simp [FIFO.output.inj] at this
          rw [this]
          apply a.ty_eq
        let fifo : AdvancingFIFO nodes := {
          t := f.t,
          producer := newProducer,
          consumer := ⟨0, h_len⟩,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := h_ty_eq ▸ newConsumerPort,
          adv := idxConv.conv_gt_zero h_len,
        }
        .advancing fifo
      | .advancing f =>
        let fifo : AdvancingFIFO nodes := {
          t := f.t,
          producer := idxConv.conv f.producer,
          consumer := idxConv.conv f.consumer,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := idxConv.conv_congr ▸ f.consumerPort,
          adv := idxConv.conv_lt f.adv
        }
        .advancing fifo
      | .initialized f =>
        let newProducer := idxConv.conv f.producer
        let newConsumer := idxConv.conv f.consumer
        let fifo : InitializedFIFO nodes := {
          t := f.t,
          initialValue := f.initialValue,
          producer := newProducer,
          consumer := newConsumer,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := idxConv.conv_congr ▸ f.consumerPort,
        }
        .initialized fifo
  )

theorem convertFifos_no_output {inputs outputs : List SimpleDataflow.Ty} {numNodes : Nat} {nodes : SDFNodeList numNodes}
  {h_len : 0 < numNodes} {a : SDFOneOutput α} {newConsumerPort : Member α.toSDF (nodes.get ⟨0, h_len⟩).inputs}
  {idxConv : IndexConverterGtZero a.g.nodes nodes}
  {memConv : {t : SimpleDataflow.Ty} → Member t a.g.inputs → Member t inputs}
 : (convertFifosOutput h_len a newConsumerPort idxConv memConv).filter
      (@FIFO.isOutput SimpleDataflow.Ty _ _ SimpleDataflow.Ops _ numNodes nodes inputs outputs)
    = [] := by
  apply List.filter_eq_nil.mpr
  intro fifo h_mem
  have h_map := List.mem_map.mp h_mem
  let ⟨⟨fifo', _⟩, ⟨_, h_match⟩⟩ := h_map
  cases fifo' <;> (simp at h_match; rw [←h_match]; simp [FIFO.isOutput])

def SDFOneInputOneOutput.convertFifosDropInput {numNodes : Nat} {nodes : SDFNodeList numNodes} {inputs : List SimpleDataflow.Ty}
  (a : SDFOneInputOneOutput α β) (idxConv : IndexConverter a.g.nodes nodes)
  : List (FIFO inputs [β.toSDF] nodes) :=
  let filtered := a.g.fifos.filter (λ fifo ↦ (fifo.isInput = false) && (fifo.isOutput = false))
  filtered.attach.map (
    λ ⟨fifo, h_mem⟩ ↦
      have h_not_input : (fifo.isInput = false) ∧ (fifo.isOutput = false) := by
        have := (List.mem_filter.mp h_mem).right
        rw [←Bool.decide_and] at this
        exact of_decide_eq_true this
      match fifo, h_not_input with
      | .initialized fifo, _ =>
        .initialized {
          t := fifo.t,
          initialValue := fifo.initialValue,
          producer := idxConv.conv fifo.producer,
          consumer := idxConv.conv fifo.consumer,
          producerPort := idxConv.conv_congr ▸ fifo.producerPort,
          consumerPort := idxConv.conv_congr ▸ fifo.consumerPort
        }
      | .advancing fifo, _ =>
        .advancing {
          t := fifo.t,
          producer := idxConv.conv fifo.producer,
          consumer := idxConv.conv fifo.consumer,
          producerPort := idxConv.conv_congr ▸ fifo.producerPort,
          consumerPort := idxConv.conv_congr ▸ fifo.consumerPort,
          adv := idxConv.conv_lt fifo.adv
        }
  )

theorem SDFOneInputOneOutput.convertFifosDropInput_no_output {numNodes : Nat} {nodes : SDFNodeList numNodes} {inputs : List SimpleDataflow.Ty}
  {a : SDFOneInputOneOutput α β} {idxConv : IndexConverter a.g.nodes nodes}
  : (@SDFOneInputOneOutput.convertFifosDropInput α β numNodes nodes inputs a idxConv).filter FIFO.isOutput = [] := by
  simp only [SDFOneInputOneOutput.convertFifosDropInput]
  apply List.filter_eq_nil.mpr
  intro fifo h_mem
  have := List.mem_map.mp h_mem
  clear h_mem
  let ⟨fifo', h_mem⟩ := this
  clear this
  rw [←h_mem.right]
  clear h_mem
  let ⟨fifo'', h_filter⟩ := fifo'
  have := (List.mem_filter.mp h_filter).right
  simp only [Bool.and_eq_true] at this
  have := this.right
  have := of_decide_eq_true this
  split <;> simp [FIFO.isOutput]

def mergeTwoGraphs (a : SDFOneOutput α) (opGraph : SDFOneInputOneOutput α β) : SDFOneOutput β :=
  let inputs := a.g.inputs
  let outputs := [β.toSDF]
  let nodes := opGraph.g.nodes.append a.g.nodes
  have h_len_app : 0 < opGraph.g.numNodes + a.g.numNodes := Nat.lt_add_right _ opGraph.nodes_len
  have h_nodes_eq : nodes.get ⟨0, h_len_app⟩ = opGraph.g.nodes.get ⟨0, opGraph.nodes_len⟩ := Vector.get_append_left (xs := opGraph.g.nodes) (ys := a.g.nodes) (i := ⟨0, opGraph.nodes_len⟩)
  let aFifosUpdated : List (FIFO inputs outputs nodes) := convertFifosOutput h_len_app a (h_nodes_eq ▸ opGraph.consumerPort) (appendConverter opGraph.nodes_len) id
  let opGraphFifosUpdated : List (FIFO inputs outputs nodes) := opGraph.convertFifosDropInput appendIdConverter

  let outIdx := ⟨0, h_len_app⟩
  have h_producer_eq : opGraph.g.nodes.get opGraph.outFifo.producer = nodes.get outIdx := by
    rw [opGraph.out_producer]
    apply Vector.get_append_left.symm
  let newOutFifo : OutputFIFO outputs nodes := {
    t := β.toSDF,
    producer := outIdx,
    producerPort := opGraph.out_ty_eq ▸ h_producer_eq ▸ opGraph.outFifo.producerPort,
    consumer := .head
  }

  let newFifos := .output newOutFifo :: aFifosUpdated ++ opGraphFifosUpdated

  let newGraph : SimpleDataflow.DataflowMachine := {
    inputs := inputs,
    outputs := outputs,
    numNodes := nodes.length,
    nodes := nodes,
    fifos := newFifos
  }

  have one_output : newGraph.fifos.filter FIFO.isOutput = [.output newOutFifo] := by
    simp [newFifos, FIFO.isOutput]
    rw [convertFifos_no_output]
    simp
    exact opGraph.convertFifosDropInput_no_output

  {
    g := newGraph,
    fifo := newOutFifo,
    one_output := one_output,
    ty_eq := rfl
  }

def mergeThreeGraphs (a : SDFOneOutput α) (b : SDFOneOutput β) (op : Step.BinaryOp α β γ) : SDFOneOutput γ :=
  let inputs := a.g.inputs ++ b.g.inputs
  let outputs := [γ.toSDF]
  let newNode : SDFNode := ⟨[α.toSDF, β.toSDF], outputs, [], []ₕ, op.compile⟩
  let nodes := newNode ::ᵥ (a.g.nodes.append b.g.nodes)

  let aFifosUpdated : List (FIFO inputs outputs nodes) := convertFifosOutput (Nat.zero_lt_succ _) a .head consConverter .append_left
  let bFifosUpdated : List (FIFO inputs outputs nodes) := convertFifosOutput (Nat.zero_lt_succ _) b (.tail .head) consAppendConverter .append_right

  let newOutputFifo : OutputFIFO outputs nodes := {
    t := γ.toSDF,
    producer := 0,
    producerPort := .head,
    consumer := .head
  }
  let newFifos := .output newOutputFifo :: (aFifosUpdated ++ bFifosUpdated)
  let newGraph : SimpleDataflow.DataflowMachine := {
    inputs := inputs,
    outputs := outputs,
    numNodes := nodes.length,
    nodes := nodes,
    fifos := newFifos
  }

  have one_output : newGraph.fifos.filter FIFO.isOutput = [.output newOutputFifo] := by
    simp [newFifos, FIFO.isOutput]
    apply And.intro convertFifos_no_output convertFifos_no_output

  {
    g := newGraph,
    fifo := newOutputFifo,
    one_output := one_output,
    ty_eq := rfl
  }

def reduceBlock {α β : Step.Prim}
  (op : Step.BinaryOp α β α) (len : Nat) (init : α.denote) (bs : SDFOneOutput β)
  : SDFOneOutput α :=
  -- Counter Logic
  let ctrWidth := (Nat.log2 len) + 1
  let ctrTy : SimpleDataflow.Ty := .prim (.bitVec ctrWidth)
  let constOne : SDFNode := ⟨[], [ctrTy], [], []ₕ, .const 1⟩
  let ctrUpdate : SDFNode := ⟨[ctrTy], [ctrTy], [ctrTy], [.zero ctrWidth]ₕ, .comp .dup (.binaryOp .add)⟩
  let constLen : SDFNode := ⟨[], [ctrTy], [], []ₕ, .const len⟩
  let ctrMod : SDFNode := ⟨[ctrTy, ctrTy], [ctrTy], [], []ₕ, .binaryOp .umod⟩



  let nodes : SDFNodeList _ := ctrMod ::ᵥ constLen ::ᵥ ctrUpdate ::ᵥ constOne ::ᵥ .nil;
  sorry

def Step.Prog.compileAux {inp : List Step.Ty} {out : Step.Ty} : Step.Prog inp out → out.toSDF
  | .const α =>
    let inputs : List SimpleDataflow.Ty := [α.prim.toSDF]
    let outputs : List SimpleDataflow.Ty := [α.prim.toSDF]
    let nodes : SDFNodeList 1 := {
      inputs := inputs,
      outputs := outputs,
      state := [],
      initialState := []ₕ,
      ops := .unaryOp .identity
    } ::ᵥ .nil
    let inputFifo := {
      t := α.prim.toSDF,
      producer := .head,
      consumer := 0,
      consumerPort := .head
    }
    let outputFifo := {
      t := α.prim.toSDF,
      producer := 0,
      producerPort := .head,
      consumer := .head,
    }
    let graph : SimpleDataflow.DataflowMachine := {
      inputs := inputs,
      outputs := outputs,
      numNodes := 1,
      nodes := nodes,
      fifos := [
        .input inputFifo,
        .output outputFifo
      ]
    }
    {
      g := graph,
      fifo := outputFifo,
      one_output := by simp [FIFO.isOutput],
      ty_eq := by simp [outputFifo]
    }
  | .zip op as bs =>
    let asg := as.compileAux
    let bsg := bs.compileAux
    mergeThreeGraphs asg bsg op
  | Step.Prog.map op as => mergeTwoGraphs as.compileAux op.compile
  | .reduce op len init bs => reduceBlock op len init bs.compileAux

def Step.Prog.compile (prog : Step.Prog inp out) : SimpleDataflow.DataflowMachine :=
  prog.compileAux.g

namespace Example
  def bitVec32Stream : Step.Ty := .stream (.bitVec 32)
  def f : Step.Prog [bitVec32Stream, bitVec32Stream] bitVec32Stream :=
    .zip .mul
      (.map (.addConst 1) (.const bitVec32Stream))
      (.map (.addConst 2) (.const bitVec32Stream))

  def fEval := f.denote
  def fcEval := f.compile.denote

  def inputs : HList id [Stream' (BitVec 32), Stream' (BitVec 32)] := [(·), (·)]ₕ
  -- def a := fcEval inputs
end Example
