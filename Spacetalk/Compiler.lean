import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph
import Spacetalk.Vector

def SDFNode := Node SimpleDataflow.Ty SimpleDataflow.Ops

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

@[reducible]
def Step.Ty.toSDF : Step.Ty → SimpleDataflow.Ty
  | bitVec w => .option (.bitVec w)

theorem ty_eq_option : ∀ sTy : Step.Ty, sTy.toSDF.denote = Option sTy.denote := by
  intro sTy
  simp

structure SDFConv (inputs : List Step.Ty) (output : Step.Ty) where
  g : SimpleDataflow.DataflowMachine

  inputs_eq : g.inputs = inputs.map Step.Ty.toSDF
  inputFifos : List (InputFIFO g.inputs g.nodes)
  only_inputs : FIFO.getInputs g.fifos = inputFifos

  output_eq : g.outputs = [output.toSDF]
  outputFifo : OutputFIFO g.outputs g.nodes
  only_output : FIFO.getOutputs g.fifos= [outputFifo]

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Ops [α.toSDF, β.toSDF] [γ.toSDF] []
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

class IndexConverter {α : Type u} {n m : Nat} (xs : Vector α n) (ys : Vector α m) :=
  newConsumer : Fin m
  conv : Fin n → Fin m
  conv_congr : ∀ {i}, xs.get i = ys.get (conv i)
  conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j
  conv_gt_consumer : ∀ {i}, newConsumer < conv i

-- def appendIdConverter : IndexConverter xs (xs.append ys) :=
--   let conv : Fin xs.length → Fin (xs.append ys).length := λ i ↦ ⟨i.val, by have := i.isLt; linarith⟩
--   have conv_congr : ∀ {i}, xs.get i = (xs.append ys).get (conv i) := by
--     intro i
--     simp [conv]
--     apply Vector.get_append_left.symm
--   have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by intro i j; simp [conv]
--   ⟨conv, conv_congr, conv_lt⟩

-- Assume new consumer is appended to the front
def consConverter : IndexConverter xs (x ::ᵥ xs.append ys) :=
  let conv : Fin xs.length → Fin (x ::ᵥ xs.append ys).length := λ i ↦ ⟨i.val + 1, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, xs.get i = (x ::ᵥ xs.append ys).get (conv i) := by
    intro i
    rw [←(x ::ᵥ xs.append ys).get_tail ⟨i, Nat.lt_add_right _ i.isLt⟩]
    exact Vector.get_append_left.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, 0 < conv i := by
    intro i
    simp [conv]
    apply Fin.mk_lt_mk.mpr
    rw [Nat.zero_mod]
    simp
  ⟨0, conv, conv_congr, conv_lt, conv_gt_zero⟩

-- Assume new consumer is appended to the front
def consAppendConverter {xs : Vector α n} {ys : Vector α m} : IndexConverter ys (x ::ᵥ xs.append ys) :=
  let conv : Fin m → Fin (n + m + 1) := λ i ↦ ⟨i.val + n + 1, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, ys.get i = (x ::ᵥ xs.append ys).get (conv i) := by
    intro i
    simp [conv]
    rw [←(x ::ᵥ xs.append ys).get_tail ⟨i + n, by simp; have := i.isLt; linarith⟩]
    simp
    exact Vector.get_append_right.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  have conv_gt_zero: ∀ {i}, 0 < conv i := by
    intro i
    simp [conv]
    apply Fin.mk_lt_mk.mpr
    rw [Nat.zero_mod]
    simp
  ⟨0, conv, conv_congr, conv_lt, conv_gt_zero⟩

def appendConverter {xs : Vector α n} {ys : Vector α m} (newConsumer : Fin n) : IndexConverter ys (xs.append ys) :=
  let conv : Fin m → Fin (n + m) := λ i ↦ ⟨i.val + n, by have := i.isLt; linarith⟩
  have conv_congr : ∀ {i}, ys.get i = (xs.append ys).get (conv i) := by
    intro i
    exact Vector.get_append_right.symm
  have conv_lt : ∀ ⦃i j⦄, i < j → conv i < conv j := by simp [conv]
  let newConsumer' : Fin (n + m) := ⟨newConsumer.val, Nat.lt_add_right m newConsumer.isLt⟩
  have conv_gt_consumer: ∀ {i}, newConsumer' < conv i := by
    intro i
    simp [conv, newConsumer']
    have := newConsumer.isLt
    linarith
  ⟨newConsumer', conv, conv_congr, conv_lt, conv_gt_consumer⟩

/-- Assume new consumer has index 0. -/
def convertFifosOutput {inputs outputs : List SimpleDataflow.Ty} {numNodes : Nat} {nodes : SDFNodeList numNodes}
  (h_len : 0 < numNodes) (a : SDFConv aInp α)
  (idxConv : IndexConverter a.g.nodes nodes)
  (newConsumerPort : Member α.toSDF (nodes.get idxConv.newConsumer).inputs)
  (memConv : {t : SimpleDataflow.Ty} → Member t a.g.inputs → Member t inputs)
  : List (FIFO inputs outputs nodes) :=
  a.g.fifos.attach.map (
    λ ⟨fifo, _⟩ ↦ match fifo with
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
        have h_ty_eq : α.toSDF = f.t := by
          have : FIFO.output f = .output a.outputFifo := by
            apply List.mem_singleton.mp
            rw [←List.map_singleton, ←a.only_output]
            aesop
          simp [FIFO.output.inj] at this
          rw [this]
          have h_output_in_output : a.outputFifo.t ∈ a.g.outputs := a.outputFifo.consumer.to_mem
          simp [a.output_eq] at h_output_in_output
          exact h_output_in_output.symm
        let fifo : AdvancingFIFO nodes := {
          t := f.t,
          producer := newProducer,
          consumer := idxConv.newConsumer,
          producerPort := idxConv.conv_congr ▸ f.producerPort,
          consumerPort := h_ty_eq ▸ newConsumerPort,
          adv := idxConv.conv_gt_consumer,
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

theorem convertFifos_no_output
  {a : SDFConv aInp α}
  {h_len : 0 < numNodes}
  {idxConv : IndexConverter a.g.nodes nodes}
  {newConsumerPort : Member α.toSDF (nodes.get idxConv.newConsumer).inputs}
  {memConv : {t : SimpleDataflow.Ty} → Member t a.g.inputs → Member t inputs}
  : FIFO.getOutputs (convertFifosOutput h_len a idxConv newConsumerPort memConv) (outputs := outputs) = [] := by
  simp [List.eq_nil_iff_forall_not_mem, List.mem_filterMap]
  intro _ fifo h_mem
  have h_map := List.mem_map.mp h_mem
  let ⟨⟨fifo', _⟩, ⟨_, h_match⟩⟩ := h_map
  cases fifo' <;> (simp at h_match; rw [←h_match]; simp [FIFO.isOutput])

def constStreamGraph (α : Step.Ty) : SDFConv [α] α :=
  let inputs : List SimpleDataflow.Ty := [α.toSDF]
  let outputs : List SimpleDataflow.Ty := [α.toSDF]
  let nodes : SDFNodeList 1 := ⟨inputs, outputs, [], []ₕ, .unaryOp .identity⟩ ::ᵥ .nil
  let inputFifo : InputFIFO inputs nodes := ⟨α.toSDF, .head, 0, .head⟩
  let outputFifo : OutputFIFO outputs nodes := ⟨α.toSDF, 0, .head, .head⟩
  let fifos := [.input inputFifo, .output outputFifo]
  let graph : SimpleDataflow.DataflowMachine := ⟨inputs, outputs, 1, nodes, fifos⟩
  {
    g := graph,
    inputs_eq := rfl,
    inputFifos := [inputFifo],
    only_inputs := by simp [List.filterMap],
    output_eq := rfl,
    outputFifo := outputFifo,
    only_output := by simp [List.filterMap]
  }

def zipGraph (op : Step.BinaryOp α β γ) (a : SDFConv aInp α) (b : SDFConv bInp β) : SDFConv (aInp ++ bInp) γ :=
  let inputs := a.g.inputs ++ b.g.inputs
  let outputs := [γ.toSDF]
  let opNode : SDFNode := ⟨[α.toSDF, β.toSDF], outputs, [], []ₕ, op.compile⟩
  let nodes := opNode ::ᵥ (a.g.nodes.append b.g.nodes)

  let aFifosConverted : List (FIFO inputs outputs nodes) := convertFifosOutput (Nat.zero_lt_succ _) a consConverter .head .append_left
  let bFifosConverted : List (FIFO inputs outputs nodes) := convertFifosOutput (Nat.zero_lt_succ _) b consAppendConverter (.tail .head) .append_right

  let newOutputFifo : OutputFIFO outputs nodes := ⟨γ.toSDF, 0, .head, .head⟩
  let newFifos := .output newOutputFifo :: (aFifosConverted ++ bFifosConverted)
  let newGraph : SimpleDataflow.DataflowMachine := ⟨inputs, outputs, nodes.length, nodes, newFifos⟩

  have one_output : FIFO.getOutputs newFifos = [newOutputFifo] := by
    simp [newFifos, FIFO.isOutput, List.filterMap_append]
    apply And.intro convertFifos_no_output convertFifos_no_output

  let inputFifos := (FIFO.getInputs aFifosConverted) ++ (FIFO.getInputs bFifosConverted)

  have only_inputs : FIFO.getInputs newFifos = inputFifos := by
    simp [inputFifos, newFifos, List.filterMap_append]

  {
    g := newGraph,

    inputs_eq := by simp; rw [←a.inputs_eq, ←b.inputs_eq],
    inputFifos := inputFifos,
    only_inputs := only_inputs,

    output_eq := rfl,
    outputFifo := newOutputFifo,
    only_output := one_output,
  }

def constValueGraph {t : Step.Ty} (c : t.denote) : SDFConv [] t :=
  let constOutFifo := ⟨t.toSDF, 0, .head, .head⟩
  let constGraph : SimpleDataflow.DataflowMachine := ⟨
    [],
    [t.toSDF],
    1,
    ⟨[], [t.toSDF], [], []ₕ, SimpleDataflow.Pipeline.const c⟩ ::ᵥ .nil,
    [.output constOutFifo]
  ⟩
  ⟨constGraph, rfl, [], rfl, rfl, constOutFifo, rfl⟩

def mapGraph (op : Step.UnaryOp α β) (a : SDFConv inp α) : SDFConv inp β :=
  match op with
  | .addConst c => zipGraph .add (constValueGraph c) a
  | .mulConst c => zipGraph .mul (constValueGraph c) a

theorem Fin.gt_of_val_gt {a b : Fin n} : a.val > b.val → a > b := by intro h; exact h

set_option maxHeartbeats 900000
def reduceBlock {α β : Step.Ty}
  (op : Step.BinaryOp α β α) (len : Nat) (init : α.denote) (b : SDFConv inp β)
  : SDFConv inp α :=
  let ctrWidth := (Nat.log2 len) + 1
  let ctrTy : SimpleDataflow.Ty := SimpleDataflow.BitVecTy ctrWidth

  let redux : SDFNode := ⟨[α.toSDF, β.toSDF], [α.toSDF], [], []ₕ, op.compile⟩

  let constZero : SDFNode := ⟨[], [ctrTy], [], []ₕ, .const (some 0)⟩
  let constOne : SDFNode := ⟨[], [ctrTy], [], []ₕ, .const (some 1)⟩
  let constLen : SDFNode := ⟨[], [ctrTy], [], []ₕ, .const (some len)⟩
  let constInit : SDFNode := ⟨[], [α.toSDF], [], []ₕ, .const (some init)⟩

  let ctrUpdate : SDFNode := ⟨[ctrTy, ctrTy], [ctrTy], [], []ₕ, .binaryOp .add⟩
  let ctrMod : SDFNode := ⟨[ctrTy, ctrTy], [ctrTy], [], []ₕ, .binaryOp .umod⟩
  let ctrComp : SDFNode := ⟨[ctrTy, ctrTy], [SimpleDataflow.BoolTy], [], []ₕ, .binaryOp .eq⟩

  let outputGuard : SDFNode := ⟨[SimpleDataflow.BoolTy, α.toSDF], [α.toSDF], [], []ₕ, .guard⟩
  let accMux : SDFNode := ⟨[SimpleDataflow.BoolTy, α.toSDF, α.toSDF], [α.toSDF], [], []ₕ, .mux⟩
  let ctrMux : SDFNode := ⟨[SimpleDataflow.BoolTy, ctrTy, ctrTy], [ctrTy], [], []ₕ, .mux⟩

  let newNodes : SDFNodeList 11 := (
    outputGuard ::ᵥ accMux ::ᵥ redux ::ᵥ
    ctrMux ::ᵥ ctrComp ::ᵥ ctrMod ::ᵥ ctrUpdate ::ᵥ
    constLen ::ᵥ constOne ::ᵥ constZero ::ᵥ constInit ::ᵥ .nil
  )
  let nodes : SDFNodeList (11 + b.g.nodes.length) := newNodes.append b.g.nodes
  have h_lt {i : Nat} (h : i < 11) : i < nodes.length := Nat.lt_add_right b.g.nodes.length h

  let outputGuardIdx : Fin nodes.length := ⟨0, h_lt (by linarith)⟩
  let accMuxIdx : Fin nodes.length := ⟨1, h_lt (by linarith)⟩
  let reduxIdx : Fin nodes.length := ⟨2, h_lt (by linarith)⟩
  let ctrMuxIdx : Fin nodes.length := ⟨3, h_lt (by linarith)⟩
  let ctrCompIdx : Fin nodes.length := ⟨4, h_lt (by linarith)⟩
  let ctrModIdx : Fin nodes.length := ⟨5, h_lt (by linarith)⟩
  let ctrUpdateIdx : Fin nodes.length := ⟨6, h_lt (by linarith)⟩
  let constLenIdx : Fin nodes.length := ⟨7, h_lt (by linarith)⟩
  let constOneIdx : Fin nodes.length := ⟨8, h_lt (by linarith)⟩
  let constZeroIdx : Fin nodes.length := ⟨9, h_lt (by linarith)⟩
  let constInitIdx : Fin nodes.length := ⟨10, h_lt (by linarith)⟩

  let inputs := b.g.inputs
  let outputs := [α.toSDF]

  let bFifosConverted : List (FIFO inputs outputs nodes) := convertFifosOutput (by linarith) b (appendConverter reduxIdx) (.tail .head) id

  let newFifos : List (FIFO inputs outputs nodes) := [
    .initialized ⟨α.toSDF, some init, accMuxIdx, reduxIdx, .head, .head⟩, -- accumulated value
    .advancing ⟨α.toSDF, reduxIdx, accMuxIdx, .head, .tail .head, Fin.gt_of_val_gt (by linarith)⟩, -- redux output
    .advancing ⟨α.toSDF, constInitIdx, accMuxIdx, .head, .tail (.tail .head), Fin.gt_of_val_gt (by linarith)⟩, -- redux initial value
    .advancing ⟨SimpleDataflow.BoolTy, ctrCompIdx, accMuxIdx, .head, .head, Fin.gt_of_val_gt (by linarith)⟩, -- accum mux condition
    .advancing ⟨SimpleDataflow.BoolTy, ctrCompIdx, outputGuardIdx, .head, .head, Fin.gt_of_val_gt (by linarith)⟩,
    .advancing ⟨α.toSDF, reduxIdx, outputGuardIdx, .head, .tail .head, Fin.gt_of_val_gt (by linarith)⟩,
    .output ⟨α.toSDF, outputGuardIdx, .head, .head⟩,

    .initialized ⟨ctrTy, some 0, ctrModIdx, ctrUpdateIdx, .head, .head⟩, -- ctr + 1 - left arg
    .advancing ⟨ctrTy, constOneIdx, ctrUpdateIdx, .head, .tail .head, Fin.gt_of_val_gt (by linarith)⟩, -- ctr + 1 - right arg
    .advancing ⟨ctrTy, ctrUpdateIdx, ctrModIdx, .head, .head, Fin.gt_of_val_gt (by linarith)⟩, -- ctr % len - left arg
    .advancing ⟨ctrTy, constLenIdx, ctrModIdx, .head, .tail .head, Fin.gt_of_val_gt (by linarith)⟩, -- ctr % len - right arg
    .advancing ⟨ctrTy, ctrModIdx, ctrCompIdx, .head, .head, Fin.gt_of_val_gt (by linarith)⟩, -- ctr == 0 - left arg
    .advancing ⟨ctrTy, constZeroIdx, ctrCompIdx, .head, .tail .head, Fin.gt_of_val_gt (by linarith)⟩, -- ctr == 0 - right arg
  ]
  sorry

def Step.Prog.compile {inp : List Ty} {out : Ty} : Step.Prog inp out → SDFConv inp out
  | .const α => constStreamGraph α
  | .zip op as bs => zipGraph op as.compile bs.compile
  | .map op as => mapGraph op as.compile
  | .reduce op len init bs => reduceBlock op len init bs.compile
