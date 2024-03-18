import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

def Step.Prim.toSDF : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .prim (.bitVec w)

def Step.Prim.toSDFOpt : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .option (.bitVec w)

def Step.UnaryOp.compile : Step.UnaryOp α β → SimpleDataflow.Pipeline [α.toSDF] [β.toSDF]
  | .addConst c => .comp (.binaryOp .add) (.par (.id (tys := [α.toSDF])) (.const c))
  | .mulConst c => .comp (.binaryOp .mul) (.par (.id (tys := [α.toSDF])) (.const c))

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Pipeline [α.toSDF, β.toSDF] [γ.toSDF]
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

def ReductionOps (α β : Step.Prim) (len : Nat) :=
  let ctrWidth : Nat := (Nat.log2 len) + 1
  let ctrType : SimpleDataflow.Ty := .prim (.bitVec ctrWidth)
  SimpleDataflow.Ops [β.toSDF] [α.toSDFOpt] [α.toSDF, ctrType]

def reductionBlock {α β : Step.Prim} (op : Step.BinaryOp α β α) (len : Nat) (init : α.denote) : ReductionOps α β len :=
  let ctrWidth : Nat := (Nat.log2 len) + 1
  let ctrType : SimpleDataflow.Ty := .prim (.bitVec ctrWidth)
  let ctrInc : SimpleDataflow.Pipeline [ctrType] [ctrType] :=
    .comp (.binaryOp .add) (.par (.id (tys := [ctrType])) (.const 1))
  let ctrMod : SimpleDataflow.Pipeline [ctrType] [ctrType] :=
    .comp (.binaryOp .umod) (.par (.id (tys := [ctrType])) (.const len))
  let ctrUpdate : SimpleDataflow.Pipeline [ctrType] [ctrType] :=
    .comp ctrMod ctrInc
  let accum : SimpleDataflow.Pipeline [β.toSDF, α.toSDF] [α.toSDF] :=
    .comp op.compile .swap
  let output : SimpleDataflow.Pipeline [SimpleDataflow.BoolTy, α.toSDF] [α.toSDFOpt] :=
    .comp .mux (.par (.id (tys := [SimpleDataflow.BoolTy])) (.par (.unaryOp .some) (.const none)))
  let accumUpdate : SimpleDataflow.Pipeline [SimpleDataflow.BoolTy, α.toSDF] [α.toSDF] :=
    .comp .mux (.par (.id (tys := [SimpleDataflow.BoolTy])) (.par (.const init) (.id (tys := [α.toSDF]))))
  let ctrComp : SimpleDataflow.Pipeline [ctrType] [SimpleDataflow.BoolTy] :=
    .comp (.binaryOp .eq) (.par (.id (tys := [ctrType])) (.const 0))
  let pipeline : SimpleDataflow.Pipeline [β.toSDF, α.toSDF, ctrType] [α.toSDFOpt, α.toSDF, ctrType] :=
    .split ctrUpdate (.split (φ := []) (.comp .swap (.par accum ctrComp)) output accumUpdate) .id
  let permuteInputs : SimpleDataflow.Pipeline [β.toSDF, α.toSDF, ctrType] [β.toSDF, ctrType, α.toSDF] :=
    .par (.id (tys := [β.toSDF])) .swap
  .comp pipeline permuteInputs

def Step.Prog.compile {sty : Step.Ty} : Step.Prog sty → SimpleDataflow.DataflowMachine
  | @Step.Prog.zip α β γ op =>
    let inputs : List SimpleDataflow.Ty := [α.toSDF, β.toSDF]
    let ia : Member α.toSDF inputs := .head
    let ib : Member β.toSDF inputs := .tail .head
    let outputs : List SimpleDataflow.Ty := [γ.toSDF]
    let ic : Member γ.toSDF outputs := .head
    let state : List SimpleDataflow.Ty:= []
    let pipeline : SimpleDataflow.Ops inputs outputs state := op.compile
    let node := ⟨inputs, outputs, state, []ₕ, pipeline⟩
    let nodes : SDFNodeList 1 := .cons node .nil
    let fifos := [
      .input ⟨α.toSDF, ia, 0, ia⟩,
      .input ⟨β.toSDF, ib, 0, ib⟩,
      .output ⟨γ.toSDF, 0, ic, ic⟩
    ]
    ⟨inputs, outputs, 1, nodes, fifos⟩
  | @Step.Prog.map α β op =>
    let inputs : List SimpleDataflow.Ty := [α.toSDF]
    let ia : Member α.toSDF inputs := .head
    let outputs : List SimpleDataflow.Ty := [β.toSDF]
    let ib : Member β.toSDF outputs := .head
    let state : List SimpleDataflow.Ty:= []
    let pipeline : SimpleDataflow.Ops inputs outputs state := op.compile
    let node := ⟨inputs, outputs, state, []ₕ, pipeline⟩
    let nodes : SDFNodeList 1 := .cons node .nil
    let fifos := [
      .input ⟨α.toSDF, ia, 0, ia⟩,
      .output ⟨β.toSDF, 0, ib, ib⟩
    ]
    ⟨inputs, outputs, 1, nodes, fifos⟩
  | @Step.Prog.reduce α β op len init =>
    let inputs : List SimpleDataflow.Ty := [β.toSDF]
    let ib : Member β.toSDF inputs := .head
    let outputs : List SimpleDataflow.Ty := [α.toSDFOpt]
    let ia : Member α.toSDFOpt outputs := .head
    let ctrWidth : Nat := (Nat.log2 len) + 1
    let ctrType : SimpleDataflow.Ty := .prim (.bitVec ctrWidth)
    let state : List SimpleDataflow.Ty:= [α.toSDF, ctrType]
    let pipeline := reductionBlock op len init
    let node := ⟨inputs, outputs, state, [init, ⟨0, by simp⟩]ₕ, pipeline⟩
    let nodes : SDFNodeList 1 := .cons node .nil
    let fifos := [
      .input ⟨β.toSDF, ib, 0, ib⟩,
      .output ⟨α.toSDFOpt, 0, ia, ia⟩
    ]
    ⟨inputs, outputs, 1, nodes, fifos⟩
  | .comp f g => sorry
  | .comp2 f g => sorry
