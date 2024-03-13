import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

def Step.Prim.toSDF : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .prim (.bitVec w)

def Step.UnaryOp.compile : Step.UnaryOp α β → SimpleDataflow.Pipeline [α.toSDF] [β.toSDF]
  | .addConst c => .unaryOp (.binOpRightConst .add c)
  | .mulConst c => .unaryOp (.binOpRightConst .mul c)

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Pipeline [α.toSDF, β.toSDF] [γ.toSDF]
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

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
    let outputs : List SimpleDataflow.Ty := [α.toSDF]
    let ia : Member α.toSDF outputs := .head
    let ctrWidth : Nat := (Nat.log2 len) + 1
    let ctrType : SimpleDataflow.Ty := .prim (.bitVec ctrWidth)
    let state : List SimpleDataflow.Ty:= [α.toSDF, ctrType]
    let pipeline : SimpleDataflow.Ops inputs outputs state := sorry
    let node := ⟨inputs, outputs, state, [init, ⟨0, by simp⟩]ₕ, pipeline⟩
    let nodes : SDFNodeList 1 := .cons node .nil
    let fifos := [
      .input ⟨β.toSDF, ib, 0, ib⟩,
      .output ⟨α.toSDF, 0, ia, ia⟩
    ]
    ⟨inputs, outputs, 1, nodes, fifos⟩
  | .comp f g => sorry
  | .comp2 f g => sorry
