import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

def SDFNodeList := NodeList SimpleDataflow.Ty SimpleDataflow.Ops

def Step.Prim.toSDF : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .prim (.bitVec w)

def Step.Prim.toSDFOpt : Step.Prim → SimpleDataflow.Ty
  | .bitVec w => .option (.bitVec w)

def c : SimpleDataflow.Pipeline [] [SimpleDataflow.BoolTy] :=
  .const 1

def g : SimpleDataflow.DataflowMachine :=
  let inputs : List SimpleDataflow.Ty := []
  let outputs : List SimpleDataflow.Ty := [SimpleDataflow.BoolTy]
  let state : List SimpleDataflow.Ty := []
  let pipeline : SimpleDataflow.Ops inputs outputs state := c
  let node := ⟨inputs, outputs, state, []ₕ, pipeline⟩
  let nodes : SDFNodeList 1 := .cons node .nil
  let fifos := [
    .output ⟨SimpleDataflow.BoolTy, 0, .head, .head⟩
  ]
  ⟨inputs, outputs, 1, nodes, fifos⟩

def binOpConstRight (op : SimpleDataflow.BinaryOp α β γ) (c : β.denote) : SimpleDataflow.DataflowMachine :=
  let constNode := ⟨[], [β], [], []ₕ, .const c⟩
  let opNode := ⟨[α, β], [γ], [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 2 := .cons constNode (.cons opNode .nil)
  let fifos := [
    .input ⟨α, .head, 1, .head⟩,
    .advancing ⟨β, 0, 1, .head, .tail .head, by simp⟩,
    .output ⟨γ, 1, .head, .head⟩
  ]
  ⟨[α], [γ], 2, nodes, fifos⟩

namespace _hidden
  def w := 10
  def add1 := binOpConstRight (.add (w := w)) 1
  def mul1 := binOpConstRight (.mul (w := w)) 1
  def s : Stream' (BitVec w) := λ n => ⟨n % (2 ^ w), by apply Nat.mod_lt; simp⟩
  #eval ((add1.denote [s]ₕ).head 8).toNat
end _hidden

def Step.UnaryOp.compile : Step.UnaryOp α β → SimpleDataflow.DataflowMachine
  | .addConst c => binOpConstRight .add c
  | .mulConst c => binOpConstRight .mul c

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SimpleDataflow.Pipeline [α.toSDF, β.toSDF] [γ.toSDF]
  | .add => .binaryOp .add
  | .mul => .binaryOp .mul

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
  | Step.Prog.map op => op.compile
  | @Step.Prog.reduce α β op len init => sorry
  | @Step.Prog.comp α β γ f g =>
    let fGraph := f.compile
    let gGraph := g.compile
    let ia : Member α.toSDF gGraph.inputs := .head
    sorry
  | .comp2 f g => sorry
