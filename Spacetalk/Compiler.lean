import Spacetalk.SimpleDataflow
import Spacetalk.Step
import Spacetalk.Graph

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
def binOpConstRightGraph (α β γ : Step.Prim) (op : SimpleDataflow.BinaryOp α.toSDF β.toSDF γ.toSDF) (c : β.denote) : SDFOneOutput γ :=
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
    .advancing ⟨β.toSDF, 0, 1, .head, .tail .head, by simp⟩,
    fifo
  ]
  let g : SimpleDataflow.DataflowMachine := ⟨inputs, outputs, 2, nodes, fifos⟩
  ⟨
    g,
    
  ⟩

def binaryOpGraph (op : SimpleDataflow.BinaryOp α β γ) : SimpleDataflow.DataflowMachine :=
  let opNode := ⟨[α, β], [γ], [], []ₕ, .binaryOp op⟩
  let nodes : SDFNodeList 1 := .cons opNode .nil
  let fifos := [
    .input ⟨α, .head, 0, .head⟩,
    .input ⟨β, .tail .head, 0, .tail .head⟩,
    .output ⟨γ, 0, .head, .head⟩
  ]
  ⟨[α, β], [γ], 1, nodes, fifos⟩

def Step.UnaryOp.compile : Step.UnaryOp α β → SDFOneOutput β
  | .addConst c => binOpConstRightGraph α α α .add c
  | .mulConst c => binOpConstRightGraph α α α .mul c

def Step.BinaryOp.compile : Step.BinaryOp α β γ → SDFOneOutput γ
  | @Step.BinaryOp.add w => ⟨binaryOpGraph (@SimpleDataflow.BinaryOp.add w), by aesop⟩
  | @Step.BinaryOp.mul w => ⟨binaryOpGraph (@SimpleDataflow.BinaryOp.mul w), by aesop⟩

def Step.Prog.compile {sty : Step.Ty} : Step.Prog sty → sty.toSDF
  | @Step.Prog.const α as => sorry
  | @Step.Prog.zip α β γ op as bs =>
    let asg := as.compile
    let bsg := bs.compile
    let opg := op.compile
    have h_op_inputs : opg.val.inputs = [α.toSDF, β.toSDF] := by
      simp [opg, Step.BinaryOp.compile, binaryOpGraph]
      aesop
    let iap : Member α.toSDF asg.val.outputs := asg.property ▸ .head
    let iac : Member α.toSDF opg.val.inputs := h_op_inputs ▸ .head
    let ibp : Member β.toSDF bsg.val.outputs := bsg.property ▸ .head
    let ibc : Member β.toSDF opg.val.inputs := h_op_inputs ▸ .tail .head

    sorry
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
