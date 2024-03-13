import Spacetalk.Step
import Spacetalk.SimpleDataflow
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.ClearExcept

def dotProd (n : Nat) (a : Stream' (BitVec 32)) (b : Stream' (BitVec 32)) : Stream' (BitVec 32) :=
  Stream'.reduce (· + ·) n 0 (Stream'.zip (· * ·) a b)

def sa : Stream' (BitVec 32) := λ n => ⟨n % (2 ^ 32), by apply Nat.mod_lt; simp⟩

theorem Nat.sub_one_succ {n : Nat} : 0 < n → n - 1 + 1 = n := by
  intro h
  rw [Nat.sub_add_cancel]
  exact h

namespace Step
  def TwoOne (w : Nat) := .stream (.bitVec w) → .stream (.bitVec w) → .stream (.bitVec w)

  def OneOne (w : Nat) := .stream (.bitVec w) → .stream (.bitVec w)

  def dotProd (w n : Nat) : Prog (TwoOne w) :=
    let multiply : Prog (TwoOne w) := .zip (.mul)
    let reduction : Prog (OneOne w) := .reduce (.add) n 0
    .comp2 reduction multiply

end Step
def func (len n : Nat) :=
  let step := (((Step.dotProd 32 len).denote sa sa) n).toNat
  let ml := (dotProd len sa sa n).toNat
  (step, ml, step == ml)
#eval func 10 6

theorem step_dp_equiv : ∀n : Nat, (Step.dotProd 32 n).denote = dotProd n := by aesop

namespace SimpleDataflow

  def accumInputs := [Ty.nat]
  def accumOutputs := [Ty.option .nat]
  def accumState := [Ty.nat, .nat]
  def accumStateCtr : Member .nat accumState := .head
  def accumStateSum : Member .nat accumState := .tail .head
  def AccumType := Ops accumInputs accumOutputs accumState

  def accum (dim : Nat) : AccumType :=
    let sumFold : Ops accumInputs accumInputs accumState := .binaryStateUpdate .add accumStateSum
    let stateInc : Ops accumInputs accumInputs accumState := .unaryStateUpdate (.binOpRightConst .add 1) accumStateCtr
    let outputGuard : Ops accumInputs accumOutputs accumState := .stateUnaryGuard (.binOpRightConst .eq dim) accumStateCtr
    let sumReset : Ops accumOutputs accumOutputs accumState := .stateReset (.binOpRightConst .eq dim) accumStateCtr accumStateSum 0
    let stateMod : Ops accumOutputs accumOutputs accumState := .unaryStateUpdate (.binOpRightConst .mod dim) accumStateCtr

    .comp stateMod (.comp sumReset (.comp outputGuard (.comp stateInc sumFold)))

  def mulInputs : List Ty := [.nat, .nat]
  def mulOutputs : List Ty := [.nat]
  def mul : Ops mulInputs mulOutputs [] := .binaryOp .mul

  def dotProdGraph (dim : Nat) : DataflowMachine :=
    let mulNode : Node Ty Ops := ⟨mulInputs, mulOutputs, [], [], mul⟩
    let accumNode : Node Ty Ops := ⟨accumInputs, accumOutputs, accumState, 0 :: 0 :: [], accum dim⟩
    let nodes : Vector (Node Ty Ops) 2:= .cons mulNode (.cons accumNode .nil)

    let mulToAccum := {
      t := .nat,
      producer := 0,
      consumer := 1,
      producerPort := .head,
      consumerPort := .head,
      adv := by simp
    }
    let inputA := {
      t := .nat,
      producer := .head,
      consumer := 0,
      consumerPort := .head,
    }
    let inputB := {
      t := .nat,
      producer := .tail .head,
      consumer := 0,
      consumerPort := .tail .head,
    }
    let output := {
      t := .option .nat,
      producer := 1,
      producerPort := .head,
      consumer := .head,
    }
    let fifos : List (FIFO mulInputs accumOutputs nodes) := [
      .input inputA,
      .input inputB,
      .advancing mulToAccum,
      .output output
    ]

    {
      inputs := mulInputs,
      outputs := accumOutputs,
      nodes := nodes,
      fifos := fifos
    }

  theorem Nat.mod_eq_zero_of_le_sub_eq_zero {m n : Nat} : m ≤ n → n - m = 0 → m % n = 0 := by
    intro h1 h2
    zify [h1] at h2
    zify at h1
    zify
    have heq := Int.eq_of_sub_eq_zero h2
    simp [heq]
    apply Int.emod_eq_zero_of_dvd
    simp

  def dotProdUnfiltered (dim : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' (Option Nat) :=
    ((dotProdGraph dim).denote (a :: b :: [])).get .head

  theorem dp_dim_some : ∀ (dim : Nat) (a : Stream' Nat) (b : Stream' Nat) (n : Nat),
    ((dotProdUnfiltered dim a b) n).isSome = true ↔ (n + 1) % dim = 0 := by
    sorry

  def dotProd (dim : Nat) (h : 0 < dim) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
    let unfiltered := dotProdUnfiltered dim a b
    λ n =>
      let val := unfiltered ((n + 1) * dim - 1)
      have hs : val.isSome = true := by
        rw [dp_dim_some]
        zify [h]
        aesop
      val.get hs

end SimpleDataflow

theorem dataflow_dp_eq : ∀ dim : Nat, (h : 0 < dim) → SimpleDataflow.dotProd dim h = dotProd dim := by
  intro dim h
  apply funext
  intro sa
  apply funext
  intro sb
  apply funext
  intro n
  sorry

def dim := 10
def sdp := SimpleDataflow.dotProd dim (by simp [dim]) sa sb
def gdp := dotProd dim sa sb
#eval (λ n => (sdp n, gdp n)) 9
