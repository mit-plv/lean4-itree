import Spacetalk.Step
import Spacetalk.SimpleDataflow
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.ClearExcept

def dotProd (n : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
  Stream'.reduce (· + ·) n 0 (Stream'.zip (· * ·) a b)

def sa : Stream' Nat := id
def sb : Stream' Nat := id

theorem Nat.sub_one_succ {n : Nat} : 0 < n → n - 1 + 1 = n := by
  intro h
  rw [Nat.sub_add_cancel]
  exact h

namespace Step
  -- A dot product of length n vectors
  def dotProd (n : Nat) : Prog rep (.stream .nat → .stream .nat → .stream .nat) :=
    let multiply := .zip (.binop .mul)
    let reduction := .reduce (.binop .add) n 0
    .lam λ a => .lam λ b => .app reduction (.app (.app multiply (.var a)) (.var b))
end Step

theorem step_dp_equiv : ∀n : Nat, (Step.dotProd n).denote = dotProd n := by aesop

namespace SimpleDataflow

  def accum (dim : Nat) : Ops [.nat] [.option .nat] [.nat, .nat] :=
    let state := [.nat, .nat] -- [counter, sum]
    let counter : Member .nat state := .head
    let sum : Member .nat state := .tail .head

    let sumUpdate : Ops [.nat] [] state := .binaryStateUpdate .add sum
    let sumOut : Ops [] [.nat] state := .unaryStateOp .id sum
    let outputGuard : Ops [.nat] [.option .nat] state := .stateUnaryGuard (.eqConst (dim - 1)) counter
    let stateReset : Ops [.option .nat] [.option .nat] state := .stateReset (.eqConst (dim - 1)) counter sum 0
    let incState : Ops [.option .nat] [.option .nat] state := .unaryStateUpdate (.incMod dim) counter

    .comp incState (.comp stateReset (.comp outputGuard (.comp sumOut sumUpdate)))

  theorem accum_dim_some : ∀ {x sum counter : Nat} (dim : Nat),
    (((accum dim).eval (x :: []) (counter :: sum :: [])).fst.get .head).isSome = true ↔ counter = dim - 1 := by
    intro x sum counter dim
    apply Iff.intro
    · intro h
      symm
      simp [Option.isSome] at h
      split at h <;>
      (
        rename_i heq
        simp [accum, Ops.eval, UnaryOp.eval, BinaryOp.eval] at heq
        split at heq <;> first | assumption | split at heq <;> contradiction
      )
    · intro h
      simp [accum, Ops.eval, UnaryOp.eval, BinaryOp.eval]
      rw [←h]
      simp

  def mul : Ops [.nat, .nat] [.nat] [] := .binaryOp .mul

  def dotProdGraph (dim : Nat) : DataflowMachine :=
    let inputs := [.nat, .nat]
    let outputs := [.option .nat]
    let mulNode : Node Ty Ops := ⟨inputs, [.nat], [], [], mul⟩
    let accumNode : Node Ty Ops := ⟨[.nat], outputs, [.nat, .nat], 0 :: 0 :: [], accum dim⟩
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
    let fifos : List (FIFO inputs outputs nodes) := [
      .input inputA,
      .input inputB,
      .advancing mulToAccum,
      .output output
    ]

    {
      inputs := inputs,
      outputs := outputs,
      nodes := nodes,
      fifos := fifos
    }

  theorem Nat.mod_eq_zero_of_le_sub_eq_zero {m n : Nat} : m ≤ n → n - m = 0 → m % n = 0 := by
    intro h1 h2
    have : n = m := by
      rw [←Nat.sub_add_cancel h1]
      rw [h2]
      simp
    rw [this]
    simp

  -- set_option maxHeartbeats 100000000
  theorem dp_nth_counter_eq_n : ∀ {dim : Nat} (inputs : DenoListsStream (dotProdGraph dim).inputs) (n : Nat),
    0 < dim → ((((dotProdGraph dim).nthCycleState inputs n) ⟨1, by simp [dotProdGraph]⟩).snd.get .head) = n := by
    intro dim inputs n h
    induction n with
    | zero =>
      rw [DataflowGraph.nthCycleState]
      split
      · simp [List.toHList]
        split
        · split
          · simp [NodeOps.eval, Ops.eval]
            split
            · rename_i heq
              simp [heq]
              simp [UnaryOp.eval]
              simp [UnaryOp.eval] at heq
              clear *- h heq
              exact Nat.mod_eq_zero_of_le_sub_eq_zero h heq
            · sorry
          · sorry
          · sorry
        · sorry
      · sorry
    | succ n ih => sorry

  def dotProdUnfiltered (dim : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' (Option Nat) :=
    ((dotProdGraph dim).denote (a :: b :: [])).get .head

  theorem dp_dim_some : ∀ (dim : Nat) (a : Stream' Nat) (b : Stream' Nat) (n : Nat),
    ((dotProdUnfiltered dim a b) n).isSome = true ↔ (n + 1) % dim = 0 := by
    intro dim a b n
    apply Iff.intro
    · sorry
    · intro h
      simp [dotProdUnfiltered]
      split
      · split
        simp [Option.isSome]
        split
        · rfl
        · rename_i heq
          simp [DataflowGraph.nthCycleState, dotProdGraph, Ops.eval, UnaryOp.eval, BinaryOp.eval] at heq

          sorry
      · sorry

  def dotProd (dim : Nat) (h : 0 < dim) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
    let unfiltered := dotProdUnfiltered dim a b
    λ n =>
      let val := unfiltered ((n + 1) * dim - 1)
      have h : val.isSome = true := by
        rw [dp_dim_some]
        have : 0 < (n + 1) * dim := by simp [h]
        calc
          ((n + 1) * dim - 1 + 1) % dim = ((n + 1) * dim) % dim := by rw [Nat.sub_one_succ this]
          _ = 0 := by rw [Nat.mul_mod_left]
      val.get h

  def dp := dotProd 10 (by decide) sa sb
  #eval dp 4

end SimpleDataflow
