import Mathlib.Tactic.Contrapose
import Std.Logic
import Mathlib.Logic.Basic

import Spacetalk.HList

structure InputEdge (α : Type u) (inputs : List α) (numNodes : Nat):=
  a : α
  producer : Member a inputs
  consumer : Fin numNodes
  consumerPort : Nat
deriving DecidableEq

structure OutputEdge (α : Type u) (numNodes : Nat):=
  a : α
  producer : Fin numNodes
  producerPort : Nat
deriving DecidableEq

structure AdvancingEdge (α : Type u) (numNodes : Nat):=
  a : α
  producer : Fin numNodes
  producerPort : Nat
  consumer : Fin numNodes
  consumerPort : Nat
  h : producer < consumer
deriving DecidableEq

structure InitializedEdge (α : Type u) (rep : α → Type) (numNodes : Nat) :=
  a : α
  producer : Fin numNodes
  producerPort : Nat
  consumer : Fin numNodes
  consumerPort : Nat
  initialValue : rep a

instance [DecidableEq α] [∀ a, DecidableEq (rep a)] : DecidableEq (InitializedEdge α rep numNodes) :=
  λ a b => by
    rw [InitializedEdge.mk.injEq]
    apply Decidable.byCases (p := (a.a = b.a ∧ a.producer = b.producer ∧ a.producerPort = b.producerPort ∧ a.consumer = b.consumer ∧ a.consumerPort = b.consumerPort))
    · intro h
      have h_eq : rep a.a = rep b.a := by rw [h.left]
      apply Decidable.byCases (p := cast h_eq a.initialValue = b.initialValue)
      · intro h_cast
        apply isTrue
        have := heq_of_cast_eq h_eq h_cast
        have := And.intro h this
        repeat rw [and_assoc] at this
        exact this
      · intro h_cast_neq
        apply isFalse
        intro h
        apply h_cast_neq
        apply cast_eq_iff_heq.mpr
        exact h.right.right.right.right.right
    · intro h_neq
      apply isFalse
      intro h
      apply h_neq
      repeat rw [←and_assoc] at h
      conv at h =>
        lhs
        repeat rw [and_assoc]
      exact h.left

inductive Edge (α : Type u) (rep : α → Type) (inputs : List α) (numNodes : Nat) : Type u
  | input : InputEdge α inputs numNodes → Edge α rep inputs numNodes
  | output : OutputEdge α numNodes → Edge α rep inputs numNodes
  | advancing : AdvancingEdge α numNodes → Edge α rep inputs numNodes
  | initialized : InitializedEdge α rep numNodes → Edge α rep inputs numNodes

instance [DecidableEq α] [∀ a, DecidableEq (rep a)] : DecidableEq (Edge α rep inputs numNodes) :=
  λ a b => by
    cases a <;> cases b <;> try exact isFalse Edge.noConfusion
    all_goals (rename_i ae be
               apply Decidable.byCases (p := ae = be)
               all_goals intro h
               · apply isTrue; simp [h]
               · apply isFalse; simp [h])
