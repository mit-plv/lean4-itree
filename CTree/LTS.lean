import CTree.Basic

namespace CTree
  /-
    Labelled transition system for `CTree`s.
  -/

  inductive Label (ε : Type → Type) (ρ : Type)
  | val (v : ρ)
  | event (α : Type) (e : ε α) (a : α)
  | tau

  inductive Step : CTree ε ρ → Label ε ρ → CTree ε ρ → Prop
  | ret : Step (ret v) (.val v) zero
  | vis {α} {e : ε α} {a : α} {k : α → CTree ε ρ} : Step (vis e k) (.event α e a) (k a)
  | tau : Step t.tau .tau t
  | choice_left (h : Step t1 l t3) : Step (t1 ⊕ t2) l t3
  | choice_right (h : Step t2 l t3) : Step (t1 ⊕ t2) l t3

  def NTauStep (n : Nat) (t1 t3 : CTree ε ρ) : Prop :=
    match n with
    | 0 => t1 = t3
    | n + 1 => ∃ t2, Step t1 .tau t2 ∧ NTauStep n t2 t3

  def WeakStep (t1 : CTree ε ρ) (l : Label ε ρ) (t4 : CTree ε ρ) : Prop :=
    ∃ t2 t3 n1 n2, NTauStep n1 t1 t2 ∧ Step t2 l t3 ∧ NTauStep n2 t3 t4

  def IsWeakSimulation (sim : Rel (CTree ε ρ) (CTree ε ρ)) : Prop :=
    ∀ p1 q1, sim p1 q1 →
      ∀ l p2, Step p1 l p2 →
        match l with
        | .tau => ∃ n q2, NTauStep n q1 q2
        | _ => ∃ q2, WeakStep q1 l q2

  def IsWeakBisimulation (sim : Rel (CTree ε ρ) (CTree ε ρ)) : Prop :=
    IsWeakSimulation sim ∧ IsWeakSimulation (flip sim)

  def WeakBisim : Rel (CTree ε ρ) (CTree ε ρ) :=
    λ p q => ∃ sim, IsWeakBisimulation sim ∧ sim p q
end CTree
