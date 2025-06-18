import CTree.Basic

namespace CTree
  /-
    Labelled transition system for `CTree`s.
  -/

  inductive Label (ε : Type → Type) (ρ : Type)
  | val (v : ρ)
  | event (α : Type) (e : ε α)
  | response (α : Type) (a : α)
  | tau

  inductive Step {ε ρ} : State ε ρ → Label ε ρ → State ε ρ → Prop
  | ret {v : ρ} : Step (C[ @ret ε ρ v ]) (.val v) (C[ zero ])
  | event {α} {e : ε α} {k : α → CTree ε ρ}
      : Step (C[ vis e k ]) (.event α e) (K[ k ])
  | response {α} {a : α} {k : α → CTree ε ρ}
      : Step (K[ k ]) (.response α a) (C[ k a ])
  | tau {t : CTree ε ρ} : Step (C[ t.tau ]) .tau (C[ t ])
  | choice_left {l : Label ε ρ} {t1 t2 : CTree ε ρ} {t3 : State ε ρ}
      (h : Step (C[ t1 ]) l t3) : Step (C[ t1 ⊕ t2 ]) l t3
  | choice_right {l : Label ε ρ} {t1 t2 : CTree ε ρ} {t3 : State ε ρ}
      (h : Step (C[ t2 ]) l t3) : Step (C[ t1 ⊕ t2 ]) l t3

  def NTauStep (n : Nat) (t1 t3 : State ε ρ) : Prop :=
    match n with
    | 0 => t1 = t3
    | n + 1 => ∃ t2, Step t1 .tau t2 ∧ NTauStep n t2 t3

  def WeakStep (t1 : State ε ρ) (l : Label ε ρ) (t4 : State ε ρ) : Prop :=
    ∃ t2 t3 n1 n2, NTauStep n1 t1 t2 ∧ Step t2 l t3 ∧ NTauStep n2 t3 t4

  def IsWeakSimulation (sim : Rel (State ε ρ) (State ε ρ)) : Prop :=
    ∀ p1 q1, sim p1 q1 →
      match p1, q1 with
      | C[ _ ], C[ _ ] =>
        ∀ l p2, Step p1 l p2 →
          match l with
          | .tau => ∃ n q2, NTauStep n q1 q2 ∧ sim p2 q2
          | _ => ∃ q2, WeakStep q1 l q2 ∧ sim p2 q2
      | K[ α1 | k1 ], K[ α2 | k2 ] =>
        ∃ (hα : α1 = α2), ∀ (a : α1), sim (C[ k1 a ]) (C[ k2 (hα ▸ a) ])
      | _, _ => False

  def IsWeakBisimulation (sim : Rel (State ε ρ) (State ε ρ)) : Prop :=
    IsWeakSimulation sim ∧ IsWeakSimulation (flip sim)

  def WeakSim : Rel (State ε ρ) (State ε ρ) :=
    λ p q => ∃ sim, IsWeakSimulation sim ∧ sim p q

  def WeakBisim : Rel (State ε ρ) (State ε ρ) :=
    λ p q => ∃ sim, IsWeakBisimulation sim ∧ sim p q
end CTree
