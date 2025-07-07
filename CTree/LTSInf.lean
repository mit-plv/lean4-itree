import CTree.Basic
import CTree.Paco

namespace CTree
  /-
    Labelled transition system for `CTree`s.
  -/

  inductive StateInf ε ρ
  | ct : CTree ε ρ → StateInf ε ρ
  | kt {α} : KTree ε α ρ → StateInf ε ρ
  | div : StateInf ε ρ

  notation:150 "C∞[ " t " ]" => StateInf.ct t
  notation:150 "K∞[ " t " ]" => StateInf.kt t
  notation:151 "K∞[ " α' " | " t " ]" => StateInf.kt (α := α') t

  inductive DivergeF (sim : CTree ε ρ → Prop) : CTree ε ρ → Prop
    | tau {t : CTree ε ρ} : sim t → DivergeF sim t.tau
    | choice_left {c1 c2 : CTree ε ρ} : sim c1 → DivergeF sim (c1 ⊕ c2)
    | choice_right {c1 c2 : CTree ε ρ} : sim c2 → DivergeF sim (c1 ⊕ c2)

  theorem DivergeF.monotone {t : CTree ε ρ}
    (sim1 sim2 : CTree ε ρ → Prop) (hsim : ∀ t, sim1 t → sim2 t) (h : DivergeF sim1 t) : DivergeF sim2 t := by
    cases h with
    | tau h => exact .tau (hsim _ h)
    | choice_left h => exact .choice_left (hsim _ h)
    | choice_right h => exact .choice_right (hsim _ h)

  /--
    Whether a `CTree` can silenty diverge
  -/
  def Diverge (t : CTree ε ρ) : Prop :=
    DivergeF Diverge t
    coinductive_fixpoint monotonicity by
      intro _ _ hsim _ h
      exact DivergeF.monotone _ _ hsim h

  inductive Label (ε : Type u → Type v) (ρ : Type w)
  | val (v : ρ)
  | event (α : Type u) (e : ε α)
  | response (α : Type u) (a : α)
  | div

  inductive Step : StateInf ε ρ → Label ε ρ → StateInf ε ρ → Prop
  | ret {v : ρ} : Step (C∞[ @ret ε ρ v ]) (.val v) (C∞[ zero ])
  | event {α} {e : ε α} {k : α → CTree ε ρ}
    : Step (C∞[ vis e k ]) (.event α e) (K∞[ k ])
  | response {α} {a : α} {k : α → CTree ε ρ}
    : Step (K∞[ k ]) (.response α a) (C∞[ k a ])
  | tau {t : CTree ε ρ} {l : Label ε ρ} {t3 : StateInf ε ρ}
    : Step (C∞[ t ]) l t3 → Step (C∞[ t.tau ]) l t3
  | choice_left {l : Label ε ρ} {t1 t2 : CTree ε ρ} {t3 : StateInf ε ρ}
    : Step (C∞[ t1 ]) l t3 → Step (C∞[ t1 ⊕ t2 ]) l t3
  | choice_right {l : Label ε ρ} {t1 t2 : CTree ε ρ} {t3 : StateInf ε ρ}
    : Step (C∞[ t2 ]) l t3 → Step (C∞[ t1 ⊕ t2 ]) l t3
  | div {t : CTree ε ρ} : Diverge t → Step (C∞[ t ]) .div .div

  def IsSimulation (sim : Rel (StateInf ε ρ) (StateInf ε ρ)) : Prop :=
    ∀ p1 q1, sim p1 q1 →
      match p1, q1 with
      | C∞[ _ ], C∞[ _ ] =>
        ∀ l p2, Step p1 l p2 → ∃ q2, Step q1 l q2 ∧ sim p2 q2
      | K∞[ α1 | k1 ], K∞[ α2 | k2 ] =>
        ∃ (hα : α1 = α2), ∀ (a : α1), sim (C∞[ k1 a ]) (C∞[ k2 (hα ▸ a) ])
      | .div, .div => True
      | _, _ => False

  def IsBisimulation (sim : Rel (StateInf ε ρ) (StateInf ε ρ)) : Prop :=
    IsSimulation sim ∧ IsSimulation (flip sim)

  def Sim : Rel (StateInf ε ρ) (StateInf ε ρ) :=
    λ p q => ∃ sim, IsSimulation sim ∧ sim p q

  def Bisim : Rel (StateInf ε ρ) (StateInf ε ρ) :=
    λ p q => ∃ sim, IsBisimulation sim ∧ sim p q

  theorem infTau_diverge : Diverge (@infTau ε ρ) := by
    pcofix cih
    pfold
    rw [infTau_eq]
    constructor
    pleft
    assumption

  theorem infND_diverge : Diverge (@infND ε ρ) := by
    pcofix cih
    pfold
    rw [infND_eq]
    constructor
    pleft
    assumption

end CTree
