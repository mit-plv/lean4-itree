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

  def vis1 (e : ε α) : CTree ε ρ :=
    vis e (λ _ => zero)

  def vis2 (e1 e2 : ε α) : CTree ε ρ :=
    vis e1 (λ _ => vis1 e2)

  theorem choice_partial_vis_angelic : WeakBisim ((@vis1 ε ρ α e1) ⊕ (vis2 e1 e2)) (vis2 e1 e2) := by
    simp only [WeakBisim]
    exists λ p q => p = (vis1 e1 ⊕ vis2 e1 e2) ∧ q = vis2 e1 e2
    apply And.intro
    · simp only [IsWeakBisimulation]
      apply And.intro
      · simp only [IsWeakSimulation]
        intro p1 q1 ⟨heq1, heq2⟩ l p2' step
        subst heq1 heq2
        generalize hp : (vis1 e1 ⊕ vis2 e1 e2) = p at *
        cases step
        <;> ctree_elim hp
        case choice_left h =>
          have ⟨hl, hr⟩ := choice_inj hp
          subst hl hr
          generalize hv1 : vis1 e1 = v1 at *
          cases h
          <;> ctree_elim hv1
          simp only
          have hα := vis_inj_α hv1
          subst hα
          have ⟨he, hk⟩ := vis_inj hv1
          subst he hk
          exists vis1 e2
          exists vis2 e1 e2, vis1 e2, 0, 0
          apply And.intro
          · simp only [NTauStep]
          · apply And.intro
            · simp only [vis2]
              exact Step.vis (α := α) (e := e1) (k := fun _ => vis1 e2)
            · simp only [NTauStep]
        case choice_right h =>
          have ⟨hl, hr⟩ := choice_inj hp
          subst hl hr
          generalize hv2 : vis2 e1 e2 = v2 at *
          cases h
          <;> ctree_elim hv2
          simp only
          have hα := vis_inj_α hv2
          subst hα
          have ⟨he, hk⟩ := vis_inj hv2
          subst he hk
          exists vis1 e2
          exists vis2 e1 e2, vis1 e2, 0, 0
          apply And.intro
          · simp only [NTauStep, vis2]
          · apply And.intro
            · simp only [vis2]
              exact Step.vis (α := α) (e := e1) (k := fun _ => vis1 e2)
            · simp only [NTauStep]
      · simp only [IsWeakSimulation]
        intro p1 q1 ⟨heq1, heq2⟩ l p2' step
        subst heq1 heq2
        generalize hp : vis2 e1 e2 = p at *
        cases step
        <;> ctree_elim hp
        simp only
        have hα := vis_inj_α hp
        subst hα
        have ⟨he, hk⟩ := vis_inj hp
        subst he hk
        exists vis1 e2
        exists (vis1 e1 ⊕ vis e1 fun x => vis1 e2), vis1 e2, 0, 0
        apply And.intro
        · simp only [NTauStep]
        · apply And.intro
          · apply Step.choice_right
            exact Step.vis
          · simp only [NTauStep]
    · simp_all only [and_self]
end CTree
