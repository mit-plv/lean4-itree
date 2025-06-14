import CTree.Refinement
import CTree.LTS

namespace CTree

/-!
# Key Lemmas for Refinement-Simulation Equivalence

This file contains the detailed proofs of the key lemmas needed to establish
the equivalence between coinductive refinement and weak simulation.
-/

lemma Step.zero_of_val (h : Step t1 (.val v) t2) : t2 = zero := by
  generalize hl : Label.val v = l at *
  induction h with
  | ret => rfl
  | vis | tau => contradiction
  | choice_left _ ih => exact ih hl
  | choice_right _ ih => exact ih hl

lemma NTauStep.ret (h : NTauStep n (ret x) t) : n = 0 := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [NTauStep] at h
    obtain ⟨_, htau, _⟩ := h
    generalize hret : CTree.ret x = tret at *
    cases htau <;> ctree_elim hret

lemma WeakStep.ret_val (h : WeakStep (ret x) (.val y) t) : x = y := by
  obtain ⟨t2, t3, n1, n2, htau1, hs, htau2⟩ := h
  rw [htau1.ret] at htau1
  simp only [NTauStep] at htau1
  subst htau1
  generalize hret : ret x = hret at *
  cases hs
  <;> ctree_elim hret
  exact ret_inj hret

lemma WeakStep.choice_left_left (h : WeakStep t1 l t3) : WeakStep (t1 ⊕ t2) l t3 := by
  obtain ⟨t1Tau, t3Tau, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau1
    subst htau1
    exists  t1 ⊕ t2, t3Tau, 0, n2
    apply And.intro
    · simp only [NTauStep]
    · refine ⟨?_, htau2⟩
      exact Step.choice_left hs
  | n + 1 =>
    simp only [NTauStep] at htau1
    obtain ⟨t2, htau, htau_n⟩ := htau1
    rename_i t2'
    exists t1Tau, t3Tau, n + 1, n2
    refine ⟨?_, hs, htau2⟩
    simp only [NTauStep]
    exists t2
    refine ⟨?_, htau_n⟩
    exact Step.choice_left htau

lemma WeakStep.choice_left_right (h : WeakStep t2 l t3) : WeakStep (t1 ⊕ t2) l t3 := by
  obtain ⟨t1Tau, t3Tau, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau1
    subst htau1
    exists  t1 ⊕ t2, t3Tau, 0, n2
    apply And.intro
    · simp only [NTauStep]
    · refine ⟨?_, htau2⟩
      exact Step.choice_right hs
  | n + 1 =>
    simp only [NTauStep] at htau1
    obtain ⟨t2, htau, htau_n⟩ := htau1
    rename_i t2'
    exists t1Tau, t3Tau, n + 1, n2
    refine ⟨?_, hs, htau2⟩
    simp only [NTauStep]
    exists t2
    refine ⟨?_, htau_n⟩
    exact Step.choice_right htau

lemma weak_step_of_ContainsRet (h : ContainsRet v t) : WeakStep t (.val v) zero := by
  induction h with
  | ret =>
    exists ret v, zero, 0, 0
    apply And.intro
    · simp only [NTauStep]
    · apply And.intro .ret
      simp only [NTauStep]
  | tau _ ih =>
    have ⟨t1, t2, n1, n2, htau1, hs, htau2⟩ := ih
    have := hs.zero_of_val
    subst this
    exists t1, zero, n1 + 1, 0
    apply And.intro
    · simp only [NTauStep]
      rename_i t2 _
      exists t2
      exact And.intro .tau htau1
    · apply And.intro hs
      simp only [NTauStep]
  | choice_left _ ih =>
    exact WeakStep.choice_left_left ih
  | choice_right _ ih =>
    exact WeakStep.choice_left_right ih

lemma weak_step_of_refine_ret (h : Refine' Eq p1 p2 (ret v) t) : WeakStep t (.val v) zero :=
  weak_step_of_ContainsRet h.dest_ret_left

lemma refine_ret_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  Step t1 (.val v) zero → Refine' Eq p1 p2 (ret v) t2 := by
  intro hstep
  generalize hl : Label.val v = l at *
  generalize hz : zero = z at *
  induction hstep
  <;> try contradiction
  case ret => rw [Label.val.inj hl]; exact href
  case choice_left _ ih =>
    apply ih href.inv_choice_left_left <;> assumption
  case choice_right _ ih =>
    apply ih href.inv_choice_left_right <;> assumption

-- Fundamental lemma: tau steps in refinement correspond to weak steps
lemma refine_tau_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  ∀ t1', Step t1 .tau t1' → Refine' Eq p1 p2 t1' t2 := by
  intro t1' hstep
  generalize hl : Label.tau = l at *
  induction hstep with
  | ret | vis => contradiction
  | tau => exact href.inv_tau_left
  | choice_left h ih => exact ih href.inv_choice_left_left hl
  | choice_right h ih => exact ih href.inv_choice_left_right hl

lemma refine_ntau_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  ∀ t1' n, NTauStep n t1 t1' → Refine' Eq p1 p2 t1' t2 := by
  intro t1' n hstep
  revert t1
  induction n with
  | zero =>
    intro t1 href hstep
    simp only [NTauStep] at hstep
    rw [←hstep]
    exact href
  | succ n ih =>
    intro t1 href hstep
    simp only [NTauStep] at hstep
    obtain ⟨t2, htau, htau_n⟩ := hstep
    apply ih _ htau_n
    exact refine_tau_correspondence href _ htau

-- Lemma for event steps
lemma refine_event_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  ∀ {α} {e : ε α} {a : α} t1', Step t1 (.event α e a) t1' →
  ∃ t2', WeakStep t2 (.event α e a) t2' ∧ Refine' Eq p1 p2 t1' t2' := by
  intro α e a t1' hstep
  generalize hl : Label.event α e a = l at *
  revert href
  induction hstep with
  | ret | tau => contradiction
  | vis =>
    intro href
    have ⟨ha, _, _⟩ := Label.event.inj hl
    subst ha
    have ⟨k2, hcont, href⟩ := href.inv_vis_left
    exists k2 a
    induction hcont with
    | vis =>
      rename_i href'
      have ⟨_, _, ha⟩ := Label.event.inj hl
      subst ha
      apply And.intro _ (href' a)
      rename_i e _ _ _ _ _
      exists vis e k2, k2 a, 0, 0
      apply And.intro _; apply And.intro
      exact Step.vis
      all_goals simp only [NTauStep]
    | tau _ ih =>
      have := Refine.dest_tau_right (by rw [Refine]; exists p1, p2)
      rw [Refine] at this
      obtain ⟨p1', p2', h⟩ := this
      rw [Refine'] at *
      have ⟨hs, h⟩ := ih (RefineF.idx_irrelevance h _ _)
      apply And.intro
      · obtain ⟨t3, t4, n1, n2, htau1, hs, htau2⟩ := hs
        exists t3, t4, n1 + 1, n2
        apply And.intro
        · simp only [NTauStep]
          rename_i t2 _ _
          exists t2
          apply And.intro _ htau1
          exact Step.tau
        · apply And.intro hs htau2
      · rw [Refine'] at h
        exact h
    | choice_left h ih =>
      have ⟨_, _, ha⟩ := Label.event.inj hl
      subst ha
      have := Refine'.of_ContainsVis h (r := Eq) (p1 := p1) (p2 := p2)
      rename_i href' _ _ _ _ _
      apply And.intro
      · have ⟨hws, _⟩ := ih (Refine'.vis_trans href' this)
        exact hws.choice_left_left
      · exact href' a
    | choice_right h ih =>
      have ⟨_, _, ha⟩ := Label.event.inj hl
      subst ha
      have := Refine'.of_ContainsVis h (r := Eq) (p1 := p1) (p2 := p2)
      rename_i href' _ _ _ _ _
      apply And.intro
      · have ⟨hws, _⟩ := ih (Refine'.vis_trans href' this)
        exact hws.choice_left_right
      · exact href' a
  | choice_left h ih =>
    intro h
    exact ih hl h.inv_choice_left_left
  | choice_right h ih =>
    intro h
    exact ih hl h.inv_choice_left_right

end CTree
