import CTree.Refinement
import CTree.LTS

namespace CTree

/-!
# Key Lemmas for Refinement-Simulation Equivalence

This file contains the detailed proofs of the key lemmas needed to establish
the equivalence between coinductive refinement and weak simulation.
-/

lemma Step.elim_zero (h : Step (C[ zero ]) l t) : False := by
  generalize hz : zero = t1 at *
  cases h <;> ctree_elim hz

lemma WeakStep.elim_zero (h : WeakStep (C[ zero ]) l t) : False := by
  obtain ⟨_, _, n1, _, htau, hs, _⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau
    subst htau
    exact hs.elim_zero
  | n + 1 =>
    obtain ⟨_, hs, _⟩ := htau
    exact hs.elim_zero

lemma Step.elim_vis_val (h : Step (C[ vis e k ]) (.val v) t) : False := by
  generalize hz : CTree.vis e k = t1 at *
  cases h <;> ctree_elim hz

lemma Step.elim_vis_tau (h : Step (C[ vis e k ]) .tau t) : False := by
  generalize hz : CTree.vis e k = t1 at *
  cases h <;> ctree_elim hz

lemma WeakStep.elim_vis_val (h : WeakStep (C[ vis e k ]) (.val v) t) : False := by
  obtain ⟨_, _, n1, _, htau, hs, _⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau
    subst htau
    exact hs.elim_vis_val
  | n + 1 =>
    obtain ⟨_, hs, _⟩ := htau
    exact hs.elim_vis_tau

lemma Step.zero_of_val (h : Step t1 (.val v) t2) : t2 = C[ zero ] := by
  generalize hl : Label.val v = l at *
  induction h with
  | ret => rfl
  | event | response | tau => contradiction
  | choice_left _ ih => exact ih hl
  | choice_right _ ih => exact ih hl

lemma NTauStep.ret (h : NTauStep n (C[ ret x ]) t) : n = 0 := by
  match n with
  | 0 => rfl
  | n + 1 =>
    simp only [NTauStep] at h
    obtain ⟨_, htau, _⟩ := h
    generalize hret : CTree.ret x = tret at *
    cases htau <;> ctree_elim hret

lemma WeakStep.ret_val (h : WeakStep (C[ ret x ]) (.val y) t) : x = y := by
  obtain ⟨t2, t3, n1, n2, htau1, hs, htau2⟩ := h
  rw [htau1.ret] at htau1
  simp only [NTauStep] at htau1
  subst htau1
  generalize hret : ret x = hret at *
  cases hs
  <;> ctree_elim hret
  exact ret_inj hret

lemma Step.vis_tau (h : Step (C[ vis e k ]) .tau t) : False := by
  generalize hv : CTree.vis e k = tv at *
  cases h <;> ctree_elim hv

lemma Step.vis_event_e {ε : Type → Type} {e1 e2 : ε α} {t : State ε β} {k : KTree ε α β}
  (h : Step (C[ vis e1 k ]) (.event α e2) t) : e1 = e2 := by
  generalize hv : CTree.vis e1 k = tv at *
  cases h <;> ctree_elim hv
  have ⟨he, _⟩ := vis_inj hv
  subst he
  rfl

lemma WeakStep.vis_event_e {ε : Type → Type} {e1 e2 : ε α} {t : State ε β} {k : KTree ε α β}
  (h : WeakStep (C[ vis e1 k ]) (.event α e2) t) : e1 = e2 := by
  obtain ⟨t1Tau, t3Tau, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau1
    subst htau1
    exact hs.vis_event_e
  | n + 1 =>
    simp only [NTauStep] at htau1
    obtain ⟨_, hs, _⟩ := htau1
    exfalso; exact hs.vis_tau

lemma Step.vis_event {a : α} (h : Step (K[ k ]) (.response α e a) t) : t = C[ k a ] := by
  cases h
  rfl

lemma WeakStep.choice_left_left (h : WeakStep (C[ t1 ]) l t3) : WeakStep (C[ t1 ⊕ t2 ]) l t3 := by
  obtain ⟨t1Tau, t3Tau, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau1
    subst htau1
    exists C[ t1 ⊕ t2 ], t3Tau, 0, n2
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

lemma WeakStep.choice_left_right (h : WeakStep (C[ t2 ]) l t3) : WeakStep (C[ t1 ⊕ t2 ]) l t3 := by
  obtain ⟨t1Tau, t3Tau, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau1
    subst htau1
    exists C[ t1 ⊕ t2 ], t3Tau, 0, n2
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

lemma weak_step_of_ContainsRet (h : ContainsRet v t) : WeakStep (C[ t ]) (.val v) (C[ zero ]) := by
  induction h with
  | ret =>
    exists C[ ret v ], C[ zero ], 0, 0
    apply And.intro
    · simp only [NTauStep]
    · apply And.intro .ret
      simp only [NTauStep]
  | tau _ ih =>
    have ⟨t1, t2, n1, n2, htau1, hs, htau2⟩ := ih
    have := hs.zero_of_val
    subst this
    exists t1, C[ zero ], n1 + 1, 0
    apply And.intro
    · simp only [NTauStep]
      rename_i t2 _
      exists C[ t2 ]
      exact And.intro .tau htau1
    · apply And.intro hs
      simp only [NTauStep]
  | choice_left _ ih =>
    exact WeakStep.choice_left_left ih
  | choice_right _ ih =>
    exact WeakStep.choice_left_right ih

lemma weak_step_of_refine_ret (h : Refine' Eq p1 p2 (ret v) t) : WeakStep (C[ t ]) (.val v) (C[ zero ]) :=
  weak_step_of_ContainsRet h.dest_ret_left

lemma refine_ret_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2)
  : Step (C[ t1 ]) (.val v) (C[ zero ]) → Refine' Eq p1 p2 (ret v) t2 := by
  intro hstep
  apply Step.rec
    (motive := fun t1' l' _ step =>
      l' = .val v →
      match t1' with
      | C[ t1' ] => Refine' Eq p1 p2 t1' t2 → Refine' Eq p1 p2 (ret v) t2
      | K[ _ ] => False
    ) (t := hstep)
  <;> try (intros; intros; whnf; contradiction)
  case ret =>
    intro v hl href
    rw [←Label.val.inj hl]
    exact href
  case choice_left =>
    intro l t1 t2 t3 hstep ih hl h
    have ih := ih hl
    whnf at ih
    exact ih h.inv_choice_left_left
  case choice_right =>
    intro l t1 t2 t3 hstep ih hl h
    have ih := ih hl
    whnf at ih
    exact ih h.inv_choice_left_right
  · rfl
  · exact href

theorem Step.tau_ct_right
  (h : Step t1 .tau t2) : ∃ t2', t2 = C[ t2' ] := by
  generalize hl : Label.tau = l at *
  induction h <;> try contradiction
  case tau =>
    rename_i t2
    exists t2
  case choice_left h ih => exact ih hl
  case choice_right h ih => exact ih hl

-- Fundamental lemma: tau steps in refinement correspond to weak steps
lemma refine_tau_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  ∀ t1', Step (C[ t1 ]) .tau (C[ t1' ]) → Refine' Eq p1 p2 t1' t2 := by
  intro t1' hstep
  apply Step.rec
    (motive := fun mt1 l mt1' step =>
      l = .tau →
      match mt1, mt1' with
      | C[ mt1 ], C[ mt1' ] => Refine' Eq p1 p2 mt1 t2 → Refine' Eq p1 p2 mt1' t2
      | _, _ => False
    ) (t := hstep)
  <;> try (intros; intros; whnf; contradiction)
  case tau =>
    intro _ _; whnf
    intro href; exact href.inv_tau_left
  case choice_left =>
    intro l t1 t2 t3 hstep h hl
    subst hl
    have h := h rfl
    obtain ⟨t1', ht1'⟩ := hstep.tau_ct_right
    subst ht1'
    whnf at *
    intro ih
    exact h ih.inv_choice_left_left
  case choice_right =>
    intro l t1 t2 t3 hstep h hl
    subst hl
    have h := h rfl
    obtain ⟨t1', ht1'⟩ := hstep.tau_ct_right
    subst ht1'
    whnf at *
    intro ih
    exact h ih.inv_choice_left_right
  · rfl
  · exact href

lemma refine_ntau_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  ∀ t1' n, NTauStep n (C[ t1 ]) (C[ t1' ]) → Refine' Eq p1 p2 t1' t2 := by
  intro t1' n hstep
  revert t1
  induction n with
  | zero =>
    intro t1 href hstep
    simp only [NTauStep] at hstep
    rw [←State.ct.inj hstep]
    exact href
  | succ n ih =>
    intro t1 href hstep
    simp only [NTauStep] at hstep
    obtain ⟨t2, htau, htau_n⟩ := hstep
    obtain ⟨t2, ht2⟩ := htau.tau_ct_right
    subst ht2
    apply ih _ htau_n
    exact refine_tau_correspondence href _ htau

-- Lemma for event steps
lemma refine_event_correspondence {t1 t2 : CTree ε ρ} {p1 p2 : ENat}
  (href : Refine' Eq p1 p2 t1 t2) :
  ∀ {α} {e : ε α} {a : α} t1', Step (C[ t1 ]) (.event α e) (C[ t1' ]) →
  ∃ t2', WeakStep (C[ t2 ]) (.event α e) (C[ t2' ]) ∧ Refine' Eq p1 p2 t1' t2' := by
  sorry
  -- intro α e a t1' hstep
  -- generalize hl : Label.event α e a = l at *
  -- revert href
  -- induction hstep with
  -- | ret | tau => contradiction
  -- | vis =>
  --   intro href
  --   have ⟨ha, _, _⟩ := Label.event.inj hl
  --   subst ha
  --   have ⟨k2, hcont, href⟩ := href.inv_vis_left
  --   exists k2 a
  --   induction hcont with
  --   | vis =>
  --     rename_i href'
  --     have ⟨_, _, ha⟩ := Label.event.inj hl
  --     subst ha
  --     apply And.intro _ (href' a)
  --     rename_i e _ _ _ _ _
  --     exists vis e k2, k2 a, 0, 0
  --     apply And.intro _; apply And.intro
  --     exact Step.vis
  --     all_goals simp only [NTauStep]
  --   | tau _ ih =>
  --     have := Refine.dest_tau_right (by rw [Refine]; exists p1, p2)
  --     rw [Refine] at this
  --     obtain ⟨p1', p2', h⟩ := this
  --     rw [Refine'] at *
  --     have ⟨hs, h⟩ := ih (RefineF.idx_irrelevance h _ _)
  --     apply And.intro
  --     · obtain ⟨t3, t4, n1, n2, htau1, hs, htau2⟩ := hs
  --       exists t3, t4, n1 + 1, n2
  --       apply And.intro
  --       · simp only [NTauStep]
  --         rename_i t2 _ _
  --         exists t2
  --         apply And.intro _ htau1
  --         exact Step.tau
  --       · apply And.intro hs htau2
  --     · rw [Refine'] at h
  --       exact h
  --   | choice_left h ih =>
  --     have ⟨_, _, ha⟩ := Label.event.inj hl
  --     subst ha
  --     have := Refine'.of_ContainsVis h (r := Eq) (p1 := p1) (p2 := p2)
  --     rename_i href' _ _ _ _ _
  --     apply And.intro
  --     · have ⟨hws, _⟩ := ih (Refine'.vis_trans href' this)
  --       exact hws.choice_left_left
  --     · exact href' a
  --   | choice_right h ih =>
  --     have ⟨_, _, ha⟩ := Label.event.inj hl
  --     subst ha
  --     have := Refine'.of_ContainsVis h (r := Eq) (p1 := p1) (p2 := p2)
  --     rename_i href' _ _ _ _ _
  --     apply And.intro
  --     · have ⟨hws, _⟩ := ih (Refine'.vis_trans href' this)
  --       exact hws.choice_left_right
  --     · exact href' a
  -- | choice_left h ih =>
  --   intro h
  --   exact ih hl h.inv_choice_left_left
  -- | choice_right h ih =>
  --   intro h
  --   exact ih hl h.inv_choice_left_right

  lemma RefineF.ret_of_weak_step {x : ρ} (h : WeakStep (C[ t ]) (Label.val x) t') : RefineF Eq sim p1 p2 (CTree.ret x) t := by
    obtain ⟨t1, t2, n1, n2, htau1, hs, htau2⟩ := h
    revert t
    induction n1 with
    | zero =>
      intro t htau
      simp only [NTauStep] at htau
      subst htau
      apply Step.rec
        (motive := fun t l _ step =>
          l = .val x →
          match t with
          | C[ t ] => RefineF Eq sim p1 p2 (.ret x) t
          | _ => False
        ) (t := hs)
      <;> try (intros; intros; whnf; contradiction)
      case ret =>
        intro x hl
        whnf
        rw [Label.val.inj hl]
        exact RefineF.ret rfl
      case choice_left =>
        intro l t1 t2 t3 hstep h hl
        have h := h hl
        whnf at *
        apply RefineF.choice_left
        apply @RefineF.idx_mono _ _ _ _ _ _ _ p1 p1 p2 ⊤
        · exact le_refl _
        · exact le_top
        · exact h
      case choice_right ih =>
        intro l t1 t2 t3 hstep h hl
        have h := h hl
        whnf at *
        apply RefineF.choice_right
        apply @RefineF.idx_mono _ _ _ _ _ _ _ p1 p1 p2 ⊤
        · exact le_refl _
        · exact le_top
        · exact h
      rfl
    | succ n ih =>
      intro t htau
      simp only [NTauStep] at htau
      obtain ⟨t', htau, htau_n⟩ := htau
      obtain ⟨t2', ht2'⟩ := Step.tau_ct_right htau
      subst ht2'
      apply Step.rec
        (motive := fun t1 l t2 step =>
          l = .tau →
          match t1, t2 with
          | C[ t1 ], C[ t2 ] => RefineF Eq sim p1 p2 (.ret x) t2 → RefineF Eq sim p1 p2 (.ret x) t1
          | _, _ => False
        ) (t := htau)
      <;> try (intros; intros; whnf; contradiction)
      case tau =>
        intro t _ h
        apply RefineF.tau_right
        exact RefineF.idx_mono (le_refl _) le_top h
      case choice_left ih =>
        intro l t1 t2 t3 hs h hl
        subst hl
        have h := h rfl
        obtain ⟨t3, ht3⟩ := hs.tau_ct_right
        subst ht3
        whnf at *
        intro href
        have ih := h href
        apply RefineF.choice_left
        apply RefineF.idx_mono (p1' := p1) (p1 := p1) (p2' := p2) (p2 := ⊤)
        · exact le_refl _
        · exact le_top
        · exact ih
      case choice_right ih =>
        intro l t1 t2 t3 hs h hl
        subst hl
        have h := h rfl
        obtain ⟨t3, ht3⟩ := hs.tau_ct_right
        subst ht3
        whnf at *
        intro href
        have ih := h href
        apply RefineF.choice_right
        apply RefineF.idx_mono (p1' := p1) (p1 := p1) (p2' := p2) (p2 := ⊤)
        · exact le_refl _
        · exact le_top
        · exact ih
      · rfl
      · exact ih htau_n

  inductive Contains : CTree ε ρ → CTree ε ρ → Prop
    | refl : Contains t t
    | tau : Contains t1 t2 → Contains (tau t1) t2
    | choice_left : Contains t1 t3 → Contains (t1 ⊕ t2) t3
    | choice_right : Contains t2 t3 → Contains (t1 ⊕ t2) t3

  theorem Contains.from_NTauStep
    (h : NTauStep n (C[ t1 ]) (C[ t2 ])) : Contains t1 t2 := by
    revert t1
    induction n with
    | zero =>
      intros t1 h
      simp only [NTauStep] at h
      have h := State.ct.inj h
      subst h
      exact .refl
    | succ n ih =>
      intro t1 h
      simp only [NTauStep] at h
      obtain ⟨t1', htau, htaun⟩ := h
      obtain ⟨t1', ht1'⟩ := htau.tau_ct_right
      subst ht1'
      apply Step.rec
        (motive := fun t1 l t1' step =>
          l = .tau →
          match t1, t1' with
          | C[ t1 ], C[ t1' ] => t1'.Contains t2 → t1.Contains t2
          | _, _ => False
        ) (t := htau)
      <;> try (intros; intros; whnf; contradiction)
      case tau =>
        intro t _
        whnf
        intro ih
        exact .tau ih
      case choice_left =>
        intro l t1 t2 t3 hs h hl
        subst hl
        have h := h rfl
        obtain ⟨t3, ht3⟩ := hs.tau_ct_right
        subst ht3
        whnf at *
        intro ih
        exact .choice_left (h ih)
      case choice_right =>
        intro l t1 t2 t3 hs h hl
        subst hl
        have h := h rfl
        obtain ⟨t3, ht3⟩ := hs.tau_ct_right
        subst ht3
        whnf at *
        intro ih
        exact .choice_right (h ih)
      · rfl
      · exact @ih t1' htaun

end CTree
