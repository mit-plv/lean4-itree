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

theorem Step.tau_ct_left
  (h : Step t1 .tau t2) : ∃ t1', t1 = C[ t1' ] := by
  cases h
  case tau =>
    rename_i t1
    exists t1.tau
  case choice_left =>
    rename_i t1 t2 _
    exists t1 ⊕ t2
  case choice_right =>
    rename_i t1 t2 _
    exists t1 ⊕ t2

theorem NTauStep.tau_ct_left
  (h : NTauStep (n + 1) t1 t2) : ∃ t1', t1 = C[ t1' ] := by
  revert t1
  match n with
  | 0 =>
    intro t1 h
    obtain ⟨t1', hs, _⟩ := h
    exact hs.tau_ct_left
  | n + 1 =>
    intro t1 h
    obtain ⟨t1', hs, hn⟩ := h
    exact hs.tau_ct_left

theorem Step.tau_ct_right
  (h : Step t1 .tau t2) : ∃ t2', t2 = C[ t2' ] := by
  generalize hl : Label.tau = l at *
  induction h <;> try contradiction
  case tau =>
    rename_i t2
    exists t2
  case choice_left h ih => exact ih hl
  case choice_right h ih => exact ih hl

theorem NTauStep.tau_ct_right
  (h : NTauStep (n + 1) t1 t2) : ∃ t2', t2 = C[ t2' ] := by
  revert t1
  induction n with
  | zero =>
    intro t1 h
    obtain ⟨t1', hs, h0⟩ := h
    subst h0
    exact hs.tau_ct_right
  | succ n ih =>
    intro t1 h
    obtain ⟨t1', hs, hn⟩ := h
    exact ih hn

lemma Step.elim_vis_val (h : Step (C[ vis e k ]) (.val v) t) : False := by
  generalize hz : CTree.vis e k = t1 at *
  cases h <;> ctree_elim hz

lemma Step.elim_tau_val (h : Step (C[ .tau t1 ]) (.val v) t2) : False := by
  generalize ht : C[ t1.tau ] = t1 at *
  cases h; all_goals ctree_elim (State.ct.inj ht)

lemma Step.elim_tau_event (h : Step (C[ .tau t1 ]) (.event α e) t2) : False := by
  generalize ht : C[ t1.tau ] = t1 at *
  cases h; all_goals ctree_elim (State.ct.inj ht)

lemma Step.elim_vis_tau (h : Step (C[ vis e k ]) .tau t) : False := by
  generalize hz : CTree.vis e k = t1 at *
  cases h <;> ctree_elim hz

lemma Step.response_kt_left (h : Step t1 (.response α a) t2) : ∃ k, t1 = K[ α | k ] := by
  generalize hl : Label.response α a = l at *
  induction h <;> try contradiction
  case response =>
    rename_i k
    have ⟨hα, _⟩ := Label.response.inj hl
    subst hα
    exists k
  all_goals
    rename_i ih
    obtain ⟨⟩ := ih hl
    contradiction

lemma Step.elim_ct_response (h : Step (C[ t1 ]) (.response α a) t2) : False := by
  have ⟨_, hk⟩ := h.response_kt_left
  contradiction

lemma WeakStep.elim_ct_response (h : WeakStep (C[ t1 ]) (.response α a) t2) : False := by
  obtain ⟨t11, t12, n1, n2, htau1, hs, htau2⟩ := h
  induction n1 with
  | zero =>
    subst htau1
    exact hs.elim_ct_response
  | succ n ih =>
    have ⟨_, h⟩ := htau1.tau_ct_right
    subst h
    exact hs.elim_ct_response

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

lemma WeakStep.ret_event (h : WeakStep (C[ ret x ]) (.event α e) t) : False := by
  obtain ⟨t2, t3, n1, n2, htau1, hs, htau2⟩ := h
  rw [htau1.ret] at htau1
  simp only [NTauStep] at htau1
  subst htau1
  generalize hret : ret x = hret at *
  cases hs <;> ctree_elim hret

lemma Step.vis_tau (h : Step (C[ vis e k ]) .tau t) : False := by
  generalize hv : CTree.vis e k = tv at *
  cases h <;> ctree_elim hv

lemma Step.vis_event_α {ε : Type → Type} {e1 : ε α1} {e2 : ε α2} {t : State ε β} {k : KTree ε α1 β}
  (h : Step (C[ vis e1 k ]) (.event α2 e2) t) : α1 = α2 := by
  generalize hc : C[ vis e1 k ] = c at *
  cases h
  case event => exact vis_inj_α <| State.ct.inj hc
  all_goals ctree_elim (State.ct.inj hc)

lemma WeakStep.vis_event_α {ε : Type → Type} {e1 : ε α1} {e2 : ε α2} {t : State ε β} {k : KTree ε α1 β}
  (h : WeakStep (C[ vis e1 k ]) (.event α2 e2) t) : α1 = α2 := by
  obtain ⟨_, _, n1, _, htau, hs, _⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau
    subst htau
    exact hs.vis_event_α
  | n + 1 =>
    obtain ⟨_, hs, _⟩ := htau
    exfalso; exact hs.vis_tau

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

lemma Step.vis_event {ε : Type → Type} {α : Type} {e : ε α} {t : State ε β} {k : KTree ε α β}
  (h : Step (C[ vis e k ]) (.event α e) t) : t = K[ k ] := by
  generalize hc : C[ vis e k ] = c at *
  cases h
  case event =>
    have ⟨_, he⟩ := vis_inj <| State.ct.inj hc
    rw [he]
  all_goals ctree_elim (State.ct.inj hc)

lemma NTauStep.cons
  (htau : Step t1 .tau t2) (htaun : NTauStep n t2 t3) : NTauStep (1 + n) t1 t3 := by
  revert t1 t2
  induction n with
  | zero =>
    intro t1 t2 htau htaun
    simp only [NTauStep] at htaun
    subst htaun
    exists t2
  | succ n ih =>
    intro t1 t2 htau htaun
    obtain ⟨t2', hs, htaun⟩ := htaun
    have := ih hs htaun
    exists t2

lemma NTauStep.append
  (h1 : NTauStep n t1 t2) (h2 : NTauStep m t2 t3) : NTauStep (n + m) t1 t3 := by
  revert t1 t2
  induction n with
  | zero =>
    intro t1 t2 h1 h2
    simp only [NTauStep] at h1
    subst h1
    rw [zero_add]
    exact h2
  | succ n ih =>
    intro t1 t2 h1 h2
    obtain ⟨t1', hs, htaun⟩ := h1
    have := ih htaun h2
    have hnm : n + 1 + m = 1 + (n + m) := by omega
    rw [hnm]
    unfold NTauStep
    split; omega
    rename_i heq
    rw [Nat.add_comm] at heq
    have := Nat.succ.inj heq
    subst this
    exists t1'

lemma Step.tau_tau (h : Step (C[ t1.tau ]) .tau t2) : t2 = C[ t1 ] := by
  generalize ht1 : C[ t1.tau ] = t1 at *
  cases h
  case tau =>
    have := tau_inj <| State.ct.inj ht1
    rw [this]
  all_goals ctree_elim State.ct.inj ht1

lemma NTauStep.inv
  (h : NTauStep (n + 1) (C[ t1.tau ]) t2) :  NTauStep n (C[ t1 ]) t2 := by
  obtain ⟨t1', htau, htaun⟩ := h
  have := htau.tau_tau
  subst this
  exact htaun

lemma WeakStep.tau_dest_tau_left {t1 : CTree ε ρ}
  (h : WeakStep (C[ t1.tau ]) .tau t2) : ∃ n, NTauStep n (C[ t1 ]) t2 := by
  obtain ⟨t11, t12, n1, n2, htau1, hs, htau2⟩ := h
  cases n1 with
  | zero =>
    simp only [NTauStep] at htau1
    subst htau1
    generalize ht1 : t1.tau = t1 at *
    cases hs <;> ctree_elim ht1
    have ht1 := tau_inj ht1
    subst ht1
    exists n2
  | succ n =>
    have := htau1.inv
    exists n + (1 + n2)
    apply NTauStep.append this
    exact NTauStep.cons hs htau2

lemma WeakStep.dest_tau_left {t1 : CTree ε ρ}
  (h : WeakStep (C[ t1.tau ]) l t2)
  : match l with
    | .tau => ∃ n, NTauStep n (C[ t1 ]) t2
    | _ => WeakStep (C[ t1 ]) l t2 := by
  match l with
  | .tau => exact h.tau_dest_tau_left
  | .val v =>
    obtain ⟨t11, t12, n1, n2, htau1, hs, htau2⟩ := h
    match n1 with
    | 0 =>
      subst htau1
      exfalso; exact hs.elim_tau_val
    | n1 + 1 =>
      have htau1 := htau1.inv
      exists t11, t12, n1, n2
  | .event α e =>
    obtain ⟨t11, t12, n1, n2, htau1, hs, htau2⟩ := h
    match n1 with
    | 0 =>
      subst htau1
      exfalso; exact hs.elim_tau_event
    | n1 + 1 =>
      have htau1 := htau1.inv
      exists t11, t12, n1, n2
  | .response α a =>
    exfalso; exact h.elim_ct_response

lemma WeakStep.vis_event {ε : Type → Type} {α : Type} {e : ε α} {t : State ε β} {k : KTree ε α β}
  (h : WeakStep (C[ vis e k ]) (.event α e) t) : t = K[ k ] := by
  obtain ⟨t1Tau, t3Tau, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    simp only [NTauStep] at htau1
    subst htau1
    have := hs.vis_event
    subst this
    match n2 with
    | 0 =>
      simp only [NTauStep] at htau2
      subst htau2; rfl
    | n + 1 =>
      obtain ⟨_, hs, _⟩ := htau2
      cases hs
  | n + 1 =>
    simp only [NTauStep] at htau1
    obtain ⟨_, hs, _⟩ := htau1
    exfalso; exact hs.vis_tau

lemma Step.vis_response {a : α} (h : Step (K[ k ]) (.response α a) t) : t = C[ k a ] := by
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

theorem Step.val_ct_left
  (h : Step t1 (.val v) t2) : ∃ t1', t1 = C[ t1' ] := by
  cases h
  case ret => exists .ret v
  case choice_left =>
    rename_i t1 t2 _
    exists t1 ⊕ t2
  case choice_right =>
    rename_i t1 t2 _
    exists t1 ⊕ t2

theorem Step.event_kt_right
  (h : Step t1 (.event α e) t2) : ∃ k, t2 = K[ α | k ] := by
  generalize hl : Label.event α e = l  at *
  induction h <;> try contradiction
  case event =>
    obtain ⟨hα, he⟩ := Label.event.inj hl
    subst hα he
    rename_i k
    exists k
  case choice_left _ ih => exact ih hl
  case choice_right _ ih => exact ih hl

theorem WeakStep.event_kt_right
  (h : WeakStep t1 (.event α e) t2) : ∃ k, t2 = K[ α | k ] := by
  obtain ⟨t11, t12, n1, n2, htau1, hs, htau2⟩ := h
  revert t1
  induction n1 with
  | zero =>
    intro t1 htau1
    subst htau1
    have ⟨k, hk⟩ := hs.event_kt_right
    subst hk
    match n2 with
    | 0 =>
      subst htau2
      exact hs.event_kt_right
    | n + 1 =>
      obtain ⟨_, hs, _⟩ := htau2
      have ⟨_, _⟩ := hs.tau_ct_left
      contradiction
  | succ n ih =>
    intro t1 htau1
    obtain ⟨t1', hs, hn⟩ := htau1
    exact ih hn

theorem Step.event_ct_left
  (h : Step t1 (.event α e) t2) : ∃ t1', t1 = C[ t1' ] := by
  cases h
  case event =>
    rename_i k
    exists .vis e k
  case choice_left =>
    rename_i t1 t2 _
    exists t1 ⊕ t2
  case choice_right =>
    rename_i t1 t2 _
    exists t1 ⊕ t2

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

lemma weak_step_of_ContainsVis {ε : Type → Type} {α : Type} {e : ε α} {t : CTree ε ρ} {k : KTree ε α ρ}
  (h : ContainsVis e k t)
  : WeakStep (C[ t ]) (.event α e) (K[ k ]) := by
  induction h with
  | vis =>
    exists C[ vis e k ], K[ k ], 0, 0
    apply And.intro
    · simp only [NTauStep]
    · apply And.intro .event
      simp only [NTauStep]
  | tau h ih =>
    have ⟨t1, t2, n1, n2, htau1, hs, htau2⟩ := ih
    exists t1, t2, n1 + 1, n2
    apply And.intro _ ⟨hs, htau2⟩
    simp only [NTauStep]
    rename_i t
    exists C[ t ]
    exact And.intro .tau htau1
  | choice_left _ ih => exact WeakStep.choice_left_left ih
  | choice_right _ ih => exact WeakStep.choice_left_right ih

-- Lemma for event steps
lemma refine_event_correspondence {ε : Type → Type} {β : Type}
  {p1 p2 : ENat} {t1 t2 : CTree ε β} (href : Refine' Eq p1 p2 t1 t2)
  : ∀ {α} {e : ε α} (k1 : KTree ε α β), Step (C[ t1 ]) (.event α e) (K[ k1 ]) →
    ∃ k2, WeakStep (C[ t2 ]) (.event α e) (K[ k2 ]) ∧ Refine'K Eq p1 p2 k1 k2 := by
  intro α e k1 hstep
  apply Step.rec
    (motive := fun t1 l k1 step =>
      l = .event α e →
      match t1, k1 with
      | C[ t1 ], K[ k1 ] =>
        Refine' Eq p1 p2 t1 t2 →
        ∃ k2, WeakStep (C[ t2 ]) (.event α e) (K[ k2 ]) ∧ Refine'K Eq p1 p2 k1 k2
      | _, _ => False
    ) (t := hstep)
  <;> try (intros; intros; whnf; contradiction)
  case event =>
    intro α e k1 hl href
    obtain ⟨hα, he⟩ := Label.event.inj hl
    subst hα he
    obtain ⟨k2, hcont, href⟩ := href.inv_vis_left
    exists k2
    exact And.intro (weak_step_of_ContainsVis hcont) href
  case choice_left =>
    intro l t1 t2 t3 hs h hl
    subst hl
    have h := h rfl
    split at h; on_goal 2 => contradiction
    intro ih
    rename_i heq _ _
    have heq := State.ct.inj heq
    subst heq
    exact h ih.inv_choice_left_left
  case choice_right =>
    intro l t1 t2 t3 hs h hl
    subst hl
    have h := h rfl
    split at h; on_goal 2 => contradiction
    intro ih
    rename_i heq _ _
    have heq := State.ct.inj heq
    subst heq
    exact h ih.inv_choice_left_right
  · rfl
  · exact href

  lemma RefineF.ret_of_weak_step {sim : ENat → ENat → CTree ε ρ → CTree ε ρ → Prop}
    {x : ρ} (h : WeakStep (C[ t ]) (Label.val x) t') : RefineF Eq sim p1 p2 (CTree.ret x) t := by
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
      case choice_right =>
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
      case choice_left =>
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
      case choice_right =>
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

theorem RefineF.of_WeakStep_event
  {sim : State ε ρ → State ε ρ → Prop}
  {k : KTree ε α ρ}
  (hsim : IsWeakSimulation sim)
  (h : sim (K[ k ]) t2')
  (hws : WeakStep (C[ t2 ]) (Label.event α e) t2')
  : RefineF Eq (fun _ _ t1 t2 => sim (C[ t1 ]) (C[ t2 ])) p1 p2 (.vis e k) t2 := by
  obtain ⟨t21, t22, n1, n2, htau1, hs, htau2⟩ := hws
  revert t2
  induction n1 with
  | zero =>
    intro t2 htau1
    subst htau1
    match n2 with
    | 0 =>
      subst htau2
      have ⟨k2, hk2⟩ := hs.event_kt_right
      subst hk2
      apply Step.rec
        (motive := fun t2 l k2 step =>
          l = .event α e →
          match t2, k2 with
          | C[ t2 ], K[ k2 ] =>
            sim (K[ k ]) (K[ k2 ])
            → RefineF Eq (fun p1 p2 t1 t2 => sim (C[ t1 ]) (C[ t2 ])) p1 p2 (.vis e k) t2
          | _, _ => False
        ) (t := hs)
      <;> try (intros; intros; whnf; contradiction)
      case event =>
        intro α e k hl h
        simp only [Label.event.injEq] at hl
        obtain ⟨hα, he⟩ := hl
        subst hα he
        apply RefineF.vis (p1' := 0) (p2' := 0)
        intro a
        have ⟨_, hk⟩ := hsim _ _ h
        simp only at hk
        exact hk a
      case choice_left =>
        intro l t1 t2 t3 hs h hl
        have h := h hl
        subst hl
        have ⟨k, hk⟩ := hs.event_kt_right
        subst hk
        intro ih
        exact RefineF.choice_left (RefineF.idx_mono (le_refl _) le_top <| h ih)
      case choice_right =>
        intro l t1 t2 t3 hs h hl
        have h := h hl
        subst hl
        have ⟨k, hk⟩ := hs.event_kt_right
        subst hk
        intro ih
        exact RefineF.choice_right (RefineF.idx_mono (le_refl _) le_top <| h ih)
      · rfl
      · exact h
    | n + 1 =>
      have ⟨k2, hk2⟩ := hs.event_kt_right
      subst hk2
      obtain ⟨_, hs, _⟩ := htau2
      have ⟨_, _⟩ := hs.tau_ct_left
      contradiction
  | succ n ih =>
    intro t2 htau1
    have ⟨t2', ht2'⟩ := htau1.tau_ct_right
    subst ht2'
    obtain ⟨t2'', hs, hn⟩ := htau1
    obtain ⟨t2'', ht2''⟩ := hs.tau_ct_right
    subst ht2''
    have href := ih hn
    apply Step.rec
      (motive := fun t2 l t2'' step =>
        l = .tau →
        match t2, t2'' with
        | C[ t2 ], C[ t2'' ] =>
          RefineF Eq (fun p1 p2 t1 t2 => sim (C[ t1 ]) (C[ t2 ])) p1 p2 (.vis e k) t2''
          → RefineF Eq (fun p1 p2 t1 t2 => sim (C[ t1 ]) (C[ t2 ])) p1 p2 (.vis e k) t2
        | _, _ => False
      ) (t := hs)
    <;> try (intros; intros; whnf; contradiction)
    case tau =>
      intro _ _ ih
      exact RefineF.tau_right (RefineF.idx_mono (le_refl _) le_top <| ih)
    case choice_left =>
      intro l t1 t2 t3 hs h hl
      have h := h hl
      subst hl
      have ⟨t3, ht3⟩ := hs.tau_ct_right
      subst ht3
      intro ih
      have h := h ih
      exact RefineF.choice_left (RefineF.idx_mono (le_refl _) le_top <| h)
    case choice_right =>
      intro l t1 t2 t3 hs h hl
      have h := h hl
      subst hl
      have ⟨t3, ht3⟩ := hs.tau_ct_right
      subst ht3
      intro ih
      have h := h ih
      exact RefineF.choice_right (RefineF.idx_mono (le_refl _) le_top <| h)
    · rfl
    · exact href

theorem Step.inv_choice_left
  (h : Step (C[ t1 ⊕ t2 ]) l t3)
  : Step (C[ t1 ]) l t3 ∨ Step (C[ t2 ]) l t3 := by
  generalize ht1 : t1 ⊕ t2 = t1 at *
  cases h <;> ctree_elim ht1
  all_goals
    rename_i h
    have ⟨ht1, ht2⟩ := choice_inj ht1
    subst ht1 ht2
  · left; exact h
  · right; exact h

theorem WeakStep.inv_choice_left
  (h : WeakStep (C[ t1 ⊕ t2 ]) l t3)
  : WeakStep (C[ t1 ]) l t3 ∨ WeakStep (C[ t2 ]) l t3 := by
  obtain ⟨t11, t12, n1, n2, htau1, hs, htau2⟩ := h
  match n1 with
  | 0 =>
    subst htau1
    apply hs.inv_choice_left.elim
    · intro h
      left
      exists C[ t1 ], t12, 0, n2
    · intro h
      right
      exists C[ t2 ], t12, 0, n2
  | n + 1 =>
    obtain ⟨t1', htau, htaun⟩ := htau1
    have ⟨t1', ht1'⟩ := htau.tau_ct_right
    subst ht1'
    generalize hc : t1 ⊕ t2 = c at *
    cases htau <;> ctree_elim hc
    on_goal 1 => left
    on_goal 2 => right
    all_goals
      rename_i h
      have ⟨ht1, ht2⟩ := choice_inj hc
      subst ht1 ht2
      exists t11, t12, n + 1, n2
      apply And.intro _ ⟨hs, htau2⟩
      exists C[ t1' ]

end CTree
