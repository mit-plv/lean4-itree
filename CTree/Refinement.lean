import CTree.Basic
import CTree.Monad
import Mathlib.Data.ENat.Basic
import CTree.Paco

namespace CTree
  /--
    The definition uses ideas from the [FreeSim paper](https://dl.acm.org/doi/10.1145/3622857)

    Note that this is not equivalent to `TraceRefine`, becasuse `TraceRefine` makes no distinction between `zero` and `infND`.
  -/
  inductive RefineF {ε : Type → Type} {ρ σ : Type}
    (r : Rel ρ σ) (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    : ENat → ENat → CTree ε ρ → CTree ε σ → Prop
  | coind {p1 p2 t1 t2} (p1' p2' : ENat)
      (h1 : p1' < p1) (h2 : p2' < p2) (h : sim p1' p2' t1 t2)
      : RefineF r sim p1 p2 t1 t2
  | ret {x y p1 p2} (h : r x y) : RefineF r sim p1 p2 (ret x) (ret y)
  | vis {p1' p2' p1 p2} {α : Type} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
      (h : ∀ a : α, sim p1' p2' (k1 a) (k2 a)) : RefineF r sim p1 p2 (vis e k1) (vis e k2)
  | tau_left {p1 p2 t1 t2}
      (h : RefineF r sim ⊤ p2 t1 t2) : RefineF r sim p1 p2 t1.tau t2
  | tau_right {p1 p2 t1 t2}
      (h : RefineF r sim p1 ⊤ t1 t2) : RefineF r sim p1 p2 t1 t2.tau
  | zero {p1 p2} {t : CTree ε σ} : RefineF r sim p1 p2 zero t
  | choice_left {p1 p2 t1 t2 t3}
      (h : RefineF r sim p1 ⊤ t1 t2) : RefineF r sim p1 p2 t1 (t2 ⊕ t3)
  | choice_right {p1 p2 t1 t2 t3}
      (h : RefineF r sim p1 ⊤ t1 t3) : RefineF r sim p1 p2 t1 (t2 ⊕ t3)
  | choice_idemp {p1 p2 t1 t2 t3}
      (h1 : RefineF r sim ⊤ p2 t1 t3) (h2 : RefineF r sim ⊤ p2 t2 t3)
      : RefineF r sim p1 p2 (t1 ⊕ t2) t3

  theorem RefineF.monotone (r : Rel ρ σ) (sim sim' : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    (hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → sim' p1 p2 t1 t2)
    {p1 p2 t1 t2} (h : RefineF r sim p1 p2 t1 t2) : RefineF r sim' p1 p2 t1 t2 := by
    induction h with
    | coind _ _ h1 h2 h => exact .coind _ _ h1 h2 (hsim _ _ _ _ h)
    | ret h => exact .ret h
    | vis h => exact .vis λ a => hsim _ _ _ _ <| h a
    | tau_left _ ih => exact RefineF.tau_left ih
    | tau_right _ ih => exact RefineF.tau_right ih
    | zero => exact .zero
    | choice_left _ ih => exact .choice_left ih
    | choice_right _ ih => exact .choice_right ih
    | choice_idemp _ _ ih1 ih2 => exact .choice_idemp ih1 ih2

  def Refine' (r : Rel ρ σ) (p1 p2 : ENat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    RefineF r (Refine' r) p1 p2 t1 t2
    greatest_fixpoint monotonicity by
      intro _ _ hsim _ _ _ _ h
      apply RefineF.monotone (hsim := hsim) (h := h)

  abbrev Refine (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) :=
    ∃ p1 p2, Refine' r p1 p2 t1 t2

  -- `t1 r≤ t2` looks better, but somehow clashes with multi-line class instance definition
  notation:60 t1:61 " ≤"r:61"≤ " t2:61 => Refine r t1 t2

  theorem RefineF.idx_mono {t1 : CTree ε ρ} {t2 : CTree ε σ}
    {p1' p1 p2' p2 : ENat} (h1 : p1' ≤ p1) (h2 : p2' ≤ p2) (h : RefineF r sim p1' p2' t1 t2)
    : RefineF r sim p1 p2 t1 t2 := by
    revert p1 p2
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros _ _ h1 h2; apply RefineF.coind p1'' p2'' _ _ h
      exact lt_of_lt_of_le h1' h1
      exact lt_of_lt_of_le h2' h2
    | ret h => intros; exact RefineF.ret h
    | vis h => intros; exact RefineF.vis h
    | tau_left h ih =>
      intros _ _ _ h2; apply RefineF.tau_left
      exact ih le_top h2
    | tau_right h ih =>
      intros _ _ h1 _; apply RefineF.tau_right
      exact ih h1 le_top
    | zero => intros; exact RefineF.zero
    | choice_left h ih =>
      intros _ _ h1 _; apply RefineF.choice_left
      exact ih h1 le_top
    | choice_right h ih =>
      intros _ _ h1 _; apply RefineF.choice_right
      exact ih h1 le_top
    | choice_idemp h1' h2' ih1 ih2 =>
      intros _ _ h1 h2; apply RefineF.choice_idemp
      · exact ih1 le_top h2
      · exact ih2 le_top h2

  macro "crush_cont_aux" ih:term ", " h_ih:term : tactic => `(tactic|(
    first
      | apply RefineF.ret; assumption
      | apply RefineF.vis; intros a; exact $(Lean.mkIdent `hk) a
      | first | apply RefineF.tau_left | apply RefineF.choice_idemp
        all_goals
          apply RefineF.idx_mono
          <;> first | assumption | apply le_top
      | apply $h_ih $ih
        first
          | exact .inr <| .inr rfl
          | exact .inr <| .inl ⟨_, rfl⟩
          | exact .inl ⟨_, rfl⟩
  ))

  macro "crush_cont" ih:term ", " h_ih:term : tactic => `(tactic|(
    intros
    rename_i cont _ _
    apply cont.elim3
    · intro h
      obtain ⟨_, h⟩ := h
      rw [h]
      apply RefineF.choice_right
      crush_cont_aux $ih, $h_ih
    · intro h
      obtain ⟨_, h⟩ := h
      rw [h]
      apply RefineF.choice_left
      crush_cont_aux $ih, $h_ih
    · intro h
      rw [h]
      apply RefineF.tau_right
      crush_cont_aux $ih, $h_ih
  ))

  /--
    If `t1` refines `t2'`, then for any `t2` that may *continue* as `t2'`, `t1` must refine `t2`.

    By *continue* we mean that `t2'` shows up as a choice within `t2` or is a `tau` step behind `t2`.
  -/
  theorem RefineF.cont_right {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    (h : RefineF r sim p1 p2 t1 t2') :
    ∀ (t2 : CTree ε σ), ((∃ t1', t2 = t1' ⊕ t2') ∨ (∃ t1', t2 = t2' ⊕ t1') ∨ t2 = t2'.tau) →
    ∀ p1' p2', RefineF r sim p1' p2' t1 t2 := by
    revert p2 t1 t2 t2'
    induction p1 using WellFoundedLT.induction
    rename_i ih
    intro _ _ _ _ h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      apply ih _ h1' (hsim _ _ _ _ h); assumption
    | ret => crush_cont _, _
    | vis hk => crush_cont _, _
    | tau_left h => crush_cont _, _
    | tau_right h h_ih => crush_cont ih, h_ih
    | zero => intros; exact RefineF.zero
    | choice_left h h_ih => crush_cont ih, h_ih
    | choice_right h h_ih => crush_cont ih, h_ih
    | choice_idemp _ _ => crush_cont _, _

  theorem RefineF.idx_irrelevance_gen {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    (h : RefineF r sim p1 p2 t1 t2)
    : ∀ p1' p2', RefineF r sim p1' p2' t1 t2 := by
    revert t1 t2 p1
    induction p2 using WellFoundedLT.induction
    rename_i p1 ih_p1
    intro p1 t1 t2 h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intro p1' p2'
      exact ih_p1 p2'' h2' (hsim _ _ _ _ h) p1' p2'
    | ret h =>
      intros; apply RefineF.ret; assumption
    | vis hk =>
      intros; apply RefineF.vis; assumption
    | tau_left h ih =>
      intros; apply RefineF.tau_left; apply ih; assumption
    | tau_right h =>
      intros
      apply RefineF.cont_right <;> try assumption
      exact (.inr (.inr rfl))
    | zero => intros; exact RefineF.zero
    | choice_left h =>
      intros
      apply RefineF.cont_right <;> try assumption
      exact (.inr (.inl ⟨_, by rfl⟩))
    | choice_right h =>
      intros
      apply RefineF.cont_right <;> try assumption
      exact (.inl ⟨_, by rfl⟩)
    | choice_idemp h1 h2 ih1 ih2 =>
      intro p1 t1
      apply RefineF.choice_idemp
      · apply ih1; assumption
      · apply ih2; assumption

  theorem RefineF.idx_irrelevance {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    (h : RefineF r (Refine' r) p1 p2 t1 t2)
    : ∀ p1' p2', RefineF r (Refine' r) p1' p2' t1 t2 := by
    apply h.idx_irrelevance_gen; intros; rw [← Refine']; assumption

  theorem Refine'.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2)
    (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : Refine' r p1 p2 t1 t2 :=
    Refine'.fixpoint_induct r sim adm p1 p2 t1 t2 h

  theorem Refine'.inv_ret_left {r1 : Rel ρ1 σ} {r2 : Rel ρ2 σ}
    {p1 p2 x} {t : CTree ε σ}
    (h : Refine' r1 p1 p2 (.ret x) t)
    : ∀ y, (∀ z, r1 x z → r2 y z) → Refine' r2 p1 p2 (.ret y) t := by
    intro y hyz
    generalize eq_t1 : ret y = t1
    generalize eq_t1' : ret x = t1' at h
    revert x y t1
    revert p1 p2 t1' t
    pcofix
    intro p1 p2 t t1' h
    punfold at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros x y hyz t _ _
      rename_i eq_ret eq_ret'
      subst eq_ret eq_ret'
      pfold
      apply RefineF.coind <;> try assumption
      rename_i p1 p2 t2
      pclearbot at h
      pleft
      apply cih <;> try assumption
      all_goals rfl
    | ret h =>
      intros x y hyz t eq_ret eq_ret'
      apply ret_inj at eq_ret'
      subst eq_ret eq_ret'
      pfold
      apply RefineF.ret; apply hyz; assumption
    | vis h =>
      intros
      rename_i _ _ eq_ret
      ctree_elim eq_ret
    | tau_left h ih =>
      intros
      rename_i _ _ eq_ret
      ctree_elim eq_ret
    | tau_right h ih =>
      intros
      pfold
      apply RefineF.tau_right
      rw [← @plfp_unfold (f := RefineF r2)]
      apply ih <;> assumption
    | zero =>
      intros
      rename_i _ _ eq_ret
      ctree_elim eq_ret
    | choice_left h ih =>
      intros
      pfold
      apply RefineF.choice_left
      rw [← @plfp_unfold (f := RefineF r2)]
      apply ih <;> assumption
    | choice_right h ih =>
      intros
      pfold
      apply RefineF.choice_right
      rw [← @plfp_unfold (f := RefineF r2)]
      apply ih <;> assumption
    | choice_idemp h1 h2 =>
      intros
      rename_i _ _ eq_ret
      ctree_elim eq_ret

  theorem Refine'.inv_ret_right {r1 : Rel ρ σ1} {r2 : Rel ρ σ2}
    {p1 p2 x} {t : CTree ε ρ}
    (h : Refine' r1 p1 p2 t (.ret x))
    : ∀ y, (∀ z, r1 z x → r2 z y) → Refine' r2 p1 p2 t (.ret y) := by
    intro y hyz
    apply Refine'.coind (fun p1 p2 t1 t2 => ∃ x y t', t' = ret x ∧ Refine' r1 p1 p2 t1 t' ∧ (∀ z, r1 z x → r2 z y) ∧ ret y = t2)
    on_goal 2 => exact ⟨x, ⟨y, ⟨ret x, by simp_all only [implies_true, and_self]⟩⟩⟩
    clear *-
    intro p1 p2 t1 t2 h
    have ⟨x, ⟨y, ⟨t', ⟨eq_ret, ⟨h', ⟨impl, eq_ret'⟩⟩⟩⟩⟩⟩ := h
    clear h
    revert t2 x y
    rw [Refine'] at h'
    induction h' with
    | coind p1'' p2'' h1' h2' h =>
      intros t x y _ _ _
      rename_i eq_ret impl eq_ret'
      subst eq_ret eq_ret'
      apply RefineF.coind <;> try assumption
      exact ⟨x, ⟨y, ⟨.ret x, by simp_all only [implies_true, and_self]⟩⟩⟩
    | ret h =>
      intros t x y eq_ret impl eq_ret'
      rename_i x' y' p1' p2'
      apply ret_inj at eq_ret
      subst eq_ret eq_ret'
      apply RefineF.ret; apply impl; assumption
    | vis h =>
      intros
      rename_i eq_ret _ _
      ctree_elim eq_ret
    | tau_left h ih =>
      intros
      apply RefineF.tau_left; apply ih <;> assumption
    | tau_right h =>
      intros
      rename_i eq_ret _ _
      ctree_elim eq_ret
    | zero =>
      intros; exact RefineF.zero
    | choice_left h =>
      intros
      rename_i eq_ret _ _
      ctree_elim eq_ret
    | choice_right h =>
      intros
      rename_i eq_ret _ _
      ctree_elim eq_ret
    | choice_idemp h1 h2 =>
      intros
      rename_i h1_ih h2_ih _ _ _ _ _ _
      apply RefineF.choice_idemp
      · apply h1_ih <;> assumption
      · apply h2_ih <;> assumption

  theorem Refine'.inv_tau_left {r : Rel ρ σ} {p1 p2 t'} {t : CTree ε σ}
    (h : Refine' r p1 p2 (.tau t') t) : Refine' r p1 p2 t' t := by
    apply Refine'.coind (fun p1 p2 t1 t2 => ∃ t'', t'' = tau t1 ∧ Refine' r p1 p2 t'' t2)
    on_goal 2 => exact ⟨t'.tau, by simp_all only [and_self]⟩
    clear *-
    intro p1 p2 t1 t2 h
    have ⟨t'', ⟨eq_tau, h'⟩⟩ := h
    clear h
    revert t1 eq_tau
    rw [Refine'] at h'
    induction h' with
    | coind p1'' p2'' h1' h2' h =>
      intros t eq_tau
      subst eq_tau
      apply RefineF.coind <;> try assumption
      exists t.tau
    | ret h =>
      intros t eq_tau
      ctree_elim eq_tau
    | vis h =>
      intros t eq_tau
      ctree_elim eq_tau
    | tau_left h ih =>
      intros t eq_tau
      apply tau_inj at eq_tau
      subst eq_tau
      apply RefineF.monotone
      on_goal 2 => apply RefineF.idx_irrelevance <;> assumption
      intro p1 p2 t1 t2 h
      exists t1.tau
      apply And.intro rfl
      rw [Refine'] at *
      apply RefineF.tau_left
      apply RefineF.idx_mono <;> (try assumption) <;> (try apply le_top)
      apply le_refl
    | tau_right h =>
      intros
      apply RefineF.tau_right
      rename_i h_ih _ _
      apply h_ih; assumption
    | zero =>
      intros t eq_tau
      ctree_elim eq_tau
    | choice_left h =>
      intros
      apply RefineF.choice_left
      rename_i h_ih _ _
      apply h_ih; assumption
    | choice_right h =>
      intros
      apply RefineF.choice_right
      rename_i h_ih _ _
      apply h_ih; assumption
    | choice_idemp h1 h2 =>
      intros t eq_tau
      ctree_elim eq_tau

  theorem Refine'.inv_tau_right {r : Rel ρ σ} {p1 p2 t'} {t : CTree ε ρ}
    (h : Refine' r p1 p2 t (.tau t')) : Refine' r p1 p2 t t' := by
    apply Refine'.coind (fun p1 p2 t1 t2 => ∃ t'', t'' = tau t2 ∧ Refine' r p1 p2 t1 t'')
    on_goal 2 => exact ⟨t'.tau, by simp_all only [and_self]⟩
    clear *-
    intro p1 p2 t1 t2 h
    have ⟨t'', ⟨eq_tau, h'⟩⟩ := h
    clear h
    revert t2 eq_tau
    rw [Refine'] at h'
    induction h' with
    | coind p1'' p2'' h1' h2' h =>
      intros t eq_tau
      subst eq_tau
      apply RefineF.coind <;> try assumption
      exists t.tau
    | ret h =>
      intros t eq_tau
      ctree_elim eq_tau
    | vis h =>
      intros t eq_tau
      ctree_elim eq_tau
    | tau_left h ih =>
      intros t eq_tau
      subst eq_tau
      have ih' := ih t rfl
      apply RefineF.tau_left; assumption
    | tau_right h =>
      intros t eq_tau
      apply tau_inj at eq_tau
      subst eq_tau
      apply RefineF.monotone
      on_goal 2 => apply RefineF.idx_irrelevance <;> assumption
      intro p1 p2 t1 t2 h
      exists t2.tau
      apply And.intro rfl
      rw [Refine'] at *
      apply RefineF.tau_right
      apply RefineF.idx_mono <;> (try assumption) <;> (try apply le_top)
      apply le_refl
    | zero =>
      intros; exact RefineF.zero
    | choice_left h =>
      intros t eq_tau
      ctree_elim eq_tau
    | choice_right h =>
      intros t eq_tau
      ctree_elim eq_tau
    | choice_idemp h1 h2 =>
      intros t eq_tau
      rename_i h1_ih h2_ih
      apply RefineF.choice_idemp
      · apply h1_ih; assumption
      · apply h2_ih; assumption

  theorem Refine'.inv_zero_right {r1 : Rel ρ σ1} {r2 : Rel ρ σ2} {p1 p2} {t1 : CTree ε ρ}
    (h : Refine' r1 p1 p2 t1 zero) : ∀ t2, Refine' r2 p1 p2 t1 t2 := by
    intro t2
    apply Refine'.coind (fun p1 p2 t1 t2 => ∃ t, t = zero ∧ Refine' r1 p1 p2 t1 t)
    on_goal 2 => exact ⟨zero, And.intro rfl h⟩
    clear *-
    intro p1 p2 t1 t2 h
    have ⟨t, ⟨eq_zero, h'⟩⟩ := h
    clear h
    revert t2
    rw [Refine'] at h'
    induction h' with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_zero
      apply RefineF.coind <;> try assumption
      exact ⟨zero, And.intro rfl h⟩
    | ret h =>
      intros; ctree_elim eq_zero
    | vis h =>
      intros; ctree_elim eq_zero
    | tau_left h ih =>
      intros; subst eq_zero
      apply RefineF.tau_left; apply ih rfl
    | tau_right h =>
      intros; ctree_elim eq_zero
    | zero =>
      intros; exact RefineF.zero
    | choice_left h =>
      intros; ctree_elim eq_zero
    | choice_right h =>
      intros; ctree_elim eq_zero
    | choice_idemp h1 h2 =>
      intros; subst eq_zero
      rename_i h1_ih h2_ih
      apply RefineF.choice_idemp <;>
      first | apply h1_ih rfl | apply h2_ih rfl

  theorem Refine'.inv_choice_left_left {r : Rel ρ σ} {p1 p2 t1 t2} {t : CTree ε σ}
    (h : Refine' r p1 p2 (t1 ⊕ t2) t) : Refine' r p1 p2 t1 t := by
    apply Refine'.coind (fun p1 p2 t1 t2 => ∃ t' t'', t'' = t1 ⊕ t' ∧ Refine' r p1 p2 t'' t2)
    on_goal 2 => exact ⟨t2, ⟨t1 ⊕ t2, by simp_all only [and_self]⟩⟩
    clear *-
    intro p1 p2 t1 t2 h
    have ⟨t', ⟨t'', ⟨eq_choice, h'⟩⟩⟩ := h
    clear h
    revert t' t1
    rw [Refine'] at h'
    induction h' with
    | coind p1'' p2'' h1' h2' h =>
      intros t t' eq_choice
      subst eq_choice
      apply RefineF.coind <;> try assumption
      exists t', (t ⊕ t')
    | ret h =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | vis h =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | tau_left h ih =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | tau_right h =>
      intros
      apply RefineF.tau_right
      rename_i h_ih _ _ _
      apply h_ih; assumption
    | zero =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | choice_left h =>
      intros
      apply RefineF.choice_left
      rename_i h_ih _ _ _
      apply h_ih; assumption
    | choice_right h =>
      intros
      apply RefineF.choice_right
      rename_i h_ih _ _ _
      apply h_ih; assumption
    | choice_idemp h1 h2 =>
      intros t t' eq_choice
      apply choice_inj at eq_choice
      have ⟨eq_choiceL, eq_choiceR⟩ := eq_choice
      subst eq_choiceL eq_choiceR
      apply RefineF.monotone
      on_goal 2 => apply RefineF.idx_irrelevance <;> assumption
      intro p1 p2 t1 t2 h
      exists t1, (t1 ⊕ t1)
      apply And.intro rfl
      rw [Refine'] at *
      apply RefineF.choice_idemp
      all_goals apply RefineF.idx_mono <;> (try assumption) <;> (try apply le_top); apply le_refl

  theorem Refine'.inv_choice_left_right {r : Rel ρ σ} {p1 p2 t1 t2} {t : CTree ε σ}
    (h : Refine' r p1 p2 (t1 ⊕ t2) t) : Refine' r p1 p2 t2 t := by
    apply Refine'.coind (fun p1 p2 t1 t2 => ∃ t' t'', t'' = t' ⊕ t1 ∧ Refine' r p1 p2 t'' t2)
    on_goal 2 => exact ⟨t1, ⟨t1 ⊕ t2, by simp_all only [and_self]⟩⟩
    clear *-
    intro p1 p2 t1 t2 h
    have ⟨t', ⟨t'', ⟨eq_choice, h'⟩⟩⟩ := h
    clear h
    revert t' t1
    rw [Refine'] at h'
    induction h' with
    | coind p1'' p2'' h1' h2' h =>
      intros t t' eq_choice
      subst eq_choice
      apply RefineF.coind <;> try assumption
      exists t', (t' ⊕ t)
    | ret h =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | vis h =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | tau_left h ih =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | tau_right h =>
      intros
      apply RefineF.tau_right
      rename_i h_ih _ _ _
      apply h_ih; assumption
    | zero =>
      intros t t' eq_choice
      ctree_elim eq_choice
    | choice_left h =>
      intros
      apply RefineF.choice_left
      rename_i h_ih _ _ _
      apply h_ih; assumption
    | choice_right h =>
      intros
      apply RefineF.choice_right
      rename_i h_ih _ _ _
      apply h_ih; assumption
    | choice_idemp h1 h2 =>
      intros t t' eq_choice
      apply choice_inj at eq_choice
      have ⟨eq_choiceL, eq_choiceR⟩ := eq_choice
      subst eq_choiceL eq_choiceR
      apply RefineF.monotone
      on_goal 2 => apply RefineF.idx_irrelevance <;> assumption
      intro p1 p2 t1 t2 h
      exists t1, (t1 ⊕ t1)
      apply And.intro rfl
      rw [Refine'] at *
      apply RefineF.choice_idemp
      all_goals apply RefineF.idx_mono <;> (try assumption) <;> (try apply le_top); apply le_refl

  theorem Refine'.trans {r12 : Rel ρ1 ρ2} {r23 : Rel ρ2 ρ3}
    {p11 p12} {t1 : CTree ε ρ1} {t2}
    (h : Refine' r12 p11 p12 t1 t2)
    : ∀ {p21 p22 t3},
      Refine' r23 p21 p22 t2 t3 →
      Refine' (r12.comp r23) p11 p22 t1 t3 := by
    intros p21 p22 t3 h2
    apply Refine'.coind (λ p11 p22 t1 t3 => Refine' (r12.comp r23) p11 p22 t1 t3 ∨ ∃ p12 p21 t2, Refine' r12 p11 p12 t1 t2 ∧ Refine' r23 p21 p22 t2 t3)
    on_goal 2 => apply Or.intro_right; exists p12, p21, t2
    clear *-
    intros p11 p22 t1 t3 h
    cases h
    on_goal 1 =>
      rename_i h
      rw [Refine'] at h
      apply RefineF.monotone <;> try assumption
      intros; apply Or.intro_left; assumption
    rename_i h
    have ⟨p12, ⟨p21, ⟨t2, ⟨h1, h2⟩⟩⟩⟩ := h
    clear h
    rw [Refine'] at h1
    revert t3 p21 p22
    induction h1 with
    | coind p1'' p2'' h1' h2' h =>
      rename_i p11 p22 t1 t2
      intros p22 t3 p21 h2
      revert t1 h
      rw [Refine'] at h2
      induction h2 with
      | coind p1'' p2'' h1' h2' h =>
        intros
        apply RefineF.coind <;> try assumption
        apply Or.intro_right
        rename_i h'
        exact ⟨_, ⟨_, ⟨_, And.intro h' h⟩⟩⟩
      | ret h =>
        intro t1 h
        rw [Refine'] at h
        apply RefineF.monotone (sim := Refine' (r12.comp r23))
        · intros; rename_i h; apply Or.intro_left; assumption
        · rw [← Refine']; apply Refine'.inv_ret_right
          · rw [Refine'] <;> (try apply RefineF.idx_irrelevance) <;> assumption
          · rename_i x y _ _ _; intros; exists x
      | vis h =>
        rename_i α e k1 k2
        intros t1 h
        rw [Refine'] at h
        have h' : ∃ p1'' p2'' t2, p2'' = 0 ∧ t2 = vis e k1 ∧ RefineF r12 (Refine' r12) p1'' p2'' t1 t2 :=
          ⟨0, ⟨0, ⟨vis e k1, And.intro rfl (And.intro rfl (by apply RefineF.idx_irrelevance; assumption))⟩⟩⟩
        clear h
        have ⟨p1'', ⟨p2'', ⟨t2, ⟨eq_idx, ⟨eq_vis, h⟩⟩⟩⟩⟩ := h'
        clear h'
        revert eq_idx eq_vis
        induction h with
        | coind p1'' p2'' h1' h2' h =>
          intro eq_idx eq_vis; subst eq_idx eq_vis
          apply not_lt_bot at h2'; cases h2'
        | ret h =>
          intro eq_idx eq_vis
          ctree_elim eq_vis
        | vis hk =>
          intro eq_idx eq_vis
          rename_i cont _ _ α' e' k1' k2' h_ih'
          have eq_α := vis_inj_α eq_vis
          subst eq_α
          have ⟨eq1, eq2⟩ := vis_inj eq_vis
          clear eq_vis
          subst eq1 eq2
          apply RefineF.vis (p1' := ⊤) (p2' := ⊤); intro a
          right
          rename_i p21 _ _ _ p12 _
          exists p12, p21, h_ih' a
          simp only [Refine'] at *
          apply And.intro
          · apply RefineF.idx_mono le_top (le_refl _)
            exact hk a
          · apply RefineF.idx_mono (le_refl _) le_top
            exact h a
        | tau_left h ih =>
          intro eq_idx eq_vis; subst eq_idx eq_vis
          apply RefineF.tau_left
          apply RefineF.idx_mono (p1' := p11) <;>
          first | apply le_top | apply le_refl | apply ih rfl rfl
        | tau_right h =>
          intro _ eq_vis; ctree_elim eq_vis
        | zero => intros; apply RefineF.zero
        | choice_left h =>
          intro _ eq_vis; ctree_elim eq_vis
        | choice_right h =>
          intro _ eq_vis; ctree_elim eq_vis
        | choice_idemp h1 h2 =>
          intro eq_idx eq_vis; subst eq_idx eq_vis
          rename_i h1_ih h2_ih
          apply RefineF.choice_idemp <;>
          apply RefineF.idx_mono (p1' := p11) <;>
          first | apply le_top | apply le_refl | apply h1_ih rfl rfl | apply h2_ih rfl rfl
      | tau_left h ih =>
        intro t1 h'
        apply Refine'.inv_tau_right at h'
        apply ih; assumption
      | tau_right h =>
        rename_i h_ih
        intros
        apply RefineF.tau_right
        apply h_ih; assumption
      | zero =>
        intro t1 h
        rw [Refine'] at h
        apply RefineF.monotone (sim := Refine' (r12.comp r23))
        · intros; rename_i h; apply Or.intro_left; assumption
        · rw [← Refine']; apply Refine'.inv_zero_right; rw [Refine'];
          apply RefineF.idx_irrelevance; assumption
      | choice_left h =>
        rename_i h_ih
        intros; apply RefineF.choice_left; apply h_ih; assumption
      | choice_right h =>
        rename_i h_ih
        intros; apply RefineF.choice_right; apply h_ih; assumption
      | choice_idemp h1 h2 =>
        rename_i p1 p2 t t' t'' h1_ih h2_ih
        intros t1 h
        rw [Refine'] at h
        have h' : ∃ p1'' p2'' t2, p2'' = 0 ∧ t2 = t ⊕ t' ∧ RefineF r12 (Refine' r12) p1'' p2'' t1 t2 :=
          ⟨0, ⟨0, ⟨t ⊕ t', And.intro rfl (And.intro rfl (by apply RefineF.idx_irrelevance; assumption))⟩⟩⟩
        clear h
        have ⟨p1'', ⟨p2'', ⟨t2, ⟨eq_idx, ⟨eq_choice, h⟩⟩⟩⟩⟩ := h'
        clear h'
        revert eq_idx eq_choice
        induction h with
        | coind p1'' p2'' h1' h2' h =>
          intro eq_idx eq_choice; subst eq_idx eq_choice
          apply not_lt_bot at h2'; cases h2'
        | ret h =>
          intro eq_idx eq_choice
          ctree_elim eq_choice
        | vis h =>
          intro eq_idx eq_choice
          ctree_elim eq_choice
        | tau_left h ih =>
          intro eq_idx eq_vis; subst eq_idx eq_vis
          apply RefineF.tau_left
          apply RefineF.idx_mono (p1' := p11) <;>
          first | apply le_top | apply le_refl | apply ih rfl rfl
        | tau_right h =>
          intro _ eq_vis; ctree_elim eq_vis
        | zero => intros; apply RefineF.zero
        | choice_left h =>
          intro eq_idx eq_choice; subst eq_idx
          apply choice_inj at eq_choice
          have ⟨eq1, eq2⟩ := eq_choice
          subst eq1 eq2; clear eq_choice
          apply h1_ih
          rw [Refine']
          apply RefineF.idx_irrelevance; assumption
        | choice_right h =>
          intro eq_idx eq_choice; subst eq_idx
          apply choice_inj at eq_choice
          have ⟨eq1, eq2⟩ := eq_choice
          subst eq1 eq2; clear eq_choice
          apply h2_ih
          rw [Refine']
          apply RefineF.idx_irrelevance; assumption
        | choice_idemp h1 h2 =>
          intro eq_idx eq_choice; subst eq_idx eq_choice
          rename_i h1_ih h2_ih
          apply RefineF.choice_idemp <;>
          apply RefineF.idx_mono (p1' := p11) <;>
          first | apply le_top | apply le_refl | apply h1_ih rfl rfl | apply h2_ih rfl rfl
    | ret h =>
      intros; rename_i h
      rw [Refine'] at h
      apply RefineF.monotone (sim := Refine' (r12.comp r23))
      · intros; rename_i h; apply Or.intro_left; assumption
      · rw [← Refine']; apply Refine'.inv_ret_left
        · rw [Refine'] <;> (try apply RefineF.idx_irrelevance) <;> assumption
        · rename_i x y _ _ _ _ _ _; intros; exists y
    | vis h =>
      rename_i p1 p2 α e k1 k2
      intro p22 t3 p21 h'
      rw [Refine'] at h'
      apply RefineF.idx_irrelevance (p1' := p1) (p2' := p22) at h'
      generalize eq_vis : vis e k2 = t2' at h'
      clear p21; revert p1
      intro p1 h'
      induction h' with
      | coind p1'' p2'' h1' h2' h =>
        subst eq_vis
        apply RefineF.coind <;> try assumption
        apply Or.intro_right; exists p2'', p1'', vis e k2
        apply And.intro _ (by assumption)
        rw [Refine']; apply RefineF.vis; assumption
      | ret h => ctree_elim eq_vis
      | vis hk =>
        rename_i cont _ _ α' e' k1' k2' h_ih'
        have eq_α := vis_inj_α eq_vis
        subst eq_α
        have ⟨eq1, eq2⟩ := vis_inj eq_vis
        clear eq_vis
        subst eq1 eq2
        apply RefineF.vis (p1' := ⊤) (p2' := ⊤); intro a
        right
        rename_i p11 p12 p21 _
        exists p12, cont, k2 a
        simp only [Refine'] at *
        apply And.intro
        · apply RefineF.idx_mono le_top (le_refl _)
          exact h a
        · apply RefineF.idx_mono (le_refl _) le_top
          exact hk a
      | tau_left h ih => ctree_elim eq_vis
      | tau_right h =>
        rename_i h_ih
        subst eq_vis
        apply RefineF.tau_right
        apply h_ih rfl
      | zero => ctree_elim eq_vis
      | choice_left h =>
        rename_i h_ih
        subst eq_vis
        apply RefineF.choice_left
        apply h_ih rfl
      | choice_right h =>
        rename_i h_ih
        subst eq_vis
        apply RefineF.choice_right
        apply h_ih rfl
      | choice_idemp h1 h2 => ctree_elim eq_vis
    | tau_left h ih =>
      intros; apply RefineF.tau_left; apply ih; assumption
    | tau_right h =>
      rename_i h_ih
      intros; rename_i h'
      apply Refine'.inv_tau_left at h'
      apply h_ih; assumption
    | zero => intros; apply RefineF.zero
    | choice_left h =>
      rename_i h_ih
      intros; rename_i h'
      apply Refine'.inv_choice_left_left at h'
      apply h_ih; assumption
    | choice_right h =>
      rename_i h_ih
      intros; rename_i h'
      apply Refine'.inv_choice_left_right at h'
      apply h_ih; assumption
    | choice_idemp h1 h2 =>
      rename_i h1_ih h2_ih
      intros
      apply RefineF.choice_idemp <;>
      apply RefineF.idx_mono (p1' := ⊤) <;>
      try (first | apply le_top | apply le_refl | apply h1_ih | apply h2_ih) <;>
      assumption

  theorem Refine.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop) (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2)
      (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : t1 ≤r≤ t2 :=
      ⟨p1, ⟨p2, Refine'.fixpoint_induct r sim adm p1 p2 t1 t2 h⟩⟩

  @[refl]
  theorem Refine.refl {r : Rel ρ ρ} [IsRefl ρ r] (t : CTree ε ρ) : t ≤r≤ t := by
    apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ t1 = t2) _ 0 0 (And.intro rfl <| And.intro rfl rfl)
    intro p1 p2 t t' h
    obtain ⟨hp1, hp2, heq⟩ := h
    subst hp1
    subst hp2
    subst heq
    apply dMatchOn t
    · intro v heq
      subst heq
      apply RefineF.ret
      exact IsRefl.refl v
    · intro c heq
      subst heq
      apply RefineF.tau_left
      apply RefineF.tau_right
      apply RefineF.coind 0 0
      <;> simp_all only [ENat.top_pos]
      simp_all only [and_self]
    · intro α e k heq
      subst heq
      apply RefineF.vis (p1' := 0) (p2' := 0)
      intro a
      simp_all only [and_self]
    · intro heq
      subst heq
      exact RefineF.zero
    · intro c1 c2 heq
      subst heq
      apply RefineF.choice_idemp
      · apply RefineF.choice_left
        apply RefineF.coind 0 0
        <;> simp_all only [ENat.top_pos]
        simp_all only [and_self]
      · apply RefineF.choice_right
        apply RefineF.coind 0 0
        <;> simp_all only [ENat.top_pos]
        simp_all only [and_self]

  @[trans]
  theorem Refine.trans {t1 : CTree ε α} {t2 : CTree ε β} {t3 : CTree ε γ}
    (h1 : t1 ≤r1≤ t2) (h2 : t2 ≤r2≤ t3) : t1 ≤r1.comp r2≤ t3 := by
    obtain ⟨_, _, h1⟩ := h1
    obtain ⟨_, _, h2⟩ := h2
    have := Refine'.trans h1 h2
    rename_i p1 _ _ p2
    exists p1, p2

  instance : LE (CTree ε ρ) where
    le := Refine Eq

  instance : Preorder (CTree ε ρ) where
    le_refl := Refine.refl
    le_trans := by
      intro t1 t2 t3 h1 h2
      have h3 := Refine.trans h1 h2
      rw [Rel.comp_right_id] at h3
      exact h3

  instance : Bot (CTree ε ρ) where
    bot := zero

  theorem Refine.zero_le : zero ≤ t := by
    simp only [LE.le, Refine, Refine']
    exists 0, 0
    exact RefineF.zero

  instance : OrderBot (CTree ε ρ) where
    bot_le _ := Refine.zero_le

  namespace Refine
    theorem choice_idemp (h1 : t1 ≤r≤ t3) (h2 : t2 ≤r≤ t3) : (t1 ⊕ t2) ≤r≤ t3 := by
      obtain ⟨_, _, h1⟩ := h1
      obtain ⟨_, _, h2⟩ := h2
      exists 0, 0
      simp only [Refine'] at *
      exact RefineF.choice_idemp (h1.idx_irrelevance _ _) (h2.idx_irrelevance _ _)

    theorem choice_left (h : t1 ≤r≤ t2) : t1 ≤r≤ (t2 ⊕ t3) := by
      obtain ⟨_, _, h⟩ := h
      exists 0, 0
      simp only [Refine'] at *
      exact RefineF.choice_left (h.idx_irrelevance _ _)

    theorem choice_right (h : t1 ≤r≤ t3) : t1 ≤r≤ (t2 ⊕ t3) := by
      obtain ⟨_, _, h⟩ := h
      exists 0, 0
      simp only [Refine'] at *
      exact RefineF.choice_right (h.idx_irrelevance _ _)

    lemma dest_tau_right_adm (h : RefineF r (Refine' r) p1 p2 t1 t2)
      : RefineF r (λ p1 p2 t1 t2 => Refine' r p1 p2 t1 t2.tau) p1 p2 t1 t2 := by
      induction h with
      | coind =>
        apply RefineF.coind <;> try assumption
        rw [Refine'] at *
        apply RefineF.tau_right
        apply RefineF.idx_irrelevance; assumption
      | ret h => exact RefineF.ret h
      | vis h =>
        rename_i p1 p2 _ _ _ _ _ _
        apply RefineF.vis (p1' := p1) (p2' := p2)
        intro a
        simp_all only [Refine']
        apply RefineF.tau_right
        apply RefineF.idx_mono (le_refl _) le_top
        exact h a
      | tau_left _ ih => exact RefineF.tau_left ih
      | tau_right _ ih => exact RefineF.tau_right ih
      | zero => exact RefineF.zero
      | choice_left _ ih => exact RefineF.choice_left ih
      | choice_right _ ih => exact RefineF.choice_right ih
      | choice_idemp _ _ ih1 ih2 => exact RefineF.choice_idemp ih1 ih2

    theorem dest_tau_right (h : t1 ≤r≤ t2.tau) : t1 ≤r≤ t2 := by
      obtain ⟨p1, p2, h⟩ := h
      apply Refine.coind (λ p1 p2 t1 t2 => Refine' r p1 p2 t1 t2.tau) _ p1 p2 h
      intro p1 p2 t1 t2 h
      simp only [Refine'] at h
      generalize ht2 : t2.tau = t2t at *
      induction h
      <;> ctree_elim ht2
      case coind =>
        subst ht2
        apply RefineF.coind <;> assumption
      case tau_left ih => exact RefineF.tau_left (ih ht2)
      case tau_right h _ =>
        rw [tau_inj ht2]
        exact dest_tau_right_adm (h.idx_irrelevance _ _)
      case zero => exact RefineF.zero
      case choice_idemp ih1 ih2 => exact RefineF.choice_idemp (ih1 ht2) (ih2 ht2)

    lemma dest_tau_left_adm (h : RefineF r (Refine' r) p1 p2 t1 t2)
      : RefineF r (λ p1 p2 t1 t2 => Refine' r p1 p2 t1.tau t2) p1 p2 t1 t2 := by
      induction h with
      | coind =>
        apply RefineF.coind <;> try assumption
        rw [Refine'] at *
        apply RefineF.tau_left
        apply RefineF.idx_irrelevance; assumption
      | ret h => exact RefineF.ret h
      | vis h =>
        rename_i p1 p2 _ _ _ _ _ _
        apply RefineF.vis (p1' := p1) (p2' := p2)
        intro a
        simp_all only [Refine']
        apply RefineF.tau_left
        apply RefineF.idx_mono le_top (le_refl _)
        exact h a
      | tau_left _ ih => exact RefineF.tau_left ih
      | tau_right _ ih => exact RefineF.tau_right ih
      | zero => exact RefineF.zero
      | choice_left _ ih => exact RefineF.choice_left ih
      | choice_right _ ih => exact RefineF.choice_right ih
      | choice_idemp _ _ ih1 ih2 => exact RefineF.choice_idemp ih1 ih2

    theorem dest_tau_left (h : t1.tau ≤r≤ t2) : t1 ≤r≤ t2 := by
      obtain ⟨p1, p2, h⟩ := h
      apply Refine.coind (λ p1 p2 t1 t2 => Refine' r p1 p2 t1.tau t2) _ p1 p2 h
      intro p1 p2 t1 t2 h
      simp only [Refine'] at h
      generalize ht1 : t1.tau = t1t at *
      induction h
      <;> ctree_elim ht1
      case coind =>
        subst ht1
        apply RefineF.coind <;> assumption
      case tau_left h _ =>
        rw [tau_inj ht1]
        exact dest_tau_left_adm (h.idx_irrelevance _ _)
      case tau_right ih => exact RefineF.tau_right (ih ht1)
      case choice_left ih => exact RefineF.choice_left (ih ht1)
      case choice_right ih => exact RefineF.choice_right (ih ht1)

    theorem dest_tauN_left (h : tauN n t1 ≤r≤ t2) : t1 ≤r≤ t2 := by
      induction n with
      | zero => simp only [tauN] at h; exact h
      | succ n ih => simp only [tauN] at h; exact ih h.dest_tau_left

    theorem dest_tauN_right (h : t1 ≤r≤ tauN n t2) : t1 ≤r≤ t2 := by
      induction n with
      | zero => simp only [tauN] at h; exact h
      | succ n ih => simp only [tauN] at h; exact ih h.dest_tau_right

    theorem dest_tau_both (h : t1.tau ≤r≤ t2.tau) : t1 ≤r≤ t2 :=
      h.dest_tau_left.dest_tau_right

    -- theorem dest_choice_left (h : t1 ⊕ t2 ≤r≤ t3) : := sorry

    lemma map_tauN : map f (tauN n t) = tauN n (map f t) := by
      induction n with
      | zero => simp only [tauN, map_tau]
      | succ => simp only [tauN, map_tau]; congr

    theorem congr_map {t1 t2 : CTree ε ρ} {f : ρ → σ} (h : t1 ≤ t2) : t1.map f ≤ t2.map f := by
      obtain ⟨p1, p2, h⟩ := h
      apply Refine.coind (λ p1 p2 ft1 ft2 => ∃ t1 t2, ft1 = t1.map f ∧ ft2 = t2.map f ∧ Refine' Eq p1 p2 t1 t2) _ p1 p2
      · exists t1, t2
      · intro p1 p2 ft1 ft2 h
        obtain ⟨t1, t2, hft1, hft2, h⟩ := h
        revert ft1 ft2
        simp_all only [Refine']
        induction h with
        | coind p1' p2' h1 h2 h =>
          rename_i t1 t2
          intros
          apply RefineF.coind p1' p2' h1 h2
          exists t1, t2
          repeat apply And.intro; rfl
          rw [Refine'] at h
          exact h
        | ret hxy =>
          intros; simp only [map_ret]; apply RefineF.ret; congr
        | vis hk =>
          rename_i p1 p2 _ _ _ k1 k2
          intros
          simp only [map_vis]
          apply RefineF.vis (p1' := p1) (p2' := p2)
          intro a
          exists k1 a, k2 a
          repeat apply And.intro; rfl
          have := hk a
          simp_all only [Refine']
          exact (hk a).idx_irrelevance _ _
        | tau_left h ih =>
          intros
          simp only [map_tau]
          apply RefineF.tau_left
          exact ih _ _ rfl rfl
        | tau_right h ih =>
          intros
          simp only [map_tau]
          apply RefineF.tau_right
          exact ih _ _ rfl rfl
        | zero =>
          intros; simp only [map_zero]; exact RefineF.zero
        | choice_left h ih =>
          intros
          simp only [map_choice]
          apply RefineF.choice_left
          exact ih _ _ rfl rfl
        | choice_right h ih =>
          intros
          simp only [map_choice]
          apply RefineF.choice_right
          exact ih _ _ rfl rfl
        | choice_idemp h1 h2 ih1 ih2 =>
          intros
          simp only [map_choice]
          apply RefineF.choice_idemp
          · exact ih1 _ _ rfl rfl
          · exact ih2 _ _ rfl rfl

    theorem vis (h : ∀ a, k1 a ≤r≤ k2 a) : (.vis e k1) ≤r≤ (.vis e k2) := by
      rw [Refine]
      exists 0, 0
      rw [Refine']
      apply RefineF.vis (p1' := 0) (p2' := 0)
      intro a
      have ⟨p1, p2, h⟩ := h a
      simp_all only [Refine']
      exact RefineF.idx_irrelevance h _ _

  end Refine

  inductive IsInfF (sim : CTree ε ρ → Prop) : CTree ε ρ → Prop
  | choice_left (h : sim t1) : IsInfF sim (t1 ⊕ t2)
  | choice_right (h : sim t2) : IsInfF sim (t1 ⊕ t2)
  | tau (h : sim t) : IsInfF sim t.tau

  def IsInf (t : CTree ε ρ) : Prop :=
    IsInfF IsInf t
    greatest_fixpoint monotonicity by
      intro sim1 sim2 hsim x h
      cases h with
      | choice_left h => exact .choice_left (hsim _ h)
      | choice_right h => exact .choice_right (hsim _ h)
      | tau h => exact .tau (hsim _ h)

  theorem infND_refine_left : infND ≤r≤ t → IsInf t := by
    intro h
    apply IsInf.fixpoint_induct (λ t => infND ≤r≤ t) _ t h
    intro t h
    rw [Refine] at h
    obtain ⟨p1, p2, h⟩ := h
    revert p1
    induction p2 using WellFoundedLT.induction
    rename_i p2 ihp2
    intro p2 h
    rw [Refine'] at h
    rw [infND_eq] at h
    generalize hinf : infND ⊕ infND = t at *
    induction h
    <;> ctree_elim hinf
    case coind _ p2 _ h2 h =>
      rw [←hinf, ←infND_eq] at h
      exact ihp2 p2 h2 _ h
    case tau_right h _ =>
      apply IsInfF.tau
      subst hinf
      rw [←infND_eq] at h
      rename_i p1 _ _ _
      exists p1, ⊤
      rw [Refine']
      assumption
    case choice_left h _ =>
      rename_i p1 _ _ _ _ _
      apply IsInfF.choice_left
      rw [←hinf, ←infND_eq] at h
      rw [Refine]
      exists p1, ⊤
      rw [Refine']
      assumption
    case choice_right h _ =>
      rename_i p1 _ _ _ _ _
      apply IsInfF.choice_right
      rw [←hinf, ←infND_eq] at h
      rw [Refine]
      exists p1, ⊤
      rw [Refine']
      assumption
    case choice_idemp h1 h2 ih1 ih2 =>
      apply ih2 ihp2
      rw [←(choice_inj hinf).right]
      simp only [←infND_eq]

  theorem Refine'.tau_left (h : Refine' r p1 p2 t1 t2) : Refine' r p1 p2 t1.tau t2 := by
    rw [Refine'] at *
    exact RefineF.idx_irrelevance (RefineF.tau_left (RefineF.idx_irrelevance h ⊤ ⊤) (p1 := p1)) p1 p2

  theorem Refine'.tau_right (h : Refine' r p1 p2 t1 t2) : Refine' r p1 p2 t1 t2.tau := by
    rw [Refine'] at *
    exact RefineF.idx_irrelevance (RefineF.tau_right (RefineF.idx_irrelevance h ⊤ ⊤) (p2 := p2)) p1 p2

  theorem Refine'.choice_left (h : Refine' r p1 p2 t1 t2) : Refine' r p1 p2 t1 (t2 ⊕ t3) := by
    have ⟨_, _, h⟩ := Refine.choice_left ⟨p1, p2, h⟩ (t3 := t3)
    rw [Refine'] at *
    exact RefineF.idx_irrelevance h p1 p2

  theorem Refine'.choice_right (h : Refine' r p1 p2 t1 t3) : Refine' r p1 p2 t1 (t2 ⊕ t3) := by
    have ⟨_, _, h⟩ := Refine.choice_right ⟨p1, p2, h⟩ (t2 := t2)
    rw [Refine'] at *
    exact RefineF.idx_irrelevance h p1 p2

  theorem Refine'.vis_trans [IsRefl _ r] [IsTrans _ r]
    (hk : ∀ a, Refine' r p1 p2 (k1 a) (k2 a)) (h : Refine' r p1 p2 (vis e k2) t)
    : Refine' r p1 p2 (vis e k1) t := by
    have : Refine' r p1 p2 (vis e k1) (vis e k2) := by
      simp only [Refine'] at *
      apply RefineF.vis
      intro a
      simp only [Refine'] at *
      exact RefineF.idx_irrelevance (hk a) ⊤ ⊤
    have := Refine'.trans this h
    rw [Rel.comp_self] at this
    exact this

  inductive ContainsVis {α : Type} (e : ε α) (k : α → CTree ε ρ) : CTree ε ρ → Prop
  | vis : ContainsVis e k (vis e k)
  | tau {t} : ContainsVis e k t → ContainsVis e k t.tau
  | choice_left {t1 t2} : ContainsVis e k t1 → ContainsVis e k (t1 ⊕ t2)
  | choice_right {t1 t2} : ContainsVis e k t2 → ContainsVis e k (t1 ⊕ t2)

  theorem Refine'.of_ContainsVis {t : CTree ε ρ} [IsRefl ρ r] (h : ContainsVis e k t) : Refine' r p1 p2 (vis e k) t := by
    induction h with
    | vis =>
      have ⟨_, _, h⟩ := Refine.refl (r := r) (vis e k)
      rw [Refine'] at *
      exact RefineF.idx_irrelevance h p1 p2
    | tau _ ih => exact Refine'.tau_right ih
    | choice_left _ ih => exact Refine'.choice_left ih
    | choice_right _ ih => exact Refine'.choice_right ih

  theorem Refine'.inv_vis_left
    (h : Refine' r p1 p2 (vis e k1) t2)
    : ∃ k2, ContainsVis e k2 t2 ∧ ∀ a, Refine' r p1 p2 (k1 a) (k2 a) := by
    simp only [Refine'] at *
    generalize ht1 : vis e k1 = t1 at *
    revert p2 t1 t2
    induction p1 using WellFounded.induction ENat.instWellFoundedLT.wf
    rename_i p1 ih_p1
    intro p2 t1 t2 ht2 h
    induction h
    <;> ctree_elim ht2
    case coind p1' p2' hp1 hp2 h =>
      simp only [Refine'] at *
      obtain ⟨k2, hcont, href⟩ := ih_p1 p1' hp1 _ ht2 (h.idx_irrelevance _ _) (p2 := p2)
      exists k2
      apply And.intro hcont
      intro a
      exact (href a).idx_irrelevance _ _
    case vis h =>
      subst_vis_inj ht2
      rename_i k2
      exists k2
      apply And.intro .vis
      intro a
      simp_all only [Refine']
      exact (h a).idx_irrelevance _ _
    case tau_right h ih =>
      have ⟨k2, hcont, href⟩ := ih ih_p1 ht2
      exists k2
      exact And.intro (.tau hcont) (λ a => (href a).idx_irrelevance _ _)
    case choice_left h ih =>
      have ⟨k2, hcont, href⟩ := ih ih_p1 ht2
      exists k2
      exact And.intro (.choice_left hcont) (λ a => (href a).idx_irrelevance _ _)
    case choice_right h ih =>
      have ⟨k2, hcont, href⟩ := ih ih_p1 ht2
      exists k2
      exact And.intro (.choice_right hcont) (λ a => (href a).idx_irrelevance _ _)

  inductive ContainsRet (v : ρ) : CTree ε ρ → Prop
  | ret : ContainsRet v (ret v)
  | tau {t} : ContainsRet v t → ContainsRet v t.tau
  | choice_left {t1 t2} : ContainsRet v t1 → ContainsRet v (t1 ⊕ t2)
  | choice_right {t1 t2} : ContainsRet v t2 → ContainsRet v (t1 ⊕ t2)

  theorem Refine'.dest_ret_left
    (h : Refine' Eq p1 p2 (ret v) t2) : ContainsRet v t2 := by
    simp only [Refine'] at *
    generalize ht1 : ret v = t1 at *
    revert p2 t1 t2
    induction p1 using WellFounded.induction ENat.instWellFoundedLT.wf
    rename_i p1 ih_p1
    intro p2 t1 t2 ht2 h
    induction h
    <;> ctree_elim ht2
    case coind p1' p2' hp1 hp2 h =>
      simp only [Refine'] at *
      exact ih_p1 p1' hp1 _ ht2 (h.idx_irrelevance _ _) (p2 := p2)
    case ret h =>
      rw [←h, ret_inj ht2]
      exact .ret
    case tau_right h ih =>
      exact .tau <| ih ih_p1 ht2
    case choice_left h ih =>
      exact .choice_left <| ih ih_p1 ht2
    case choice_right h ih =>
      exact .choice_right <| ih ih_p1 ht2

end CTree
