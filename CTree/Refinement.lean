import CTree.Basic
import CTree.Monad
import Mathlib.Data.ENat.Basic
import CTree.Paco

namespace CTree
  /--
    The definition uses ideas from the [FreeSim paper](https://dl.acm.org/doi/10.1145/3622857)

    Note that this is not equivalent to `TraceRefine`, becasuse `TraceRefine` makes no distinction between `zero` and `infND`.
  -/
  inductive RefineF {ε : Type u → Type v} {ρ : Type w1} {σ : Type w2}
    (r : Rel ρ σ) (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    : ENat → ENat → CTree ε ρ → CTree ε σ → Prop
  | coind {p1 p2 t1 t2} (p1' p2' : ENat)
      (h1 : p1' < p1) (h2 : p2' < p2) (h : sim p1' p2' t1 t2)
      : RefineF r sim p1 p2 t1 t2
  | ret {x y p1 p2} (h : r x y) : RefineF r sim p1 p2 (ret x) (ret y)
  | vis {p1' p2' p1 p2} {α} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
      (h : ∀ a : α, sim p1' p2' (k1 a) (k2 a)) : RefineF r sim p1 p2 (vis e k1) (vis e k2)
  | tau_left {p1 p1' p2 t1 t2}
      (h : RefineF r sim p1' p2 t1 t2) : RefineF r sim p1 p2 t1.tau t2
  | tau_right {p1 p2 p2' t1 t2}
      (h : RefineF r sim p1 p2' t1 t2) : RefineF r sim p1 p2 t1 t2.tau
  | zero {p1 p2} {t : CTree ε σ} : RefineF r sim p1 p2 zero t
  | choice_left {p1 p2 p2' t1 t2 t3}
      (h : RefineF r sim p1 p2' t1 t2) : RefineF r sim p1 p2 t1 (t2 ⊕ t3)
  | choice_right {p1 p2 p2' t1 t2 t3}
      (h : RefineF r sim p1 p2' t1 t3) : RefineF r sim p1 p2 t1 (t2 ⊕ t3)
  | choice_idemp {p1 p1' p2 t1 t2 t3}
      (h1 : RefineF r sim p1' p2 t1 t3) (h2 : RefineF r sim p1' p2 t2 t3)
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
    coinductive_fixpoint monotonicity by
      intro _ _ hsim _ _ _ _ h
      apply RefineF.monotone (hsim := hsim) (h := h)

  abbrev Refine (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) :=
    ∃ p1 p2, Refine' r p1 p2 t1 t2

  -- `t1 r≤ t2` looks better, but somehow clashes with multi-line class instance definition
  notation:60 t1:61 " ≤"r:61"≤ " t2:61 => Refine r t1 t2

  theorem RefineF.idx_mono {sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop}
    {t1 : CTree ε ρ} {t2 : CTree ε σ}
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
      apply RefineF.choice_right (p2' := ⊤)
      crush_cont_aux $ih, $h_ih
    · intro h
      obtain ⟨_, h⟩ := h
      rw [h]
      apply RefineF.choice_left (p2' := ⊤)
      crush_cont_aux $ih, $h_ih
    · intro h
      rw [h]
      apply RefineF.tau_right (p2' := ⊤)
      crush_cont_aux $ih, $h_ih
  ))

  variable {ε : Type u → Type v} {ρ : Type w1} {σ : Type w2}
  variable {sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop}
  variable {r : Rel ρ σ}

  /--
    If `t1` refines `t2'`, then for any `t2` that may *continue* as `t2'`, `t1` must refine `t2`.

    By *continue* we mean that `t2'` shows up as a choice within `t2` or is a `tau` step behind `t2`.
  -/
  theorem RefineF.cont_right {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
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

  theorem RefineF.idx_irrelevance_gen {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
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
      intros; apply RefineF.tau_left (p1' := ⊤); apply ih; assumption
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
      apply RefineF.choice_idemp (p1' := ⊤)
      · apply ih1; assumption
      · apply ih2; assumption

  theorem RefineF.idx_irrelevance {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    (h : RefineF r (Refine' r) p1 p2 t1 t2)
    : ∀ p1' p2', RefineF r (Refine' r) p1' p2' t1 t2 := by
    apply h.idx_irrelevance_gen; intros; rw [← Refine']; assumption

  theorem Refine'.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2)
    (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : Refine' r p1 p2 t1 t2 :=
    Refine'.coinduct r sim adm p1 p2 t1 t2 h

  theorem RefineF.inv_ret_left {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {r' : Rel ρ' σ} {sim'} {t : CTree ε σ}
    (h : RefineF r sim p1 p2 (.ret x) t)
    : ∀ p1' p2' y, (∀ z, r x z → r' y z) → RefineF r' sim' p1' p2' (.ret y) t := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := 0) (p2' := p2) at h
    clear p1
    generalize eq_p1 : (0 : ℕ∞) = p1 at h
    generalize eq_t1 : CTree.ret x = t1 at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p1
      apply not_lt_bot at h1'
      cases h1'
    | ret h =>
      intros _ _ _ hyz
      apply ret_inj at eq_t1
      subst eq_t1
      apply RefineF.ret; apply hyz; assumption
    | vis h =>
      ctree_elim eq_t1
    | tau_left h ih =>
      ctree_elim eq_t1
    | tau_right h ih =>
      intros
      subst eq_p1 eq_t1
      apply RefineF.tau_right (p2' := ⊤)
      apply ih <;> first | rfl | assumption
    | zero =>
      ctree_elim eq_t1
    | choice_left h ih =>
      intros
      subst eq_p1 eq_t1
      apply RefineF.choice_left (p2' := ⊤)
      apply ih <;> first | rfl | assumption
    | choice_right h ih =>
      intros
      subst eq_p1 eq_t1
      apply RefineF.choice_right (p2' := ⊤)
      apply ih <;> first | rfl | assumption
    | choice_idemp h1 h2 =>
      ctree_elim eq_t1

  theorem RefineF.inv_ret_right {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {sim'} {r' : Rel ρ σ'}
    {p1 p2 x} {t : CTree ε ρ}
    (h : RefineF r sim p1 p2 t (.ret x))
    : ∀ p1' p2' y, (∀ z, r z x → r' z y) → RefineF r' sim' p1' p2' t (.ret y) := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := p1) (p2' := 0) at h
    clear p2
    generalize eq_p2 : (0 : ℕ∞) = p2 at h
    generalize eq_t2 : CTree.ret x = t2 at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p2
      apply not_lt_bot at h2'
      cases h2'
    | ret h =>
      intros _ _ _ hyz
      apply ret_inj at eq_t2
      subst eq_t2
      apply RefineF.ret; apply hyz; assumption
    | vis h =>
      ctree_elim eq_t2
    | tau_left h ih =>
      intros
      subst eq_p2 eq_t2
      apply RefineF.tau_left (p1' := ⊤); apply ih <;> first | rfl | assumption
    | tau_right h =>
      ctree_elim eq_t2
    | zero =>
      intros; exact RefineF.zero
    | choice_left h =>
      ctree_elim eq_t2
    | choice_right h =>
      ctree_elim eq_t2
    | choice_idemp h1 h2 =>
      intros
      subst eq_p2 eq_t2
      rename_i h1_ih h2_ih
      apply RefineF.choice_idemp (p1' := ⊤)
      · apply h1_ih <;> first | rfl | assumption
      · apply h2_ih <;> first | rfl | assumption

  theorem RefineF.inv_vis_left {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {sim' : ℕ∞ → ℕ∞ → CTree ε ρ' → CTree ε ρ → Prop}
    {sim''} {r' : Rel ρ' σ}
    {p1 p2 e k1 k2} {t : CTree ε σ}
    (h : RefineF r sim p1 p2 (.vis e k1) t)
    {p1' p2'}
    (hk : ∀ a : α, sim' p1' p2' (k2 a) (k1 a))
    {hsim' : ∀ p11 p12 t1 t2 p21 p22 t3, sim' p11 p12 t1 t2 → sim p21 p22 t2 t3 → sim'' p11 p22 t1 t3}
    : ∀ p1'' p2'', RefineF r' sim'' p1'' p2'' (.vis e k2) t := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := 0) (p2' := p2) at h
    clear p1
    generalize eq_p1 : (0 : ℕ∞) = p1 at h
    generalize eq_t1 : CTree.vis _ _ = t' at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      subst eq_p1
      apply not_lt_bot at h1'
      cases h1'
    | ret h =>
      ctree_elim eq_t1
    | vis h' =>
      intros
      subst eq_p1
      have := vis_inj_α eq_t1; subst this
      apply vis_inj at eq_t1
      have ⟨h, h'⟩ := eq_t1; subst h h'
      apply RefineF.vis
      intros
      apply hsim' <;> first | apply hk | apply h'
    | tau_left h ih =>
      ctree_elim eq_t1
    | tau_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.tau_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | zero =>
      ctree_elim eq_t1
    | choice_left h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_left (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_idemp h1 h2 =>
      ctree_elim eq_t1

  theorem RefineF.inv_vis_right {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {sim' : ℕ∞ → ℕ∞ → CTree ε σ → CTree ε σ' → Prop}
    {sim''} {r' : Rel ρ σ'}
    {p1 p2 e k1 k2} {t : CTree ε ρ}
    (h : RefineF r sim p1 p2 t (.vis e k1))
    {p1' p2'}
    (hk : ∀ a : α, sim' p1' p2' (k1 a) (k2 a))
    {hsim' : ∀ p11 p12 t1 t2 p21 p22 t3, sim p11 p12 t1 t2 → sim' p21 p22 t2 t3 → sim'' p11 p22 t1 t3}
    : ∀ p1'' p2'', RefineF r' sim'' p1'' p2'' t (.vis e k2) := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := p1) (p2' := 0) at h
    clear p2
    generalize eq_p2 : (0 : ℕ∞) = p2 at h
    generalize eq_t2 : CTree.vis _ _ = t' at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      subst eq_p2
      apply not_lt_bot at h2'
      cases h2'
    | ret h =>
      ctree_elim eq_t2
    | vis h' =>
      intros
      subst eq_p2
      have := vis_inj_α eq_t2; subst this
      apply vis_inj at eq_t2
      have ⟨h, h'⟩ := eq_t2; subst h h'
      apply RefineF.vis
      intros
      apply hsim' <;> first | apply hk | apply h'
    | tau_left h ih =>
      intros
      subst eq_p2 eq_t2
      apply RefineF.tau_left (p1' := ⊤); apply ih <;> rfl
    | tau_right h =>
      ctree_elim eq_t2
    | zero =>
      intros; apply RefineF.zero
    | choice_left h =>
      ctree_elim eq_t2
    | choice_right h =>
      ctree_elim eq_t2
    | choice_idemp h1 h2 ih1 ih2 =>
      intros
      subst eq_p2 eq_t2
      apply RefineF.choice_idemp (p1' := ⊤)
      · apply ih1 <;> rfl
      · apply ih2 <;> rfl

  theorem RefineF.inv_tau_left {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {p1 p2 t'} {t : CTree ε σ}
    (h : RefineF r sim p1 p2 (.tau t') t) : ∀ p1' p2', RefineF r sim p1' p2' t' t := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := 0) (p2' := p2) at h
    clear p1
    generalize eq_p1 : (0 : ℕ∞) = p1 at h
    generalize eq_t1 : tau t' = t1 at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p1
      apply not_lt_bot at h1'
      cases h1'
    | ret h =>
      ctree_elim eq_t1
    | vis h =>
      ctree_elim eq_t1
    | tau_left h ih =>
      intros
      apply tau_inj at eq_t1
      subst eq_t1
      apply RefineF.idx_irrelevance_gen <;> assumption
    | tau_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.tau_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | zero =>
      ctree_elim eq_t1
    | choice_left h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_left (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_idemp h1 h2 =>
      ctree_elim eq_t1

  theorem Refine'.inv_tau_left {p1 p2 t'} {t : CTree ε σ}
    (h : Refine' r p1 p2 (.tau t') t) : Refine' r p1 p2 t' t := by
    rw [Refine'] at *; apply RefineF.inv_tau_left <;> try assumption
    intros; rename_i h; rw [Refine'] at h; assumption

  theorem RefineF.inv_tau_right {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {p1 p2 t'} {t : CTree ε ρ}
    (h : RefineF r sim p1 p2 t (.tau t')) : ∀ p1' p2', RefineF r sim p1' p2' t t' := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := p1) (p2' := 0) at h
    clear p2
    generalize eq_p2 : (0 : ℕ∞) = p2 at h
    generalize eq_t2 : tau t' = t2 at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p2
      apply not_lt_bot at h2'
      cases h2'
    | ret h =>
      ctree_elim eq_t2
    | vis h =>
      ctree_elim eq_t2
    | tau_left h ih =>
      intros
      subst eq_p2 eq_t2
      apply RefineF.tau_left (p1' := ⊤); apply ih <;> rfl
    | tau_right h =>
      intros
      apply tau_inj at eq_t2
      subst eq_p2 eq_t2
      apply RefineF.idx_irrelevance_gen <;> first | assumption
    | zero =>
      intros; exact RefineF.zero
    | choice_left h =>
      ctree_elim eq_t2
    | choice_right h =>
      ctree_elim eq_t2
    | choice_idemp h1 h2 =>
      intros
      subst eq_p2 eq_t2
      rename_i h1_ih h2_ih
      apply RefineF.choice_idemp (p1' := ⊤)
      · apply h1_ih <;> rfl
      · apply h2_ih <;> rfl

  theorem RefineF.inv_zero_right {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {sim'} {r' : Rel ρ σ'} {p1 p2} {t1 : CTree ε ρ}
    (h : RefineF r sim p1 p2 t1 .zero) : ∀ p1' p2' t2, RefineF r' sim' p1' p2' t1 t2 := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := p1) (p2' := 0) at h
    clear p2
    generalize eq_p2 : (0 : ℕ∞) = p2 at h
    generalize eq_t2 : CTree.zero = t2 at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p2
      apply not_lt_bot at h2'
      cases h2'
    | ret h =>
      ctree_elim eq_t2
    | vis h =>
      ctree_elim eq_t2
    | tau_left h ih =>
      intros
      subst eq_p2 eq_t2
      apply RefineF.tau_left (p1' := ⊤); apply ih <;> rfl
    | tau_right h =>
      ctree_elim eq_t2
    | zero =>
      intros; exact RefineF.zero
    | choice_left h =>
      ctree_elim eq_t2
    | choice_right h =>
      ctree_elim eq_t2
    | choice_idemp h1 h2 =>
      intros
      subst eq_p2 eq_t2
      rename_i h1_ih h2_ih
      apply RefineF.choice_idemp (p1' := ⊤)
      · apply h1_ih <;> rfl
      · apply h2_ih <;> rfl

  theorem RefineF.inv_choice_left_left {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {p1 p2} {t : CTree ε σ}
    (h : RefineF r sim p1 p2 (t1 ⊕ t2) t) : ∀ p1' p2', RefineF r sim p1' p2' t1 t := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := 0) (p2' := p2) at h
    clear p1
    generalize eq_p1 : (0 : ℕ∞) = p1 at h
    generalize eq_t1 : t1 ⊕ t2 = t' at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p1
      apply not_lt_bot at h1'
      cases h1'
    | ret h =>
      ctree_elim eq_t1
    | vis h =>
      ctree_elim eq_t1
    | tau_left h ih =>
      ctree_elim eq_t1
    | tau_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.tau_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | zero =>
      ctree_elim eq_t1
    | choice_left h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_left (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_idemp h1 h2 =>
      intros
      apply choice_inj at eq_t1
      have ⟨eq_t1, eq_t1'⟩ := eq_t1
      subst eq_t1 eq_t1'
      apply RefineF.idx_irrelevance_gen <;> assumption

  theorem Refine'.inv_choice_left_left {p1 p2} {t : CTree ε σ}
    (h : Refine' r p1 p2 (t1 ⊕ t2) t) : Refine' r p1 p2 t1 t := by
    rw [Refine'] at *; apply RefineF.inv_choice_left_left <;> try assumption
    intros; rename_i h; rw [Refine'] at h; assumption

  theorem RefineF.inv_choice_left_right {hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2}
    {p1 p2} {t : CTree ε σ}
    (h : RefineF r sim p1 p2 (t1 ⊕ t2) t) : ∀ p1' p2', RefineF r sim p1' p2' t2 t := by
    apply RefineF.idx_irrelevance_gen (hsim := hsim) (p1' := 0) (p2' := p2) at h
    clear p1
    generalize eq_p1 : (0 : ℕ∞) = p1 at h
    generalize eq_t1 : t1 ⊕ t2 = t' at h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intros
      subst eq_p1
      apply not_lt_bot at h1'
      cases h1'
    | ret h =>
      ctree_elim eq_t1
    | vis h =>
      ctree_elim eq_t1
    | tau_left h ih =>
      ctree_elim eq_t1
    | tau_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.tau_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | zero =>
      ctree_elim eq_t1
    | choice_left h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_left (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_right h =>
      intros
      subst eq_t1 eq_p1
      apply RefineF.choice_right (p2' := ⊤)
      rename_i h_ih
      apply h_ih <;> first | assumption | rfl
    | choice_idemp h1 h2 =>
      intros
      apply choice_inj at eq_t1
      have ⟨eq_t1, eq_t1'⟩ := eq_t1
      subst eq_t1 eq_t1'
      apply RefineF.idx_irrelevance_gen <;> assumption

  theorem Refine'.inv_choice_left_right {p1 p2} {t : CTree ε σ}
    (h : Refine' r p1 p2 (t1 ⊕ t2) t) : Refine' r p1 p2 t2 t := by
    rw [Refine'] at *; apply RefineF.inv_choice_left_right <;> try assumption
    intros; rename_i h; rw [Refine'] at h; assumption

  theorem RefineF.trans {r12 : Rel ρ1 ρ2} {r23 : Rel ρ2 ρ3}
    {sim12 sim23}
    {hsim12 : ∀ p1 p2 t1 t2, sim12 p1 p2 t1 t2 → RefineF (ε := ε) r12 sim12 p1 p2 t1 t2}
    {hsim23 : ∀ p1 p2 t1 t2, sim23 p1 p2 t1 t2 → RefineF (ε := ε) r23 sim23 p1 p2 t1 t2}
    {p11 p12 t1 t2} (h : RefineF r12 sim12 p11 p12 t1 t2)
    : ∀ {p21 p22 t3},
      RefineF r23 sim23 p21 p22 t2 t3 →
      RefineF (r12.comp r23) (λ p11 p22 t1 t3 => ∃ p12, ∃ t2, ∃ p21, sim12 p11 p12 t1 t2 ∧ RefineF r23 sim23 p21 p22 t2 t3) p11 p22 t1 t3 := by
    intros p21 p22 t3 h2
    revert p11 p12 t1
    induction h2 with
    | coind p1'' p2'' h1' h2' h =>
      intro p11 p12 t1 h1
      apply hsim23 at h
      revert t2 h
      induction h1 with
      | coind p1'' p2'' h1' h2' h =>
        intros; apply RefineF.coind <;> try assumption
        rename_i h'
        exact ⟨_, ⟨_, ⟨_, ⟨h, h'⟩⟩⟩⟩
      | ret h =>
        intros; apply RefineF.inv_ret_left <;> try assumption
        simp only [Rel.comp]
        intros _ h'
        exact ⟨_, ⟨h, h'⟩⟩
      | vis h =>
        intros; apply RefineF.inv_vis_left <;> try assumption
        intros; rename_i h12 h23
        exact ⟨_, ⟨_, ⟨_, ⟨h12, hsim23 _ _ _ _ h23⟩⟩⟩⟩
      | tau_left h ih =>
        intros
        apply RefineF.tau_left <;> (apply ih <;> assumption)
      | tau_right h ih =>
        intros
        apply ih <;> first | assumption | apply RefineF.inv_tau_left <;> assumption
      | zero =>
        intros; apply RefineF.zero
      | choice_left h ih =>
        intros
        apply ih <;> first | assumption | apply RefineF.inv_choice_left_left <;> assumption
      | choice_right h ih =>
        intros
        apply ih <;> first | assumption | apply RefineF.inv_choice_left_right <;> assumption
      | choice_idemp h1 h2 ih1 ih2 =>
        intros
        apply RefineF.choice_idemp <;> first | apply ih1 <;> assumption | apply ih2 <;> assumption
    | ret h =>
      intros; apply RefineF.inv_ret_right <;> try assumption
      simp only [Rel.comp]
      intros _ h'
      exact ⟨_, ⟨h', h⟩⟩
    | vis h =>
      intros; apply RefineF.inv_vis_right <;> try assumption
      intros; rename_i h12 h23
      exact ⟨_, ⟨_, ⟨_, ⟨h12, hsim23 _ _ _ _ h23⟩⟩⟩⟩
    | tau_left h ih =>
      intros
      apply ih <;> first | assumption | apply RefineF.inv_tau_right <;> assumption
    | tau_right h ih =>
      intros
      apply RefineF.tau_right <;> (apply ih <;> assumption)
    | zero =>
      intros
      apply RefineF.inv_zero_right <;> assumption
    | choice_left h ih =>
      intros
      apply RefineF.choice_left <;> (apply ih <;> assumption)
    | choice_right h ih =>
      intros
      apply RefineF.choice_right <;> (apply ih <;> assumption)
    | choice_idemp h1 h2 ih1 ih2 =>
      intros p11 p12 t1 h12
      apply RefineF.idx_irrelevance_gen (hsim := hsim12) (p1' := p11) (p2' := 0) at h12
      clear p12
      generalize eq_p12 : (0 : ℕ∞) = p12 at h12
      generalize eq_t2 : _ ⊕ _ = t' at h12
      induction h12 with
      | coind p1'' p2'' h1' h2' h =>
        subst eq_p12
        apply not_lt_bot at h2'
        cases h2'
      | ret h =>
        ctree_elim eq_t2
      | vis h' =>
        ctree_elim eq_t2
      | tau_left h ih =>
        subst eq_p12 eq_t2
        apply RefineF.tau_left; apply ih <;> rfl
      | tau_right h =>
        ctree_elim eq_t2
      | zero =>
        apply RefineF.zero
      | choice_left h ih =>
        apply choice_inj at eq_t2
        have ⟨h, h'⟩ := eq_t2; subst h h'
        apply ih1 <;> assumption
      | choice_right h =>
        apply choice_inj at eq_t2
        have ⟨h, h'⟩ := eq_t2; subst h h'
        apply ih2 <;> assumption
      | choice_idemp h1 h2 ih1 ih2 =>
        subst eq_p12 eq_t2
        apply RefineF.choice_idemp <;> solve | apply ih1 rfl rfl | apply ih2 rfl rfl

  theorem Refine'.trans {r12 : Rel ρ1 ρ2} {r23 : Rel ρ2 ρ3}
    {p11 p12 t1 t2} (h : Refine' (ε := ε) r12 p11 p12 t1 t2)
    : ∀ {p21 p22 t3},
      Refine' r23 p21 p22 t2 t3 →
      Refine' (r12.comp r23) p11 p22 t1 t3 := by
    intros p21 p22 t3 h'
    rw [Refine'] at h h'
    revert p11 p12 t1 t2 p21 p22 t3
    pcofix cih
    intros p11 p12 t1 t2 h1 p21 p22 t3 h2
    pfold
    apply RefineF.monotone
    on_goal 2 =>
      apply RefineF.trans <;> try assumption
    on_goal 3 =>
      intros; rename_i h; punfold at h
      apply RefineF.monotone <;> try assumption
      intros; rename_i h; pclearbot at h
      assumption
    · intro p11 p22 t1 t3 ⟨p12, ⟨t2, ⟨p21, ⟨h1, h2⟩⟩⟩⟩
      pleft
      punfold at h1
      apply cih p11 p12 <;> try assumption
      apply RefineF.monotone <;> try assumption
      intros; rename_i h; pclearbot at h
      assumption
    · intros; rename_i h; punfold at h
      apply RefineF.monotone <;> try assumption
      intros; rename_i h; pclearbot at h
      assumption

  theorem Refine.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2)
    (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : t1 ≤r≤ t2 :=
    ⟨p1, p2, Refine'.coinduct r sim adm p1 p2 t1 t2 h⟩

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
      apply RefineF.tau_left (p1' := ⊤)
      apply RefineF.tau_right (p2' := ⊤)
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
      apply RefineF.choice_idemp (p1' := ⊤)
      · apply RefineF.choice_left (p2' := ⊤)
        apply RefineF.coind 0 0
        <;> simp_all only [ENat.top_pos]
        simp_all only [and_self]
      · apply RefineF.choice_right (p2' := ⊤)
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
      exact RefineF.choice_idemp (p1' := ⊤) (h1.idx_irrelevance _ _) (h2.idx_irrelevance _ _)

    theorem choice_left (h : t1 ≤r≤ t2) : t1 ≤r≤ (t2 ⊕ t3) := by
      obtain ⟨_, _, h⟩ := h
      exists 0, 0
      simp only [Refine'] at *
      exact RefineF.choice_left (p2' := ⊤) (h.idx_irrelevance _ _)

    theorem choice_right (h : t1 ≤r≤ t3) : t1 ≤r≤ (t2 ⊕ t3) := by
      obtain ⟨_, _, h⟩ := h
      exists 0, 0
      simp only [Refine'] at *
      exact RefineF.choice_right (p2' := ⊤) (h.idx_irrelevance _ _)

    lemma dest_tau_right_adm (h : RefineF r (Refine' r) p1 p2 t1 t2)
      : RefineF r (λ p1 p2 t1 t2 => Refine' r p1 p2 t1 t2.tau) p1 p2 t1 t2 := by
      induction h with
      | coind =>
        apply RefineF.coind <;> try assumption
        rw [Refine'] at *
        apply RefineF.tau_right <;> assumption
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
        apply RefineF.tau_left (p1' := ⊤)
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
      | zero => simp only [tauN]
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
    coinductive_fixpoint monotonicity by
      intro sim1 sim2 hsim x h
      cases h with
      | choice_left h => exact .choice_left (hsim _ h)
      | choice_right h => exact .choice_right (hsim _ h)
      | tau h => exact .tau (hsim _ h)

  theorem infND_refine_left : infND ≤r≤ t → IsInf t := by
    intro h
    apply IsInf.coinduct (λ t => infND ≤r≤ t) _ t h
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
      exact ⟨_, ⟨_, by rw [Refine']; assumption⟩⟩
    case choice_left h _ =>
      rename_i p1 _ _ _ _ _
      apply IsInfF.choice_left
      rw [←hinf, ←infND_eq] at h
      rw [Refine]
      exact ⟨_, ⟨_, by rw [Refine']; assumption⟩⟩
    case choice_right h _ =>
      rename_i p1 _ _ _ _ _
      apply IsInfF.choice_right
      rw [←hinf, ←infND_eq] at h
      rw [Refine]
      exact ⟨_, ⟨_, by rw [Refine']; assumption⟩⟩
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

  theorem Refine'.vis_trans [IsRefl _ r'] [IsTrans _ r']
    (hk : ∀ a, Refine' r' p1 p2 (k1 a) (k2 a)) (h : Refine' r' p1 p2 (vis e k2) t)
    : Refine' r' p1 p2 (vis e k1) t := by
    have : Refine' r' p1 p2 (vis e k1) (vis e k2) := by
      simp only [Refine'] at *
      apply RefineF.vis
      intro a
      simp only [Refine'] at *
      exact RefineF.idx_irrelevance (hk a) ⊤ ⊤
    have := Refine'.trans this h
    rw [Rel.comp_self] at this
    exact this

  theorem Refine'.of_ContainsVis {t : CTree ε ρ} [IsRefl ρ r'] (h : ContainsVis e k t) : Refine' r' p1 p2 (vis e k) t := by
    induction h with
    | vis =>
      have ⟨_, _, h⟩ := Refine.refl (r := r') (vis e k)
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

  def Refine'K (r : Rel β1 β2) (p1 p2 : ENat) (k1 : KTree ε α β1) (k2 : KTree ε α β2) : Prop :=
    ∀ a : α, Refine' r p1 p2 (k1 a) (k2 a)

  def RefineK (r : Rel β1 β2) (k1 : KTree ε α β1) (k2 : KTree ε α β2) : Prop :=
    ∀ a : α, (k1 a) ≤r≤ (k2 a)

  instance instLEKTree : LE (KTree ε α β) where
    le := RefineK Eq

  def Refine'S (r : Rel β1 β2) (p1 p2 : ENat) : State ε β1 → State ε β2 → Prop
    | C[ t1 ], C[ t2 ] => Refine' r p1 p2 t1 t2
    | K[ α1 | t1 ], K[ α2 | t2 ] => ∃ hα : α1 = α2, Refine'K r p1 p2 t1 (hα ▸ t2)
    | _, _ => False

  def RefineS (r : Rel β1 β2) (k1 : State ε β1) (k2 : State ε β2) : Prop :=
    ∃ p1 p2, Refine'S r p1 p2 k1 k2

  instance instLEState : LE (State ε β) where
    le := RefineS Eq

  macro "crush_refine" : tactic => `(tactic|(
    repeat first
    | exact RefineF.ret rfl
    | exact RefineF.zero
    | apply RefineF.tau_left (p1' := ⊤)
    | apply RefineF.tau_right (p2' := ⊤)
    | apply RefineF.vis (p1' := 0) (p2' := 0)
    | apply RefineF.choice_idemp (p1' := ⊤)
    | apply RefineF.coind 0 0 ENat.top_pos ENat.top_pos
  ))

  syntax "ctree_match " (num ", ")? term (" with " tactic)? : tactic
  open Lean in
  macro_rules
    | `(tactic|ctree_match $[$n:num,]? $t:term $[ with $simp_rule:tactic]?) => do
      let n := (n.map (Nat.repr ∘ TSyntax.getNat)).getD ""
      let mkIdent' (name : String) := mkIdent (.str .anonymous s!"{name}{n}")
      let simp_rule ←
        match simp_rule with
        | some simp_rule => `(tactic|(
            all_goals try ($simp_rule; crush_refine)
          ))
        | none => `(tactic|skip)
      `(tactic|(
        apply dMatchOn $t
        case' ret =>
          intro $(mkIdent' "v") heq
          subst heq
        case' vis =>
          intro $(mkIdent' "α") $(mkIdent' "e") $(mkIdent' "k") heq
          subst heq
        case' tau =>
          intro $(mkIdent' "t") heq
          subst heq
        case' zero =>
          intro heq
          subst heq
        case' choice =>
          intro $(mkIdent' "cl") $(mkIdent' "cr") heq
          subst heq
        $simp_rule
      ))

end CTree
