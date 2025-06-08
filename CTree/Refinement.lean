import CTree.Basic
import Mathlib.Data.Nat.PartENat


namespace CTree
  /--
    Somewhat failed attemp at defining a direct refinement between `CTree`s without defining traces first.
    The definition uses ideas from the [FreeSim paper](https://dl.acm.org/doi/10.1145/3622857)

    While this definition seems plausible and we can prove reflexivity and an intersting theorem about infinite non-determinism.
    This nested inductive-coinductive structure is very difficult to work with in practice compared to `TraceRefine` (at least
    for writing general equational theories, ymmv when proving equivalence of concrete systems).

    Note that this is not equivalent to `TraceRefine`, becasuse `TraceRefine` makes no distinction between `zero` and `infND`.
  -/
  inductive RefineF {ε : Type → Type} {ρ σ : Type}
    (r : Rel ρ σ) (sim : PartENat → PartENat → CTree ε ρ → CTree ε σ → Prop)
    : PartENat → PartENat → CTree ε ρ → CTree ε σ → Prop
  | coind {p1 p2 t1 t2} (p1' p2' : PartENat)
      (h1 : p1' < p1) (h2 : p2' < p2) (h : sim p1' p2' t1 t2)
      : RefineF r sim p1 p2 t1 t2
  | ret {x y p1 p2} (h : r x y) : RefineF r sim p1 p2 (ret x) (ret y)
  | vis {p1 p2} {α : Type} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
      (h : ∀ a : α, RefineF r sim ⊤ ⊤ (k1 a) (k2 a)) : RefineF r sim p1 p2 (vis e k1) (vis e k2)
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

  def Refine' (r : Rel ρ σ) (p1 p2 : PartENat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    RefineF r (Refine' r) p1 p2 t1 t2
    greatest_fixpoint monotonicity by
      intro _ _ hsim _ _ _ _ h
      induction h with
      | coind _ _ h1 h2 h => exact .coind _ _ h1 h2 (hsim _ _ _ _ h)
      | ret h => exact .ret h
      | vis _ ih => exact .vis λ a => ih a
      | tau_left _ ih => exact RefineF.tau_left ih
      | tau_right _ ih => exact RefineF.tau_right ih
      | zero => exact .zero
      | choice_left _ ih => exact .choice_left ih
      | choice_right _ ih => exact .choice_right ih
      | choice_idemp _ _ ih1 ih2 => exact .choice_idemp ih1 ih2

  abbrev Refine (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) :=
    ∃ p1 p2, Refine' r p1 p2 t1 t2

  -- `t1 r⊑ t2` looks better, but somehow clashes with multi-line class instance definition
  notation:60 t1:61 " ⊑"r:61"⊑ " t2:61 => Refine r t1 t2

  theorem RefineF.idx_mono_left {p1' p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    (h1 : p1' ≤ p1) (h : RefineF r sim p1' p2 t1 t2) : RefineF r sim p1 p2 t1 t2 := by
    induction h with
    | coind p1'' p2'' h1' h2 h =>
      apply RefineF.coind p1'' p2'' _ h2 h
      exact lt_of_lt_of_le h1' h1
    | ret h => exact RefineF.ret h
    | vis h => exact RefineF.vis h
    | tau_left h => exact RefineF.tau_left h
    | tau_right h ih =>
      apply RefineF.tau_right
      exact ih h1
    | zero => exact RefineF.zero
    | choice_left h ih =>
      apply RefineF.choice_left
      exact ih h1
    | choice_right h ih =>
      apply RefineF.choice_right
      exact ih h1
    | choice_idemp h1' h2' => exact RefineF.choice_idemp h1' h2'

  theorem RefineF.idx_mono_right {p1 p2' p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    (h2 : p2' ≤ p2) (h : RefineF r sim p1 p2' t1 t2) : RefineF r sim p1 p2 t1 t2 := by
    induction h with
    | coind p1'' p2'' h1 h2' h =>
      apply RefineF.coind p1'' p2'' h1 _ h
      exact lt_of_lt_of_le h2' h2
    | ret h => exact RefineF.ret h
    | vis h => exact RefineF.vis h
    | tau_left h ih =>
      apply RefineF.tau_left
      exact ih h2
    | tau_right h =>
      exact RefineF.tau_right h
    | zero => exact RefineF.zero
    | choice_left h => exact RefineF.choice_left h
    | choice_right h => exact RefineF.choice_right h
    | choice_idemp _ _ ih1 ih2 =>
      apply RefineF.choice_idemp
      · exact ih1 h2
      · exact ih2 h2

  theorem RefineF.idx_mono {t1 : CTree ε ρ} {t2 : CTree ε σ}
    {p1' p1 p2' p2 : PartENat} (h1 : p1' ≤ p1) (h2 : p2' ≤ p2) (h : RefineF r sim p1' p2' t1 t2)
    : RefineF r sim p1 p2 t1 t2 := by
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      apply RefineF.coind p1'' p2'' _ _ h
      exact lt_of_lt_of_le h1' h1
      exact lt_of_lt_of_le h2' h2
    | ret h => exact RefineF.ret h
    | vis h _ => exact RefineF.vis h
    | tau_left h =>
      apply RefineF.tau_left
      exact RefineF.idx_mono_right h2 h
    | tau_right h =>
      apply RefineF.tau_right
      exact RefineF.idx_mono_left h1 h
    | zero => exact RefineF.zero
    | choice_left h =>
      apply RefineF.choice_left
      exact RefineF.idx_mono_left h1 h
    | choice_right h =>
      apply RefineF.choice_right
      exact RefineF.idx_mono_left h1 h
    | choice_idemp h1' h2' =>
      apply RefineF.choice_idemp
      · exact RefineF.idx_mono_right h2 h1'
      · exact RefineF.idx_mono_right h2 h2'

  macro "crush_cont_aux" ih:term ", " h_ih:term : tactic => `(tactic|(
    first
      | apply RefineF.ret; assumption
      | apply RefineF.vis; assumption
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
    (h : RefineF r (Refine' r) p1 p2 t1 t2') :
    ∀ (t2 : CTree ε σ), ((∃ t1', t2 = t1' ⊕ t2') ∨ (∃ t1', t2 = t2' ⊕ t1') ∨ t2 = t2'.tau) →
    ∀ p1' p2', RefineF r (Refine' r) p1' p2' t1 t2 := by
    revert p2 t1 t2 t2'
    induction p1 using WellFounded.induction PartENat.lt_wf
    rename_i ih
    intro _ _ _ _ h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      rw [Refine'] at h
      apply ih <;> assumption
    | ret => crush_cont _, _
    | vis hk _ => crush_cont _, _
    | tau_left h => crush_cont _, _
    | tau_right h h_ih => crush_cont ih, h_ih
    | zero => intros; exact RefineF.zero
    | choice_left h h_ih => crush_cont ih, h_ih
    | choice_right h h_ih => crush_cont ih, h_ih
    | choice_idemp _ _ => crush_cont _, _

  theorem RefineF.idx_irrelevance {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
    (h : RefineF r (Refine' r) p1 p2 t1 t2)
    : ∀ p1' p2', RefineF r (Refine' r) p1' p2' t1 t2 := by
    revert t1 t2 p1
    induction p2 using WellFounded.induction PartENat.lt_wf
    rename_i p1 ih_p1
    intro p1 t1 t2 h
    induction h with
    | coind p1'' p2'' h1' h2' h =>
      intro p1' p2'
      rw [Refine'] at h
      exact ih_p1 p2'' h2' h p1' p2'
    | ret h =>
      intros; apply RefineF.ret; assumption
    | vis h _ =>
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
    | choice_idemp h1 h2 =>
      rename_i h1_ih h2_ih
      intro p1 t1
      apply RefineF.choice_idemp
      · apply h1_ih; assumption
      · apply h2_ih; assumption

  theorem Refine.coind (sim : PartENat → PartENat → CTree ε ρ → CTree ε σ → Prop) (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → RefineF r sim p1 p2 t1 t2)
    (p1 p2 : PartENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : t1 ⊑r⊑ t2 :=
    ⟨p1, ⟨p2, Refine'.fixpoint_induct r sim adm p1 p2 t1 t2 h⟩⟩

  @[refl]
  theorem Refine.refl {r : Rel ρ ρ} [IsRefl ρ r] (t : CTree ε ρ) : t ⊑r⊑ t := by
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
      <;> simp_all only [PartENat.zero_lt_top]
      simp_all only [and_self]
    · intro α e k heq
      subst heq
      apply RefineF.vis
      intro a
      apply RefineF.coind 0 0
      <;> simp_all only [PartENat.zero_lt_top]
      simp_all only [and_self]
    · intro heq
      subst heq
      exact RefineF.zero
    · intro c1 c2 heq
      subst heq
      apply RefineF.choice_idemp
      · apply RefineF.choice_left
        apply RefineF.coind 0 0
        <;> simp_all only [PartENat.zero_lt_top]
        simp_all only [and_self]
      · apply RefineF.choice_right
        apply RefineF.coind 0 0
        <;> simp_all only [PartENat.zero_lt_top]
        simp_all only [and_self]

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

  theorem infND_refine_left : infND ⊑r⊑ t → IsInf t := by
    intro h
    apply IsInf.fixpoint_induct (λ t => infND ⊑r⊑ t) _ t h
    intro t h
    rw [Refine] at h
    obtain ⟨p1, p2, h⟩ := h
    revert p1
    induction p2 using WellFounded.induction PartENat.lt_wf
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

end CTree
