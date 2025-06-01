import CTree.Basic

namespace CTree
  inductive RefineF {ε : Type → Type} {ρ σ : Type}
    (r : Rel ρ σ) (sim : Nat → Nat → CTree ε ρ → CTree ε σ → Prop)
    : Nat → Nat → CTree ε ρ → CTree ε σ → Prop
  | prog {p1 p2 t1 t2} (h : sim p1 p2 t1 t2) : RefineF r sim (p1 + 1) (p2 + 1) t1 t2
  | ret {x y p1 p2} (h : r x y) : RefineF r sim p1 p2 (ret x) (ret y)
  | vis {p1 p2} {α : Type} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
      (h : ∀ a : α, sim (p1 + 1) (p2 + 1) (k1 a) (k2 a)) : RefineF r sim p1 p2 (vis e k1) (vis e k2)
  -- | tau (h : sim t1 t2) : RefineF r sim p1 p2 t1.tau t2.tau
  | tau_left {p1 p2 t1 t2}
      (h : RefineF r sim p1 p2 t1 t2) : RefineF r sim (p1 + 1) p2 t1.tau t2
  | tau_right {p1 p2 t1 t2}
      (h : RefineF r sim p1 p2 t1 t2) : RefineF r sim p1 (p2 + 1) t1 t2.tau
  | zero {p1 p2} {t : CTree ε σ} : RefineF r sim p1 p2 zero t
  | choice_left {p1 p2 t1 t2 t3}
      (h : RefineF r sim p1 p2 t1 t2) : RefineF r sim p1 (p2 + 1) t1 (t2 ⊕ t3)
  | choice_right {p1 p2 t1 t2 t3}
      (h : RefineF r sim p1 p2 t1 t3) : RefineF r sim p1 (p2 + 1) t1 (t2 ⊕ t3)
  | choice_idemp {p1 p2 t1 t2 t3}
      (h1 : RefineF r sim p1 p2 t1 t3) (h2 : RefineF r sim p1 p2 t2 t3)
      : RefineF r sim (p1 + 1) p2 (t1 ⊕ t2) t3

  def Refine' (r : Rel ρ σ) (p1 p2 : Nat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    RefineF r (Refine' r p1 p2) p1 p2 t1 t2
    greatest_fixpoint monotonicity by
      intro _ _ hsim _ _ h
      induction h with
      | ret h => exact .ret h
      | vis h => exact .vis λ a => hsim _ _ <| h a
      | tau h => exact .tau (hsim _ _ h)
      | tau_left _ ih => exact RefineF.tau_left ih
      | tau_right _ ih => exact RefineF.tau_right ih
      | zero => exact .zero
      | choice_left _ ih => exact .choice_left ih
      | choice_right _ ih => exact .choice_right ih
      | choice_idemp _ _ ih1 ih2 => exact .choice_idemp ih1 ih2

  -- `t1 r⊑ t2` looks better, but somehow clashes with multi-line class instance definition
  notation:60 t1:61 " ⊑"r:61"⊑ " t2:61 => Refine r t1 t2

  theorem Refine.coind (sim : CTree ε ρ → CTree ε σ → Prop) (adm : ∀ t1 t2, sim t1 t2 → RefineF r sim t1 t2)
    {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim t1 t2) : t1 ⊑r⊑ t2 :=
    Refine.fixpoint_induct r sim adm _ _ h

  theorem RefineF.tauN_left (h : RefineF r sim t1 t2) : ∀ n, RefineF r sim (tauN n t1) t2 := by
    intro n
    induction n with
    | zero =>
      simp only [tauN]
      exact h
    | succ _ ih =>
      simp only [tauN]
      apply RefineF.tau_left
      exact ih

  theorem RefineF.tauN_right (h : RefineF r sim t1 t2) : ∀ n, RefineF r sim t1 (tauN n t2) := by
    intro n
    induction n with
    | zero =>
      simp only [tauN]
      exact h
    | succ _ ih =>
      simp only [tauN]
      apply RefineF.tau_right
      exact ih

  -- Various custom destructors for instances of `Refine` and `RefineF`

  theorem Refine.dest_tau_left (h : t1.tau ⊑r⊑ t2) : t1 ⊑r⊑ t2 := by
    generalize ht1 : t1.tau = t1t at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    case tau h =>
      apply RefineF.tau_right
      rw [Refine] at *
      rw [tau_inj ht1]
      exact h
    case tau_left h ih =>
      rw [tau_inj ht1]
      exact h
    case tau_right ih =>
      apply RefineF.tau_right
      exact ih ht1
    case choice_left _ ih =>
      apply RefineF.choice_left
      exact ih ht1
    case choice_right _ ih =>
      apply RefineF.choice_right
      exact ih ht1

  theorem RefineF.dest_tau_left (h : RefineF r (Refine r) t1.tau t2) : RefineF r (Refine r) t1 t2 := by
    have := Refine.dest_tau_left (by rw [Refine]; exact h)
    rw [Refine] at this
    exact this

  theorem Refine.dest_tau_right (h : t1 ⊑r⊑ t2.tau) : t1 ⊑r⊑ t2 := by
    generalize ht2 : t2.tau = t2t at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    case tau h =>
      apply RefineF.tau_left
      rw [Refine] at *
      rw [tau_inj ht2]
      exact h
    case tau_left ih =>
      apply RefineF.tau_left
      exact ih ht2
    case tau_right h _ =>
      rw [tau_inj ht2]
      exact h
    case zero =>
      exact RefineF.zero
    case choice_idemp ih1 ih2 =>
      exact RefineF.choice_idemp (ih1 ht2) (ih2 ht2)

  theorem RefineF.dest_tau_right (h : RefineF r (Refine r) t1 t2.tau) : RefineF r (Refine r) t1 t2 := by
    have := Refine.dest_tau_right (by rw [Refine]; exact h)
    rw [Refine] at this
    exact this

  theorem Refine.dest_tau (h : t1.tau ⊑r⊑ t2.tau) : t1 ⊑r⊑ t2 := by
    generalize ht1 : t1.tau = t1t at *
    generalize ht2 : t2.tau = t2t at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    <;> ctree_elim ht2
    case tau h =>
      rw [tau_inj ht1, tau_inj ht2]
      rw [Refine] at h
      exact h
    case tau_left h _ =>
      rw [←ht2] at h
      rw [tau_inj ht1]
      exact h.dest_tau_right
    case tau_right h _ =>
      rw [←ht1] at h
      rw [tau_inj ht2]
      exact h.dest_tau_left

  theorem Refine.dest_tauN_left (h : tauN n t1 ⊑r⊑ t2) : t1 ⊑r⊑ t2 := by
    induction n with
    | zero =>
      simp only [tauN] at h
      exact h
    | succ n ih =>
      simp only [tauN] at h
      exact ih h.dest_tau_left

  theorem Refine.dest_tauN_right (h : t1 ⊑r⊑ tauN n t2) : t1 ⊑r⊑ t2 := by
    induction n with
    | zero =>
      simp only [tauN] at h
      exact h
    | succ n ih =>
      simp only [tauN] at h
      exact ih h.dest_tau_right

  theorem RefineF.dest_ret_ret {ε} (h : RefineF (ε := ε) r (Refine r) (.ret x) (.ret y)) : r x y := by
    generalize ht1 : CTree.ret x = t1 at *
    generalize ht2 : CTree.ret y = t2 at *
    cases h
    <;> ctree_elim ht1
    <;> ctree_elim ht2
    rw [ret_inj ht1]
    rw [ret_inj ht2]
    assumption

  theorem Refine.dest_ret_ret {ε} (h : Refine (ε := ε) r (ret x) (ret y)) : r x y := by
    rw [Refine] at h
    exact h.dest_ret_ret

  theorem Refine.dest_ret_left {t2 : CTree ε σ} (h : Refine r (ret x) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (y : σ), t2' = ret y ∧ r x y)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (ret x ⊑r⊑ t3 ∨ ret x ⊑r⊑ t4))) := by
    generalize ht1 : ret x = t1 at h
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    case ret hxy =>
      rename_i _ y
      rw [←ret_inj ht1] at hxy
      exists 0, ret y
      apply And.intro
      · simp only [tauN]
      · apply Or.inl
        exists y
    case tau_right ih =>
      have ⟨n, t2', ⟨ht2, h⟩⟩ := ih ht1
      exists n + 1, t2'
      apply And.intro _ h
      rw [ht2]
      simp only [tauN]
    case choice_left h _ =>
      rename_i t3 t4 _
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        rw [Refine]
        exact Or.inl h
    case choice_right h _ =>
      rename_i t4 t3 _
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        simp only [Refine]
        exact Or.inr h

  theorem RefineF.dest_ret_left {t2 : CTree ε σ} (h : RefineF r (Refine r) (.ret x) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (y : σ), t2' = .ret y ∧ r x y)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (.ret x ⊑r⊑ t3 ∨ .ret x ⊑r⊑ t4))) :=
    Refine.dest_ret_left (by rw [Refine]; exact h)

  theorem Refine.dest_ret_right (h : Refine r t1 (ret y))
    : ∃ n t1', t1 = tauN n t1' ∧
        (t1' = zero
          ∨ (∃ x, t1' = ret x ∧ r x y)
          ∨ (∃ t1 t2, t1' = t1 ⊕ t2 ∧ t1 ⊑r⊑ ret y ∧ t2 ⊑r⊑ ret y)) := by
    generalize ht2 : ret y = t2 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    case ret hxy =>
      rename_i x y
      rw [ret_inj ht2]
      exists 0, ret x
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        apply Or.inl
        exists x
    case tau_left ih =>
      have ⟨n, t1', ht1, h⟩ := ih ht2
      exists n + 1, t1'
      apply And.intro _ h
      rw [ht1]
      simp only [tauN]
    case zero =>
      exists 0, zero
      apply And.intro
      · simp only [tauN]
      · exact Or.inl rfl
    case choice_idemp h1 h2 _ _ =>
      rename_i t1 t3 t2 _ _
      exists 0, t1 ⊕ t2
      apply And.intro
      · simp only [tauN]
      · repeat apply Or.inr
        exists t1, t2
        apply And.intro rfl
        apply And.intro <;> (rw [Refine]; assumption)

  theorem RefineF.dest_vis_both (h : RefineF r (Refine r) (.vis e k1) (.vis e k2)) : ∀ a, k1 a ⊑r⊑ k2 a := by
    generalize ht1 : CTree.vis e k1 = t1 at *
    generalize ht2 : CTree.vis e k2 = t2 at *
    cases h
    <;> ctree_elim ht1
    <;> ctree_elim ht2
    have hα := vis_inj_α ht1
    subst hα
    have ⟨he, hk1⟩ := vis_inj ht1
    subst hk1
    have ⟨he, hk2⟩ := vis_inj ht2
    subst hk2
    assumption

  theorem Refine.dest_vis_left {e : ε α} {t2 : CTree ε σ} (h : Refine r (vis e k1) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (k2 : α → CTree ε σ), t2' = vis e k2 ∧ ∀ a, k1 a ⊑r⊑ k2 a)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (vis e k1 ⊑r⊑ t3 ∨ vis e k1 ⊑r⊑ t4))) := by
    generalize ht1 : vis e k1 = t1 at h
    rw [Refine] at *
    induction h
    <;> ctree_elim ht1
    case vis h =>
      rename_i k2
      have ha := vis_inj_α ht1
      subst ha
      have ⟨he, hk⟩ := vis_inj ht1
      subst he
      rw [←hk] at h
      exists 0, vis e k2
      apply And.intro
      · simp only [tauN]
      · apply Or.inl
        exists k2
    case tau_right ih =>
      have ⟨n, t2', ⟨ht2, h⟩⟩ := ih ht1
      exists n + 1, t2'
      apply And.intro _ h
      rw [ht2]
      simp only [tauN]
    case choice_left h _ =>
      rename_i t3 t4 _
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        rw [Refine]
        exact Or.inl h
    case choice_right h _ =>
      rename_i t4 t3 _
      exists 0, t3 ⊕ t4
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        exists t3, t4
        apply And.intro rfl
        simp only [Refine]
        exact Or.inr h

  theorem RefineF.dest_vis_left {e : ε α} {t2 : CTree ε σ} (h : RefineF r (Refine r) (.vis e k1) t2)
    : ∃ (n : Nat) (t2' : CTree ε σ), t2 = tauN n t2' ∧
          ((∃ (k2 : α → CTree ε σ), t2' = .vis e k2 ∧ ∀ a, k1 a ⊑r⊑ k2 a)
           ∨ (∃ t3 t4, t2' = t3 ⊕ t4 ∧ (.vis e k1 ⊑r⊑ t3 ∨ .vis e k1 ⊑r⊑ t4))) :=
    Refine.dest_vis_left (by rw [Refine]; exact h)

  theorem Refine.dest_vis_right {e : ε α} (h : Refine r t1 (vis e k2))
    : ∃ n t1', t1 = tauN n t1' ∧
        (t1' = zero
          ∨ (∃ k1, t1' = vis e k1 ∧ ∀ a, k1 a ⊑r⊑ k2 a)
          ∨ (∃ t1 t2, t1' = t1 ⊕ t2 ∧ t1 ⊑r⊑ vis e k2 ∧ t2 ⊑r⊑ vis e k2)) := by
    generalize ht2 : vis e k2 = t2 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    case vis hk =>
      rename_i e k1 k2
      have hα := vis_inj_α ht2
      subst hα
      have ⟨he, hk⟩ := vis_inj ht2
      subst he
      subst hk
      exists 0, vis e k1
      apply And.intro
      · simp only [tauN]
      · apply Or.inr
        apply Or.inl
        exists k1
    case tau_left ih =>
      have ⟨n, t1', ht1, h⟩ := ih ht2
      exists n + 1, t1'
      apply And.intro _ h
      rw [ht1]
      simp only [tauN]
    case zero =>
      exists 0, zero
      apply And.intro
      · simp only [tauN]
      · exact Or.inl rfl
    case choice_idemp h1 h2 _ _ =>
      rename_i t1 t3 t2 _ _
      exists 0, t1 ⊕ t2
      apply And.intro
      · simp only [tauN]
      · repeat apply Or.inr
        exists t1, t2
        apply And.intro rfl
        apply And.intro <;> (rw [Refine]; assumption)

  theorem Refine.dest_zero_right (h : Refine r t1 zero)
    : ∃ n, t1 = tauN n zero ∨ ∃ t2 t3, t1 = tauN n (t2 ⊕ t3) ∧ t2 ⊑r⊑ zero ∧ t3 ⊑r⊑ zero := by
    generalize ht2 : zero = t2 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht2
    rw [←ht2]
    case tau_left ih =>
      have ⟨n, h⟩ := ih ht2
      exists n + 1
      match h with
      | .inl h =>
        apply Or.inl
        rw [h]
        simp only [tauN]
      | .inr ⟨t2, t3, h⟩ =>
        apply Or.inr
        exists t2, t3
        simp only [tauN]
        apply And.intro
        · congr
          exact h.left
        · rw [ht2]
          exact h.right
    case zero =>
      exists 0
      apply Or.inl
      simp only [tauN]
    case choice_idemp h1 h2 _ _ =>
      exists 0
      apply Or.inr
      rename_i t1 _ t2 _ _
      exists t1, t2
      apply And.intro
      · simp only [tauN]
      · apply And.intro <;> (rw [Refine]; assumption)

  theorem Refine.dest_choice_ret (h : (t1 ⊕ t2) ⊑r⊑ ret y)
    : t1 ⊑r⊑ (ret y) ∧ t2 ⊑r⊑ (ret y) := by
    generalize ht1 : t1 ⊕ t2 = t1 at *
    generalize ht2 : ret y = t2 at *
    rw [Refine] at h
    cases h
    <;> ctree_elim ht1
    <;> ctree_elim ht2
    case choice_idemp h1 h2 =>
      have ⟨h1eq, h2eq⟩ := choice_inj ht1
      apply And.intro
      · rw [h1eq, Refine]
        exact h1
      · rw [h2eq, Refine]
        exact h2

  theorem RefineF.dest_choice_ret (h : RefineF r (Refine r) (t1 ⊕ t2) (.ret y))
    : Refine r t1 (.ret y) ∧ Refine r t2 (.ret y) :=
    Refine.dest_choice_ret (by rw [Refine]; exact h)

  theorem Refine.dest_choice_right (h : t1 ⊑r⊑ t2 ⊕ t3)
    : ∃ n t1', t1 = tauN n t1' ∧
      ((t1' = zero) ∨ (t1 ⊑r⊑ t2) ∨ (t1 ⊑r⊑ t3) ∨ (∃ t11 t12, t1' = t11 ⊕ t12 ∧ t11 ⊕ t12 ⊑r⊑ t2 ⊕ t3)) := by
    generalize ht2 : t2 ⊕ t3 = t2 at *
    rw [Refine] at h
    induction h
    <;> ctree_elim ht2
    case tau_left ih =>
      obtain ⟨n, t1', ht1', ih⟩ := ih ht2
      exists n + 1, t1'
      apply And.intro
      · simp only [tauN, ht1']
      · apply ih.elim3
        · intro h
          exact Or.inl h
        · intro h
          apply Or.inr (Or.inl _)
          rw [Refine] at *
          exact RefineF.tau_left h
        · intro h
          match h with
          | .inl h =>
            apply Or.inr (Or.inr (Or.inl _))
            rw [Refine]
            apply RefineF.tau_left
            rw [Refine] at h
            exact h
          | .inr h =>
            apply Or.inr <| Or.inr <| Or.inr _
            exact h
    case zero =>
      exists 0, zero
      apply And.intro _ (.inl rfl)
      simp only [tauN]
    case choice_left h _ =>
      rename_i t1 t2 t3 _
      have ⟨heq1, _⟩ := choice_inj ht2
      subst heq1
      exists 0, t1
      apply And.intro
      · simp only [tauN]
      · apply Or.inr <| Or.inl _
        rw [Refine]
        assumption
    case choice_right h _ =>
      rename_i t1 t2 t3 _
      have ⟨_, heq2⟩ := choice_inj ht2
      subst heq2
      exists 0, t1
      apply And.intro
      · simp only [tauN]
      · apply Or.inr <| Or.inr <| Or.inl _
        rw [Refine]
        assumption
    case choice_idemp h1 h2 _ _ =>
      rename_i t1 t3 t2 _ _
      exists 0, t1 ⊕ t2
      apply And.intro
      · simp only [tauN]
      · apply Or.inr <| Or.inr <| Or.inr _
        exists t1, t2
        apply And.intro rfl
        rw [Refine]
        exact RefineF.choice_idemp h1 h2

  theorem Refine.dest_choice_left_zero_left (h : (zero ⊕ t1) ⊑r⊑ t2) : t1 ⊑r⊑ t2 := by
    generalize ht1 : zero ⊕ t1 = t1' at *
    rw [Refine] at h
    induction h
    <;> ctree_elim ht1
    case tau_right ih =>
      rw [Refine] at *
      apply RefineF.tau_right
      exact ih ht1
    case choice_left ih =>
      rw [Refine] at *
      apply RefineF.choice_left
      exact ih ht1
    case choice_right ih =>
      rw [Refine] at *
      apply RefineF.choice_right
      exact ih ht1
    case choice_idemp =>
      rw [(choice_inj ht1).right]
      rw [Refine]
      assumption

  theorem RefineF.dest_choice_left_zero_left (h : RefineF r (Refine r) (.zero ⊕ t1) t2) : RefineF r (Refine r) t1 t2 := by
    have := Refine.dest_choice_left_zero_left (by rw [Refine]; exact h)
    rw [Refine] at this
    exact this

  @[refl]
  theorem Refine.refl {r : Rel ρ ρ} [IsRefl ρ r] (t : CTree ε ρ) : t ⊑r⊑ t := by
    sorry

  @[refl]
  theorem RefineF.refl {r : Rel ρ ρ} [IsRefl ρ r] (t : CTree ε ρ) : RefineF r (Refine r) t t := by
    have := Refine.refl (r := r) t
    rw [Refine] at this
    exact this

  /- Transitivity Proof -/

  theorem Refine.choice_left_tau (h : (t1 ⊕ t2) ⊑r⊑ t3) : (t1.tau ⊕ t2) ⊑r⊑ t3 := by
    generalize ht4 : t1 ⊕ t2 = t4 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht4
    case tau_right ih => exact RefineF.tau_right (ih ht4)
    case choice_left ih => exact RefineF.choice_left (ih ht4)
    case choice_right ih => exact RefineF.choice_right (ih ht4)
    case choice_idemp h1 h2 ih1 ih2 =>
      have ⟨heq1, heq2⟩ := choice_inj ht4
      subst heq1
      subst heq2
      exact RefineF.choice_idemp (RefineF.tau_left h1) h2

  theorem Refine.choice_right_tau (h : (t1 ⊕ t2) ⊑r⊑ t3) : (t1 ⊕ t2.tau) ⊑r⊑ t3 := by
    generalize ht4 : t1 ⊕ t2 = t4 at *
    rw [Refine] at *
    induction h
    <;> ctree_elim ht4
    case tau_right ih => exact RefineF.tau_right (ih ht4)
    case choice_left ih => exact RefineF.choice_left (ih ht4)
    case choice_right ih => exact RefineF.choice_right (ih ht4)
    case choice_idemp h1 h2 ih1 ih2 =>
      have ⟨heq1, heq2⟩ := choice_inj ht4
      subst heq1
      subst heq2
      exact RefineF.choice_idemp h1 (RefineF.tau_left h2)

  theorem Refine.choice_choice_or (h1 : t1 ⊑r⊑ t3 ⊕ t4) (h2 : t2 ⊑r⊑ t3 ⊕ t4)
    : (t1 ⊕ t2) ⊑r⊑ t3 ∨ (t1 ⊕ t2) ⊑r⊑ t4 := by
    generalize ht5 : t3 ⊕ t4 = t5 at *
    rw [Refine] at h1
    rw [Refine] at h2
    induction h1
    <;> ctree_elim ht5
    case tau_left ih =>
      apply (ih ht5 h2).elim
      · intro h
        exact Or.inl h.choice_left_tau
      · intro h
        exact Or.inr h.choice_left_tau
    case zero =>
      induction h2
      <;> ctree_elim ht5
      case tau_left ih =>
        apply (ih ht5).elim
        · intro h
          exact Or.inl h.choice_right_tau
        · intro h
          exact Or.inr h.choice_right_tau
      case zero =>
        apply Or.inl
        rw [Refine]
        apply RefineF.choice_idemp
        <;> exact RefineF.zero
      case choice_left =>
        have := (choice_inj ht5).left
        subst this
        apply Or.inl
        rw [Refine]
        apply RefineF.choice_idemp
        · exact RefineF.zero
        · assumption
      case choice_right =>
        have := (choice_inj ht5).right
        subst this
        apply Or.inr
        rw [Refine]
        apply RefineF.choice_idemp
        · exact RefineF.zero
        · assumption
      case choice_idemp ih1 ih2 =>
        have ih2 := ih2 ht5
        have ih1 := ih1 ht5
        cases ih1 <;> cases ih2
        · rename_i h1 h2
          apply Or.inl
          rw [Refine] at *
          apply RefineF.choice_idemp RefineF.zero
          apply RefineF.choice_idemp
          <;> (apply RefineF.dest_choice_left_zero_left; assumption)
        · rename_i h1 h2

          sorry
        · sorry
        · rename_i h1 h2
          apply Or.inr
          rw [Refine] at *
          apply RefineF.choice_idemp RefineF.zero
          apply RefineF.choice_idemp
          <;> (apply RefineF.dest_choice_left_zero_left; assumption)
    all_goals sorry

  @[trans]
  theorem Refine.trans {r1 : Rel α β} {r2 : Rel β γ} {t1 : CTree ε α} {t2 : CTree ε β} {t3 : CTree ε γ}
    (h1 : t1 ⊑r1⊑ t2) (h2 : t2 ⊑r2⊑ t3) : t1 ⊑(r1.comp r2)⊑ t3 := by
    apply Refine.coind (λ t1 t3 => ∃ t2, t1 ⊑r1⊑ t2 ∧ t2 ⊑r2⊑ t3) _
    · exists t2
    · intro t1 t3 ⟨t2, ⟨h1, h2⟩⟩
      rw [Refine] at *
      induction h1 with
      | ret hxy =>
        rename_i x y
        clear *- hxy h2
        generalize ht2 : ret y = t2 at *
        induction h2
        <;> ctree_elim ht2
        case ret hyz =>
          rename_i z
          have := ret_inj ht2
          subst this
          apply RefineF.ret
          exists y
        case tau_right ih => exact RefineF.tau_right (ih ht2)
        case choice_left ih => exact RefineF.choice_left (ih ht2)
        case choice_right ih => exact RefineF.choice_right (ih ht2)
      | vis hk1 =>
        rename_i α e k1 k2
        clear *- hk1 h2
        generalize ht2 : vis e k2 = t2 at *
        induction h2
        <;> ctree_elim ht2
        case vis hk2 =>
          rename_i k3
          have hα := vis_inj_α ht2
          subst hα
          have ⟨he, hk⟩ := vis_inj ht2
          subst he
          subst hk
          apply RefineF.vis
          intro a
          exists k2 a
          exact And.intro (hk1 a) (hk2 a)
        case tau_right ih => exact RefineF.tau_right (ih ht2)
        case choice_left ih => exact RefineF.choice_left (ih ht2)
        case choice_right ih => exact RefineF.choice_right (ih ht2)
      | tau h1 =>
        induction h2.dest_tau_left with
        | ret hyz =>
          rename_i t1 _ y z
          apply RefineF.tau_left
          have h2 := h2.dest_tau_left
          clear *- hyz h1 h2
          rw [Refine] at h1
          generalize ht2 : ret y = t2 at *
          induction h1
          <;> ctree_elim ht2
          case ret hxy =>
            have := ret_inj ht2
            subst this
            apply RefineF.ret
            exists y
          case tau_left ih => exact RefineF.tau_left (ih ht2 h2)
          case zero => exact RefineF.zero
          case choice_idemp ih1 ih2 => exact RefineF.choice_idemp (ih1 ht2 h2) (ih2 ht2 h2)
        | vis hk2 =>
          rename_i t1 _ α e k2 k3
          have h2 := h2.dest_tau_left
          clear *- hk2 h1 h2
          apply RefineF.tau_left
          generalize ht2 : vis e k2 = t2 at *
          rw [Refine] at h1
          induction h1
          <;> ctree_elim ht2
          case vis hk1 =>
            have hα := vis_inj_α ht2
            subst hα
            have ⟨he, hk⟩ := vis_inj ht2
            subst he
            subst hk
            apply RefineF.vis
            intro a
            exists k2 a
            exact And.intro (hk1 a) (hk2 a)
          case tau_left ih => exact RefineF.tau_left (ih ht2 h2)
          case zero => exact RefineF.zero
          case choice_idemp ih1 ih2 => exact RefineF.choice_idemp (ih1 ht2 h2) (ih2 ht2 h2)
        | tau h =>
          apply RefineF.tau
          rename_i t2 _
          exists t2
          apply And.intro h1.dest_tau_right
          rw [Refine]
          exact h2.dest_tau_left.dest_tau_left.dest_tau_right
        | tau_left _ ih => exact ih h1.dest_tau_right h2.dest_tau_left
        | tau_right _ ih => exact RefineF.tau_right (ih h1 h2.dest_tau_right)
        | zero =>
          rename_i t1 _ t3
          have h2 := h2.dest_tau_left
          clear *- h1 h2
          apply RefineF.tau_left
          rw [Refine] at h1
          generalize ht2 : zero = t2 at *
          induction h1
          <;> ctree_elim ht2
          case tau_left ih => exact RefineF.tau_left (ih ht2 h2)
          case zero => exact RefineF.zero
          case choice_idemp ih1 ih2 => exact RefineF.choice_idemp (ih1 ht2 h2) (ih2 ht2 h2)
        | choice_left h ih =>
          apply RefineF.choice_left
          apply ih h1
          exact RefineF.tau_left h
        | choice_right h ih =>
          apply RefineF.choice_right
          apply ih h1
          exact RefineF.tau_left h
        | choice_idemp h21 h22 ih1 ih2 =>
          rename_i t1 _ t21 t3 t22
          clear *- h1 h21 h22 ih1 ih2
          obtain ⟨n, t1', ht1', h1⟩ := h1.dest_choice_right
          apply h1.elim4
          · intro h
            subst ht1'
            subst h
            apply RefineF.tau_left
            apply RefineF.tauN_left
            exact RefineF.zero
          · intro h
            exact ih1 h (RefineF.tau_left h21)
          · intro h
            exact ih2 h (RefineF.tau_left h22)
          · intro h
            obtain ⟨t11, t12, ht1', h1c⟩ := h
            rename_i ht1
            subst ht1
            subst ht1'
            clear *- h1c ih1 ih2 h21 h22
            generalize ht1 : t11 ⊕ t12 = t1 at *
            generalize ht2 : t21 ⊕ t22 = t2 at *
            rw [Refine] at h1c
            induction h1c
            <;> ctree_elim ht1
            <;> ctree_elim ht2
            case choice_left =>
              apply ih1
              · rw [(choice_inj ht2).left]
                rw [Refine]
                apply RefineF.tauN_left
                assumption
              · exact RefineF.tau_left h21
            case choice_right =>
              apply ih2
              · rw [(choice_inj ht2).right]
                rw [Refine]
                apply RefineF.tauN_left
                assumption
              · exact RefineF.tau_left h22
            case choice_idemp h1 h2 _ _ =>
              subst ht2
              have ⟨heq1, heq2⟩ := choice_inj ht1
              subst heq1
              subst heq2
              clear *- h1 h2 h21 h22 ih1 ih2
              have := Refine.choice_choice_or (by rw [Refine]; exact h1) (by rw [Refine]; exact h2)
              apply this.elim
              · intro h
                apply ih1
                · rw [Refine] at *
                  apply RefineF.tauN_left
                  exact h
                · exact RefineF.tau_left h21
              · intro h
                apply ih2
                · rw [Refine] at *
                  apply RefineF.tauN_left
                  exact h
                · exact RefineF.tau_left h22
      | tau_left _ ih => exact RefineF.tau_left (ih h2)
      | tau_right _ ih => exact ih h2.dest_tau_left
      | zero => exact RefineF.zero
      | choice_left h1 ih =>
        rename_i t21 t22
        apply ih
        clear *- h2
        generalize ht2 : t21 ⊕ t22 = t2 at *
        induction h2
        <;> ctree_elim ht2
        case tau_right ih => exact RefineF.tau_right (ih ht2)
        case choice_left ih => exact RefineF.choice_left (ih ht2)
        case choice_right ih => exact RefineF.choice_right (ih ht2)
        case choice_idemp h1 _ _ _ =>
          rw [(choice_inj ht2).left]
          exact h1
      | choice_right h1 ih =>
        rename_i t22 t21
        apply ih
        clear *- h2
        generalize ht2 : t21 ⊕ t22 = t2 at *
        induction h2
        <;> ctree_elim ht2
        case tau_right ih => exact RefineF.tau_right (ih ht2)
        case choice_left ih => exact RefineF.choice_left (ih ht2)
        case choice_right ih => exact RefineF.choice_right (ih ht2)
        case choice_idemp _ h2 _ _ =>
          rw [(choice_inj ht2).right]
          exact h2
      | choice_idemp _ _ ih1 ih2 => apply RefineF.choice_idemp (ih1 h2) (ih2 h2)

  instance {r : Rel ρ ρ} [IsRefl ρ r] : IsRefl (CTree ε ρ) (Refine r) where
    refl := .refl

  -- TODO: Does `r` have to be refl and trans?
  instance {r : Rel ρ ρ} [IsRefl ρ r] [IsTrans ρ r] : IsTrans (CTree ε ρ) (Refine r) where
    trans := by
      intro a b c h1 h2
      have := Refine.trans h1 h2
      rw [Rel.comp_self (r := r)] at this
      exact this

  def Refine.instPreorder (r : Rel ρ ρ) [IsRefl ρ r] [IsTrans ρ r] : Preorder (CTree ε ρ) :=
  {
    le := Refine r,
    le_refl := refl,
    le_trans := by
      intro a b c h1 h2
      have := trans h1 h2
      rw [Rel.comp_self (r := r)] at this
      exact this
  }

end CTree
