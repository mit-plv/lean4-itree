import CTree.Basic
import CTree.Refinement

namespace CTree

  def Eutt (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    t1 ⊑r⊑ t2 ∧ t2 ⊑(flip r)⊑ t1

  instance {r : Rel α α} [IsRefl α r] : IsRefl α (flip r) where
    refl a := by
      simp only [flip]
      exact IsRefl.refl a

  instance {r : Rel α α} [IsTrans α r] : IsTrans α (flip r) where
    trans a b c := by
      intro h1 h2
      simp only [flip] at *
      exact IsTrans.trans _ _ _ h2 h1

  namespace Eutt
    @[refl]
    theorem refl {r : Rel ρ ρ} [IsRefl _ r] {t : CTree ε ρ} : Eutt r t t :=
      ⟨.refl _, .refl _⟩

    @[symm]
    theorem symm {r : Rel ρ ρ} [IsSymm _ r] (t1 t2 : CTree ε ρ) : Eutt r t1 t2 → Eutt r t2 t1 := by
      sorry

    @[trans]
    theorem trans {r : Rel ρ ρ} [IsRefl _ r] [IsTrans _ r] (t1 t2 t3 : CTree ε ρ) (h1 : Eutt r t1 t2) (h2 : Eutt r t2 t3) : Eutt r t1 t3 :=
      ⟨(Rel.comp_self (r := r)) ▸ .trans h1.left h2.left, (Rel.comp_self (r := flip r)) ▸ .trans h2.right h1.right⟩

    theorem choice_idemp {t1 t2 : CTree ε ρ} {t3 : CTree ε σ} (h1 : Eutt r t1 t3) (h2 : Eutt r t2 t3)
      : Eutt r (t1 ⊕ t2) t3 := by
      have ⟨h1l, h1r⟩ := h1
      have ⟨h2l, h2r⟩ := h2
      rw [Refine] at *
      apply And.intro
      · rw [Refine]
        exact RefineF.choice_idemp h1l h2l
      · rw [Refine]
        exact RefineF.choice_left h1r

    theorem choice_idemp_self [IsRefl _ r] : Eutt r (t ⊕ t) t :=
      choice_idemp refl refl

    theorem choice_comm [IsRefl _ r] {t1 t2 : CTree ε ρ} : Eutt r (t1 ⊕ t2) (t2 ⊕ t1) := by
      apply And.intro
      all_goals (rw [Refine]; apply RefineF.choice_idemp)
      on_goal 1 => apply RefineF.choice_right
      on_goal 2 => apply RefineF.choice_left
      on_goal 3 => apply RefineF.choice_right
      on_goal 4 => apply RefineF.choice_left
      all_goals rfl

    theorem zero_left_id [IsRefl _ r] : Eutt r (zero ⊕ t) t := by
      apply And.intro
      all_goals rw [Refine]
      · apply RefineF.choice_idemp
        · exact RefineF.zero
        · rfl
      · apply RefineF.choice_right
        rfl

    theorem zero_right_id [IsRefl _ r] : Eutt r (t ⊕ zero) t := by
      apply And.intro
      all_goals rw [Refine]
      · apply RefineF.choice_idemp
        · rfl
        · exact RefineF.zero
      · apply RefineF.choice_left
        rfl

    theorem choice_assoc [IsRefl _ r] : Eutt r ((t1 ⊕ t2) ⊕ t3) (t1 ⊕ (t2 ⊕ t3)) := by
      apply And.intro
      all_goals rw [Refine]
      · apply RefineF.choice_idemp
        · apply RefineF.choice_idemp
          · apply RefineF.choice_left
            rfl
          · apply RefineF.choice_right
            apply RefineF.choice_left
            rfl
        · apply RefineF.choice_right
          apply RefineF.choice_right
          rfl
      · apply RefineF.choice_idemp
        · apply RefineF.choice_left
          apply RefineF.choice_left
          rfl
        · apply RefineF.choice_idemp
          · apply RefineF.choice_left
            apply RefineF.choice_right
            rfl
          · apply RefineF.choice_right
            rfl

  end Eutt

  instance [IsEquiv _ r] : IsEquiv (CTree ε ρ) (Eutt r) where
     refl := @Eutt.refl _ _ _ _
     trans := Eutt.trans
     symm := Eutt.symm

  instance : HasEquiv (CTree ε ρ) where
    Equiv := Eutt Eq

end CTree
