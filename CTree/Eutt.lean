import CTree.Basic
import CTree.Refinement

namespace CTree

  def Eutt (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    t1 ⊑r⊑ t2 ∧ t2 ⊑(flip r)⊑ t1

  namespace Eutt
    @[refl]
    theorem refl {r : Rel ρ ρ} [IsRefl _ r] {t : CTree ε ρ} : Eutt r t t :=
      ⟨.refl _, .refl _⟩

    @[symm]
    theorem symm {r : Rel ρ ρ} [IsSymm _ r] {t1 t2 : CTree ε ρ} : Eutt r t1 t2 → Eutt r t2 t1 := by
      intro h
      have flip_eq := (flip_eq_iff (r := r)).mpr (λ x y h => IsSymm.symm x y h)
      obtain ⟨h1, h2⟩ := h
      apply And.intro
      · rw [flip_eq] at h2
        exact h2
      · rw [flip_eq]
        exact h1

    @[trans]
    theorem trans {r : Rel ρ ρ} [IsRefl _ r] [IsTrans _ r] {t1 t2 t3 : CTree ε ρ} (h1 : Eutt r t1 t2) (h2 : Eutt r t2 t3) : Eutt r t1 t3 :=
      ⟨(Rel.comp_self (r := r)) ▸ .trans h1.left h2.left, (Rel.comp_self (r := flip r)) ▸ .trans h2.right h1.right⟩

    theorem choice_idemp {t1 t2 : CTree ε ρ} {t3 : CTree ε σ} (h1 : Eutt r t1 t3) (h2 : Eutt r t2 t3)
      : Eutt r (t1 ⊕ t2) t3 := by
      sorry

    theorem choice_idemp_self [IsRefl _ r] : Eutt r (t ⊕ t) t :=
      choice_idemp refl refl

    theorem choice_comm {r : Rel ρ ρ} [IsRefl _ r] {t1 t2 : CTree ε ρ} : Eutt r (t1 ⊕ t2) (t2 ⊕ t1) := by
      sorry

    theorem zero_left_id [IsRefl _ r] : Eutt r (zero ⊕ t) t := by
      sorry

    theorem zero_right_id [IsRefl _ r] : Eutt r (t ⊕ zero) t := by
      sorry

    theorem choice_assoc [IsRefl _ r] : Eutt r ((t1 ⊕ t2) ⊕ t3) (t1 ⊕ (t2 ⊕ t3)) := by
      sorry

  end Eutt

  instance {r : Rel ρ ρ} [IsEquiv _ r] : IsEquiv (CTree ε ρ) (Eutt r) where
     refl _ := Eutt.refl
     trans _ _ _ := Eutt.trans
     symm _ _ := Eutt.symm

  instance : HasEquiv (CTree ε ρ) where
    Equiv := Eutt Eq

end CTree
