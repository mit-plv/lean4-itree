import CTree.Basic
import CTree.Trace

namespace CTree

  def TraceEq (t1 t2 : CTree ε ρ) : Prop :=
    t1 ≤ t2 ∧ t2 ≤ t1

  instance : HasEquiv (CTree ε ρ) where
    Equiv := TraceEq

  namespace TraceEq
    @[refl]
    theorem refl {t : CTree ε ρ} : t ≈ t :=
      ⟨.refl, .refl⟩

    @[symm]
    theorem symm {t1 t2 : CTree ε ρ} : t1 ≈ t2 → t2 ≈ t1 :=
      λ ⟨l, r⟩ => ⟨r, l⟩

    @[trans]
    theorem trans {t1 t2 t3 : CTree ε ρ} (h1 : t1 ≈ t2) (h2 : t2 ≈ t3) : t1 ≈ t3 :=
      ⟨.trans h1.left h2.left, .trans h2.right h1.right⟩

    instance instCTreeIsEquiv : IsEquiv (CTree ε ρ) TraceEq where
      refl _ := refl
      trans _ _ _ := trans
      symm _ _ := symm

    theorem choice_idemp {t1 t2 t3 : CTree ε ρ}
      (h1 : t1 ≈ t3) (h2 : t2 ≈ t3) : (t1 ⊕ t2) ≈ t3 :=
      ⟨.choice_idemp h1.left h2.left, .choice_left h1.right⟩

    theorem choice_idemp_self {t : CTree ε ρ} : (t ⊕ t) ≈ t :=
      choice_idemp refl refl

    theorem choice_comm {t1 t2 : CTree ε ρ} : (t1 ⊕ t2) ≈ (t2 ⊕ t1) :=
      ⟨.choice_idemp (.choice_right .refl) (.choice_left .refl), .choice_idemp (.choice_right .refl) (.choice_left .refl)⟩

    theorem zero_left_id : (zero ⊕ t) ≈ t :=
      ⟨.choice_idemp .zero_le .refl, .choice_right .refl⟩

    theorem zero_right_id : (t ⊕ zero) ≈ t :=
      ⟨.choice_idemp .refl .zero_le, .choice_left .refl⟩

    theorem choice_assoc {t1 t2 t3 : CTree ε ρ} : ((t1 ⊕ t2) ⊕ t3) ≈ (t1 ⊕ (t2 ⊕ t3)) :=
      ⟨
        .choice_idemp
          (.choice_idemp (.choice_left .refl) (.choice_right <| .choice_left .refl))
          (.choice_right <| .choice_right .refl),
        .choice_idemp
          (.choice_left <| .choice_left .refl)
          (.choice_idemp (.choice_left <| .choice_right .refl) (.choice_right .refl))
      ⟩

    theorem map_eq {t1 t2 : CTree ε ρ} (h1 : t1 ≈ t2) (h2 : f <$> t2 ≈ t3) : f <$> t1 ≈ t3 := by
      sorry
  end TraceEq

end CTree
