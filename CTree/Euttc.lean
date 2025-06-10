import CTree.Refinement

namespace CTree
  /--
  Equivalent up to tau and choice.
  -/
  def Euttc (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    t1 ≤r≤ t2 ∧ t2 ≤flip r≤ t1

  @[refl]
  theorem Euttc.refl {r : Rel ρ ρ} [IsRefl ρ r] : Euttc r t t :=
    ⟨.refl _, .refl _⟩

  @[symm]
  theorem Euttc.symm {r : Rel ρ σ} (h : Euttc r t1 t2) : Euttc (flip r) t2 t1 :=
    ⟨h.2, h.1⟩

  @[trans]
  theorem Euttc.trans (h1 : Euttc r1 t1 t2) (h2 : Euttc r2 t2 t3) : Euttc (r1.comp r2) t1 t3 :=
    have heq : Rel.comp (flip r2) (flip r1) = flip (r1.comp r2) := by
      funext x y
      simp only [Rel.comp, flip, eq_iff_iff]
      apply Iff.intro
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {exact left
          }
          · simp_all only
      · intro a
        obtain ⟨w, h⟩ := a
        obtain ⟨left, right⟩ := h
        apply Exists.intro
        · apply And.intro
          on_goal 2 => {exact left
          }
          · simp_all only
    ⟨.trans h1.1 h2.1, heq ▸ .trans h2.2 h1.2⟩

  instance : HasEquiv (CTree ε ρ) where
    Equiv := Euttc Eq

  @[refl]
  theorem Euttc.eq_refl {t : CTree ε ρ} : t ≈ t :=
    ⟨.refl _, .refl _⟩

  @[symm]
  theorem Euttc.eq_symm {t1 t2 : CTree ε ρ} (h : t1 ≈ t2) : t2 ≈ t1 := by
    have := Euttc.symm h
    rw [flip_eq] at this
    exact this

  @[trans]
  theorem Euttc.eq_trans {t1 t2 t3 : CTree ε ρ} (h1 : t1 ≈ t2) (h2 : t2 ≈ t3) : t1 ≈ t3 := by
    have := Euttc.trans h1 h2
    rw [Rel.comp_right_id] at this
    exact this

  instance : IsEquiv (CTree ε ρ) (Euttc Eq) where
    refl _ := Euttc.eq_refl
    symm _ _ := Euttc.eq_symm
    trans _ _ _ := Euttc.eq_trans

  namespace Euttc
    theorem choice_idemp (h1 : Euttc r t1 t3) (h2 : Euttc r t2 t3) : Euttc r (t1 ⊕ t2) t3 :=
      ⟨.choice_idemp h1.1 h2.1, .choice_left h1.2⟩

    theorem choice_idemp_self {t : CTree ε ρ} : (t ⊕ t) ≈ t :=
      choice_idemp refl refl

    theorem choice_comm {t1 t2 : CTree ε ρ} : (t1 ⊕ t2) ≈ (t2 ⊕ t1) :=
      ⟨
        .choice_idemp (.choice_right <| .refl _) (.choice_left <| .refl _),
        .choice_idemp (.choice_right <| .refl _) (.choice_left <| .refl _)
      ⟩

    theorem zero_left_id (h : t1 ≈ t2) : (zero ⊕ t1) ≈ t2 :=
      ⟨.choice_idemp .zero_le <| h.1, .choice_right <| h.2⟩

    theorem zero_right_id (h : t1 ≈ t2) : (t1 ⊕ zero) ≈ t2 :=
      ⟨.choice_idemp h.1 .zero_le, .choice_left <| h.2⟩

    theorem choice_assoc {t1 t2 t3 : CTree ε ρ} : ((t1 ⊕ t2) ⊕ t3) ≈ (t1 ⊕ (t2 ⊕ t3)) :=
      ⟨
        .choice_idemp
          (.choice_idemp (.choice_left <| .refl _) (.choice_right <| .choice_left <| .refl _))
          (.choice_right <| .choice_right <| .refl _),
        .choice_idemp
          (.choice_left <| .choice_left <| .refl _)
          (.choice_idemp (.choice_left <| .choice_right <| .refl _) (.choice_right <| .refl _))
      ⟩

    theorem congr_map {t1 t2 : CTree ε ρ} {f : ρ → σ} (h : t1 ≈ t2) : t1.map f ≈ t2.map f :=
      ⟨
        .congr_map h.1,
        by
          have := Refine.congr_map (f := f) (flip_eq (r := Eq) ▸ h.2)
          rw [flip_eq]
          exact this
      ⟩

    theorem map_trans {t1 t2 : CTree ε ρ} {t3 : CTree ε σ} {f : ρ → σ}
      (h1 : t1 ≈ t2) (h2 : t2.map f ≈ t3) : t1.map f ≈ t3 :=
      .eq_trans h1.congr_map h2

  end Euttc

end CTree
