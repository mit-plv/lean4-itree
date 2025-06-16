import CTree.Basic
import CTree.Monad
import Mathlib.Data.ENat.Basic

namespace CTree
  inductive EuttcF {ε : Type → Type} {ρ σ : Type}
    (r : Rel ρ σ) (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    : ENat → ENat → CTree ε ρ → CTree ε σ → Prop
  | coind {p1 p2 t1 t2} (p1' p2' : ENat)
      (h1 : p1' < p1) (h2 : p2' < p2) (h : sim p1' p2' t1 t2)
      : EuttcF r sim p1 p2 t1 t2
  | ret {x y p1 p2} (h : r x y) : EuttcF r sim p1 p2 (ret x) (ret y)
  | vis {p1 p2} {α : Type} {e : ε α} {k1 : α → CTree ε ρ} {k2 : α → CTree ε σ}
      (h : ∀ a : α, EuttcF r sim ⊤ ⊤ (k1 a) (k2 a)) : EuttcF r sim p1 p2 (vis e k1) (vis e k2)
  | tau_left {p1 p2 t1 t2}
      (h : EuttcF r sim ⊤ p2 t1 t2) : EuttcF r sim p1 p2 t1.tau t2
  | tau_right {p1 p2 t1 t2}
      (h : EuttcF r sim p1 ⊤ t1 t2) : EuttcF r sim p1 p2 t1 t2.tau
  | zero {p1 p2} : EuttcF r sim p1 p2 zero zero
  | choice_left {p1 p2 t1 t2 t3}
      (h1 : EuttcF r sim ⊤ p2 t1 t3)
      (h2 : EuttcF r sim ⊤ p2 t2 t3)
      : EuttcF r sim p1 p2 (t1 ⊕ t2) t3
  | choice_right {p1 p2 t1 t2 t3}
      (h1 : EuttcF r sim p1 ⊤ t1 t2)
      (h2 : EuttcF r sim p1 ⊤ t1 t3)
      : EuttcF r sim p1 p2 t1 (t2 ⊕ t3)

  theorem EuttcF.monotone (r : Rel ρ σ) (sim sim' : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
    (hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → sim' p1 p2 t1 t2)
    {p1 p2 t1 t2} (h : EuttcF r sim p1 p2 t1 t2) : EuttcF r sim' p1 p2 t1 t2 := by
    induction h with
    | coind _ _ h1 h2 h => exact .coind _ _ h1 h2 (hsim _ _ _ _ h)
    | ret h => exact .ret h
    | vis _ ih => exact .vis λ a => ih a
    | tau_left _ ih => exact EuttcF.tau_left ih
    | tau_right _ ih => exact EuttcF.tau_right ih
    | zero => exact .zero
    | choice_left _ _ ih1 ih2 => exact .choice_left ih1 ih2
    | choice_right _ _ ih1 ih2 => exact .choice_right ih1 ih2

  def Euttc' (r : Rel ρ σ) (p1 p2 : ENat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
    EuttcF r (Euttc' r) p1 p2 t1 t2
    greatest_fixpoint monotonicity by
      intro _ _ hsim _ _ _ _ h
      apply EuttcF.monotone (hsim := hsim) (h := h)

  abbrev Euttc (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) :=
    ∃ p1 p2, Euttc' r p1 p2 t1 t2

  @[refl]
  theorem Euttc.refl {r : Rel ρ ρ} [IsRefl ρ r] : Euttc r t t :=
    sorry

  @[symm]
  theorem Euttc.symm {r : Rel ρ σ} (h : Euttc r t1 t2) : Euttc (flip r) t2 t1 :=
    sorry

  @[trans]
  theorem Euttc.trans (h1 : Euttc r1 t1 t2) (h2 : Euttc r2 t2 t3) : Euttc (r1.comp r2) t1 t3 :=
    sorry

  instance : HasEquiv (CTree ε ρ) where
    Equiv := Euttc Eq

  @[refl]
  theorem Euttc.eq_refl {t : CTree ε ρ} : t ≈ t :=
    sorry

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
      sorry

    theorem choice_idemp_self {t : CTree ε ρ} : (t ⊕ t) ≈ t :=
      choice_idemp refl refl

    theorem choice_comm {t1 t2 : CTree ε ρ} : (t1 ⊕ t2) ≈ (t2 ⊕ t1) :=
      sorry

    theorem zero_left_id (h : t1 ≈ t2) : (zero ⊕ t1) ≈ t2 :=
      sorry

    theorem zero_right_id (h : t1 ≈ t2) : (t1 ⊕ zero) ≈ t2 :=
      sorry

    theorem choice_assoc {t1 t2 t3 : CTree ε ρ} : ((t1 ⊕ t2) ⊕ t3) ≈ (t1 ⊕ (t2 ⊕ t3)) :=
      sorry

    theorem congr_map {t1 t2 : CTree ε ρ} {f : ρ → σ} (h : t1 ≈ t2) : t1.map f ≈ t2.map f :=
      sorry

    theorem map_trans {t1 t2 : CTree ε ρ} {t3 : CTree ε σ} {f : ρ → σ}
      (h1 : t1 ≈ t2) (h2 : t2.map f ≈ t3) : t1.map f ≈ t3 :=
      sorry

    theorem vis_eq {e : ε α} {k1 k2 : α → CTree ε ρ}
      (h : ∀ a, k1 a ≈ k2 a) : vis e k1 ≈ vis e k2 :=
      sorry

  end Euttc

end CTree
