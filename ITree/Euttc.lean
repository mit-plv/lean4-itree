-- import CTree.Basic
-- import CTree.Monad
-- import CTree.Refinement
-- import Mathlib.Data.ENat.Basic

-- namespace CTree
--   def EuttcF {ε : Type u → Type v} {ρ : Type w1} {σ : Type w2}
--     (r : Rel ρ σ) (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
--     (p1 p2 : ENat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
--     RefineF r sim p1 p2 t1 t2 ∧
--       RefineF (flip r) (λ p1 p2 t1 t2 => sim p2 p1 t2 t1) p2 p1 t2 t1

--   theorem EuttcF.monotone (r : Rel ρ σ) (sim sim' : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
--     (hsim : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → sim' p1 p2 t1 t2)
--     {p1 p2 t1 t2} (h : EuttcF r sim p1 p2 t1 t2) : EuttcF r sim' p1 p2 t1 t2 := by
--     have ⟨hl, hr⟩ := h
--     apply And.intro
--     · apply RefineF.monotone <;> assumption
--     · apply RefineF.monotone <;> try assumption
--       intro p1 p2 t1 t2 hs
--       simp_all only

--   def Euttc' (r : Rel ρ σ) (p1 p2 : ENat) (t1 : CTree ε ρ) (t2 : CTree ε σ) : Prop :=
--     EuttcF r (Euttc' r) p1 p2 t1 t2
--     coinductive_fixpoint monotonicity by
--       intro _ _ hsim _ _ _ _ h
--       apply EuttcF.monotone (hsim := hsim) (h := h)

--   abbrev Euttc (r : Rel ρ σ) (t1 : CTree ε ρ) (t2 : CTree ε σ) :=
--     ∃ p1 p2, Euttc' r p1 p2 t1 t2

--   theorem EuttcF.idx_mono
--     {sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop}
--     {t1 : CTree ε ρ} {t2 : CTree ε σ}
--     {p1' p1 p2' p2 : ENat} (h1 : p1' ≤ p1) (h2 : p2' ≤ p2) (h : EuttcF r sim p1' p2' t1 t2)
--     : EuttcF r sim p1 p2 t1 t2 := by
--     apply And.intro
--     · exact RefineF.idx_mono h1 h2 h.left
--     · exact RefineF.idx_mono h2 h1 h.right

--   theorem EuttcF.idx_irrelevance {p1 p2} {t1 : CTree ε ρ} {t2 : CTree ε σ}
--     (h : EuttcF r (Euttc' r) p1 p2 t1 t2)
--     : ∀ p1' p2', EuttcF r (Euttc' r) p1' p2' t1 t2 := by
--     intro p1' p2'
--     apply And.intro
--     · apply RefineF.idx_irrelevance_gen h.left
--       intro p1 p2 t1 t2 h
--       simp only [Euttc'] at h
--       exact h.left
--     · apply RefineF.idx_irrelevance_gen h.right
--       intro p1 p2 t1 t2 h
--       simp only [Euttc'] at h
--       exact h.right

--   theorem EuttcF.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
--     (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → EuttcF r sim p1 p2 t1 t2)
--     (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : EuttcF r (Euttc' r) p1 p2 t1 t2 := by
--     have := Euttc'.coinduct r sim adm p1 p2 t1 t2 h
--     rw [Euttc'] at this
--     exact this

--   theorem Euttc'.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
--     (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → EuttcF r sim p1 p2 t1 t2)
--     (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : Euttc' r p1 p2 t1 t2 :=
--     Euttc'.coinduct r sim adm p1 p2 t1 t2 h

--   theorem Euttc.coind (sim : ENat → ENat → CTree ε ρ → CTree ε σ → Prop)
--     (adm : ∀ p1 p2 t1 t2, sim p1 p2 t1 t2 → EuttcF r sim p1 p2 t1 t2)
--     (p1 p2 : ENat) {t1 : CTree ε ρ} {t2 : CTree ε σ} (h : sim p1 p2 t1 t2) : Euttc r t1 t2 :=
--     ⟨p1, p2, Euttc'.coinduct r sim adm p1 p2 t1 t2 h⟩

--   @[refl]
--   theorem Euttc.refl {r : Rel ρ ρ} [IsRefl ρ r] : Euttc r t t := by
--     apply Euttc.coind (fun p1 p2 t1 t2 => ∃ t, t1 = t ∧ t2 = t) _ 0 0
--     · exists t
--     · intro p1 p2 _ t ⟨_, ht1, ht2⟩
--       subst ht1 ht2
--       ctree_match t
--       case ret =>
--         apply And.intro
--         <;> exact RefineF.ret (IsRefl.refl v)
--       case tau =>
--         apply And.intro <;> (crush_refine; exists t)
--       case vis =>
--         apply And.intro <;> (crush_refine; intro a; exists k a)
--       case zero =>
--         apply And.intro <;> crush_refine
--       case choice =>
--         apply And.intro
--         all_goals
--           crush_refine
--           · apply RefineF.choice_left
--             crush_refine
--             exists cl
--           · apply RefineF.choice_right
--             crush_refine
--             exists cr

--   theorem EuttcF.dest_tau_left
--     (h : EuttcF r (Euttc' r) p1 p2 t1.tau t2) : EuttcF (flip r) (Euttc' r) p1 p2 t1 t2 := by

--     sorry

--   theorem Euttc'.flip_iff : Euttc' r p1 p2 t1 t2 ↔ Euttc' (flip r) p2 p1 t2 t1 := by
--     apply Iff.intro
--     · intro h
--       apply Euttc'.coind (fun p1 p2 t1 t2 => Euttc' r p2 p1 t2 t1) _ _ _ h
--       intro p1 p2 t1 t2 h
--       simp_all only [Euttc']
--       apply And.intro
--       · induction h.right with
--         | coind p1' p2' hp1 hp2 h =>
--           apply RefineF.coind p1' p2' hp1 hp2
--           exact EuttcF.idx_irrelevance h _ _
--         | ret hxy => exact RefineF.ret hxy
--         | vis hk =>
--           apply RefineF.vis
--           intro a
--           simp only [Euttc'] at hk
--           exact hk a
--         | tau_left _ ih =>

--           sorry
--         | tau_right => sorry
--         | zero => sorry
--         | choice_left => sorry
--         | choice_right => sorry
--         | choice_idemp => sorry
--       · sorry
--     · sorry

--   -- theorem EuttcF.flip_or_swapped
--   --   (h : EuttcF r (Euttc' r) p2 p1 t2 t1) : EuttcF (flip r) (Euttc' r) p1 p2 t1 t2 := by
--   --   apply EuttcF.coind (r := flip r) (λ p1 p2 t1 t2 => EuttcF (r) (Euttc' r) p2 p1 t2 t1)
--   --   apply And.intro
--   --   · induction h.right with
--   --     | coind p1' p2' hp1 hp2 h =>
--   --       have := h.right
--   --       sorry
--   --     | ret hxy =>
--   --       exact RefineF.ret hxy
--   --     | vis cih =>
--   --       apply RefineF.vis
--   --       · intro a

--   --         sorry
--   --       sorry
--   --     | tau_left => sorry
--   --     | tau_right => sorry
--   --     | zero => sorry
--   --     | choice_left => sorry
--   --     | choice_right => sorry
--   --     | choice_idemp => sorry
--   --   sorry

--   theorem RefineF.flip_euttc
--     (h : RefineF (flip r) (fun p1 p2 t1 t2 => Euttc' r p2 p1 t2 t1) p2 p1 t2 t1)
--     : RefineF (flip r) (Euttc' (flip r)) p2 p1 t2 t1 := by
--     induction h with
--     | coind p1' p2' hp1 hp2 h =>
--       apply RefineF.coind p1' p2' hp1 hp2
--       sorry
--     | ret => sorry
--     | vis => sorry
--     | tau_left => sorry
--     | tau_right => sorry
--     | zero => sorry
--     | choice_left => sorry
--     | choice_right => sorry
--     | choice_idemp => sorry

--   @[symm]
--   theorem Euttc.symm {r : Rel ρ σ} (h : Euttc r t1 t2) : Euttc (flip r) t2 t1 := by
--     simp only [Euttc, Euttc'] at *
--     obtain ⟨p1, p2, hl, hr⟩ := h
--     exists p2, p1
--     apply And.intro
--     ·

--       sorry
--     · sorry

--   @[trans]
--   theorem Euttc.trans (h1 : Euttc r1 t1 t2) (h2 : Euttc r2 t2 t3) : Euttc (r1.comp r2) t1 t3 :=
--     sorry

--   instance : HasEquiv (CTree ε ρ) where
--     Equiv := Euttc Eq

--   @[refl]
--   theorem Euttc.eq_refl {t : CTree ε ρ} : t ≈ t :=
--     Euttc.refl

--   @[symm]
--   theorem Euttc.eq_symm {t1 t2 : CTree ε ρ} (h : t1 ≈ t2) : t2 ≈ t1 := by
--     have := Euttc.symm h
--     rw [flip_eq] at this
--     exact this

--   @[trans]
--   theorem Euttc.eq_trans {t1 t2 t3 : CTree ε ρ} (h1 : t1 ≈ t2) (h2 : t2 ≈ t3) : t1 ≈ t3 := by
--     have := Euttc.trans h1 h2
--     rw [Rel.comp_right_id] at this
--     exact this

--   instance : IsEquiv (CTree ε ρ) (Euttc Eq) where
--     refl _ := Euttc.eq_refl
--     symm _ _ := Euttc.eq_symm
--     trans _ _ _ := Euttc.eq_trans

--   namespace Euttc
--     theorem choice_idemp (h1 : Euttc r t1 t3) (h2 : Euttc r t2 t3) : Euttc r (t1 ⊕ t2) t3 :=
--       sorry

--     theorem choice_idemp_self {t : CTree ε ρ} : (t ⊕ t) ≈ t :=
--       choice_idemp refl refl

--     theorem choice_comm {t1 t2 : CTree ε ρ} : (t1 ⊕ t2) ≈ (t2 ⊕ t1) :=
--       sorry

--     theorem zero_left_id (h : t1 ≈ t2) : (zero ⊕ t1) ≈ t2 :=
--       sorry

--     theorem zero_right_id (h : t1 ≈ t2) : (t1 ⊕ zero) ≈ t2 :=
--       sorry

--     theorem choice_assoc {t1 t2 t3 : CTree ε ρ} : ((t1 ⊕ t2) ⊕ t3) ≈ (t1 ⊕ (t2 ⊕ t3)) :=
--       sorry

--     theorem congr_map {t1 t2 : CTree ε ρ} {f : ρ → σ} (h : t1 ≈ t2) : t1.map f ≈ t2.map f :=
--       sorry

--     theorem map_trans {t1 t2 : CTree ε ρ} {t3 : CTree ε σ} {f : ρ → σ}
--       (h1 : t1 ≈ t2) (h2 : t2.map f ≈ t3) : t1.map f ≈ t3 :=
--       sorry

--     theorem vis_eq {e : ε α} {k1 k2 : α → CTree ε ρ}
--       (h : ∀ a, k1 a ≈ k2 a) : vis e k1 ≈ vis e k2 :=
--       sorry

--   end Euttc

-- end CTree
