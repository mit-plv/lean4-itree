import CTree.Par
import CTree.Paco

namespace CTree
  inductive IsParR (t : CTree ε β) (t1 : CTree ε α) (t2 : CTree ε β) : Prop
    | lS : t = map Prod.snd (parAux (t1 ◁ t2)) → IsParR t t1 t2
    | rS : t = map Prod.snd (parAux (t1 ▷ t2)) → IsParR t t1 t2
    | lrS : t = map Prod.snd (parAux (t1 ◁▷ t2)) → IsParR t t1 t2
    | bothS : t = map Prod.snd (parAux (t1 ⋈ t2)) → IsParR t t1 t2
    | parS : t = map Prod.snd (parAux (t1 ‖ₛ t2)) → IsParR t t1 t2

  namespace Euttc
    macro "crush_refine" : tactic => `(tactic|(
      repeat first
      | exact RefineF.ret rfl
      | exact RefineF.zero
      | apply RefineF.tau_left
      | apply RefineF.tau_right
      | apply RefineF.vis
      | apply RefineF.choice_idemp
      | apply RefineF.choice_idemp
      | apply RefineF.coind 0 0 ENat.top_pos ENat.top_pos
    ))

    macro "crush_parR_ret " c:term : tactic => `(tactic|(
      repeat apply And.intro rfl _
      exists $c
      apply And.intro _ rfl
      solve
      | exact IsParR.bothS rfl
      | exact IsParR.rS rfl
      | exact IsParR.parS rfl
    ))

    macro "parR_ret_left_lS " t2:term : tactic => `(tactic|(
      apply dMatchOn $t2
      all_goals
        intros; rename_i heq; subst heq
        simp only [parAux_lS_ret, map_zero]
        crush_refine
    ))

    macro "parR_ret_left_rS " t2:term : tactic => `(tactic|(
      apply dMatchOn $t2
      · intro y heq
        subst heq
        simp only [parAux_rS_ret_ret, map_zero]
        crush_refine
      · intro c heq
        subst heq
        simp only [parAux_rS_ret_tau, map_tau]
        crush_refine; crush_parR_ret c
      · intro α e k heq
        subst heq
        simp only [parAux_rS_ret_vis, map_vis]
        crush_refine; intro a
        crush_refine; crush_parR_ret k a
      · intro heq
        subst heq
        simp only [parAux_rS_ret_zero, map_zero]
        crush_refine
      · intro c1 c2 heq
        subst heq
        simp only [parAux_rS_ret_choice, map_choice]
        crush_refine
        · apply RefineF.choice_left
          crush_refine; crush_parR_ret c1
        · apply RefineF.choice_right
          crush_refine; crush_parR_ret c2
    ))

    theorem parR_ret_le : ((ret x) ‖→ t) ≤Eq≤ t := by
      apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ ∃ t, IsParR t1 (ret x) t ∧ t2 = t) _ 0 0
      · crush_parR_ret t
      · intro p1 p2 t1 t2 ⟨hp1, hp2, t, ht1, ht2⟩
        subst hp1 hp2 ht2
        match ht1 with
        | .lS heq =>
          subst heq
          parR_ret_left_lS t2
        | .rS heq =>
          subst heq
          parR_ret_left_rS t2
        | .lrS heq =>
          subst heq
          simp only [parAux_lrS, map_choice]
          apply RefineF.choice_idemp
          · parR_ret_left_lS t2
          · parR_ret_left_rS t2
        | .bothS heq =>
          subst heq
          apply dMatchOn t2
          · intro v heq
            subst heq
            simp only [parAux_bothS_ret_ret, map_ret]
            crush_refine
          · intro c heq
            subst heq
            simp only [parAux_bothS_ret_tau, map_tau]
            repeat (crush_refine; crush_parR_ret c)
          · intro α e k heq
            subst heq
            simp only [parAux_bothS_ret_vis, map_zero]
            crush_refine
          · intro heq
            subst heq
            simp only [parAux_bothS_ret_zero, map_zero]
            crush_refine
          · intro c1 c2 heq
            subst heq
            simp only [parAux_bothS_ret_choice, map_choice]
            crush_refine
            · apply RefineF.choice_left
              crush_refine; crush_parR_ret c1
            · apply RefineF.choice_right
              crush_refine; crush_parR_ret c2
        | .parS heq =>
          subst heq
          apply dMatchOn t2
          · intro v heq
            subst heq
            simp only [parAux_parS_ret_ret, map_choice, map_ret, map_zero]
            crush_refine
          · intro c heq
            subst heq
            simp only [parAux_parS_ret_tau, map_choice, map_tau, map_zero]
            repeat (crush_refine; crush_parR_ret c)
          · intro α e k heq
            subst heq
            simp only [parAux_parS_ret_vis, map_choice, map_zero, map_vis]
            crush_refine
            intro a
            crush_refine; crush_parR_ret k a
          · intro heq
            subst heq
            simp only [parAux_parS_ret_zero, map_choice, map_zero]
            crush_refine
          · intro c1 c2 heq
            subst heq
            simp only [parAux_parS_ret_choice, map_choice, map_zero]
            crush_refine
            · apply RefineF.choice_left
              crush_refine; crush_parR_ret c1
            · apply RefineF.choice_right
              crush_refine; crush_parR_ret c2
            · crush_refine
              · apply RefineF.choice_left
                crush_refine; crush_parR_ret c1
              · apply RefineF.choice_right
                crush_refine; crush_parR_ret c2

    -- set_option pp.explicit true
    theorem le_parR_ret : t ≤Eq≤ ((ret (ρ := ρ) x) ‖→ t) := by
      exists 0, 0
      revert t x
      pcofix
      intros
      pfold
      sorry

    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · exact parR_ret_le
      · rw [flip_eq]
        exact le_parR_ret

    macro "crush_parR_map_both_le " t1:term ", " t2:term : tactic => `(tactic|(
      repeat apply And.intro rfl _
      exists $t1, $t2
      try simp only [map_ret, and_self]
    ))

    macro "simp_parAux_bothS" : tactic => `(tactic|(
      simp only [
        parAux_bothS_ret_ret, parAux_bothS_ret_vis, parAux_bothS_ret_tau, parAux_bothS_ret_zero, parAux_bothS_ret_choice,
        parAux_bothS_vis_ret, parAux_bothS_vis_vis, parAux_bothS_vis_tau, parAux_bothS_vis_zero, parAux_bothS_vis_choice,
        parAux_bothS_tau_ret, parAux_bothS_tau_vis, parAux_bothS_tau_tau, parAux_bothS_tau_zero, parAux_bothS_tau_choice,
        parAux_bothS_zero_ret, parAux_bothS_zero_vis, parAux_bothS_zero_tau, parAux_bothS_zero_zero, parAux_bothS_zero_choice,
        parAux_bothS_choice_ret, parAux_bothS_choice_vis, parAux_bothS_choice_tau, parAux_bothS_choice_zero, parAux_bothS_choice_choice,
        map_vis, map_ret, map_tau, map_zero, map_choice
      ]
    ))

    open Lean

    macro "crush_match" t:term " with " simp_rule:tactic : tactic => `(tactic|(
      apply dMatchOn $t
      case' ret =>
        intro $(mkIdent `y) heq
        subst heq
      case' vis =>
        intro $(mkIdent `α2) $(mkIdent `e2) $(mkIdent `k2) heq
        subst heq
      case' tau =>
        intro $(mkIdent `t2) heq
        subst heq
      case' zero =>
        intro heq
        subst heq
      case' choice =>
        intro $(mkIdent `c21) $(mkIdent `c22) heq
        subst heq
      all_goals try ($simp_rule; crush_refine)
    ))

    theorem parR_map_both_le : map Prod.snd (parAux (map f t1 ⋈ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ⋈ t2)) := by
      apply Refine.coind
        (λ p1 p2 t1 t2 =>
          p1 = 0 ∧ p2 = 0 ∧ ∃ t1' t2', t1 = map Prod.snd (parAux (map f t1' ⋈ t2')) ∧ t2 = map Prod.snd (parAux (t1' ⋈ t2'))
        ) _ 0 0
      · crush_parR_map_both_le t1, t2
      · intro p1 p2 t1' t2' ⟨hp1, hp2, t1, t2, ht1, ht2⟩
        subst hp1 hp2 ht1 ht2
        apply dMatchOn t1
        · intro x heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le ret x, c21
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le ret x, c22
          · crush_parR_map_both_le ret x, t2
        · intro t1 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · crush_parR_map_both_le t1, c21 ⊕ c22
          · crush_parR_map_both_le t1, zero
          · crush_parR_map_both_le t1, tau t2
          · crush_parR_map_both_le t1, vis e2 k2
          · crush_parR_map_both_le t1, ret y
        · intro α1 e1 k1 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          all_goals rw [←map_vis (e := e1) (k := k1) (f := f)]
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le vis e1 k1, c21
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le vis e1 k1, c22
          · crush_parR_map_both_le vis e1 k1, t2
        · intro heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le zero, c21
            simp only [map_zero, and_self]
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le zero, c22
            simp only [map_zero, and_self]
          · crush_parR_map_both_le zero, t2
            simp only [map_zero, and_self]
        · intro c11 c12 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, c21 ⊕ c22
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, c21 ⊕ c22
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, zero
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, zero
          · rw [←map_choice (c1 := c11) (c2 := c12) (f := f)]
            crush_parR_map_both_le c11 ⊕ c12, t2
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, vis e2 k2
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, vis e2 k2
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, ret y
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, ret y

    -- theorem parR_map_lS_le : map Prod.snd (parAux (map f t1 ◁ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ◁ t2)) := by
    --   apply Refine.coind
    --     (λ p1 p2 t1 t2 =>
    --       p1 = 0 ∧ p2 = 0 ∧ ∃ t1' t2', t1 = map Prod.snd (parAux (map f t1' ◁ t2')) ∧ t2 = map Prod.snd (parAux (t1' ◁ t2'))
    --     ) _ 0 0
    --   · repeat apply And.intro rfl _
    --     exists t1, t2
    --   · intro p1 p2 t1' t2' ⟨hp1, hp2, t1, t2, ht1, ht2⟩
    --     subst hp1 hp2 ht1 ht2
    --     apply dMatchOn t1
    --     case vis =>
    --       intro α e k heq
    --       subst heq
    --       simp only [parAux_lS_vis, map_vis]
    --       crush_refine
    --       intro a
    --       -- TODO: this cannot be separated out into a separate lemma. Need to prove this with in the greater par lemma.
    --       sorry
    --     all_goals sorry

    -- theorem parR_map_rS_le : map Prod.snd (parAux (map f t1 ▷ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ▷ t2)) := by
    --   sorry

    -- theorem parR_map_lrS_le : map Prod.snd (parAux (map f t1 ◁▷ t2)) ≤Eq≤ map Prod.snd (parAux (t1 ◁▷ t2)) := by
    --   simp only [parAux_lrS, map_choice]
    --   apply Refine.choice_idemp
    --   · apply Refine.choice_left
    --     exact parR_map_lS_le
    --   · apply Refine.choice_right
    --     exact parR_map_rS_le

    theorem parR_map_le : ((map f t1) ‖→ t2) ≤Eq≤ (t1 ‖→ t2) := by
      simp only [parR, par, Functor.map, parAux_parS, map_choice]
      sorry
      -- apply Refine.choice_idemp
      -- · apply Refine.choice_left
      --   exact parR_map_both_le
      -- · apply Refine.choice_right
      --   exact parR_map_lrS_le

    theorem le_parR_map : (t1 ‖→ t2) ≤Eq≤ ((map f t1) ‖→ t2) := by
      simp only [parR, par, Functor.map, parAux_parS, map_choice]
      sorry

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      apply And.intro
      · exact parR_map_le
      · rw [flip_eq]
        exact le_parR_map

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
