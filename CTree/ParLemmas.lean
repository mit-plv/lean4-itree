import CTree.Par
import CTree.Refinement
import CTree.Paco

namespace CTree
  inductive IsParR (t : CTree ε β) (t1 : CTree ε α) (t2 : CTree ε β) : Prop
    | lS : t = map Prod.snd (parAux (t1 ◁ t2)) → IsParR t t1 t2
    | rS : t = map Prod.snd (parAux (t1 ▷ t2)) → IsParR t t1 t2
    | lrS : t = map Prod.snd (parAux (t1 ◁▷ t2)) → IsParR t t1 t2
    | bothS : t = map Prod.snd (parAux (t1 ⋈ t2)) → IsParR t t1 t2
    | parS : t = map Prod.snd (parAux (t1 ‖ₛ t2)) → IsParR t t1 t2

  namespace Euttc
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

    theorem parR_ret_le : ((ret x) ‖→ t) ≤ t := by
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
            simp only [parAux_bothS_ret_tau, map_zero]
            crush_refine
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
            crush_parR_ret k a
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
    theorem le_parR_ret : t ≤ ((ret (ρ := ρ) x) ‖→ t) := by
      exists 0, 0
      revert t x
      pcofix
      intros
      pfold
      sorry

    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      sorry

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

    syntax "crush_match" term (" with " tactic)? : tactic
    open Lean in
    macro_rules
      | `(tactic|crush_match $t $[ with $simp_rule]?) => do
        let simp_rule ←
          match simp_rule with
          | some simp_rule => `(tactic|(
              all_goals try ($simp_rule; crush_refine)
            ))
          | none => `(tactic|skip)
        `(tactic|(
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
          $simp_rule
        ))

    theorem parR_map_both_le : map Prod.snd (parAux (map f t1 ⋈ t2)) ≤ map Prod.snd (parAux (t1 ⋈ t2)) := by
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
        · intro t1 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            have := (map_tau (f := f) (c := t1)).symm
            simp only [this]
            crush_refine
            crush_parR_map_both_le t1.tau, c21
          · apply RefineF.choice_right
            have := (map_tau (f := f) (c := t1)).symm
            simp only [this]
            crush_refine
            crush_parR_map_both_le t1.tau, c22
        · intro α1 e1 k1 heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          all_goals rw [←map_vis (e := e1) (k := k1) (f := f)]
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le vis e1 k1, c21
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le vis e1 k1, c22
        · intro heq
          subst heq
          crush_match t2 with simp_parAux_bothS
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le zero, c21
            simp only [map_zero, and_self]
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le zero, c22
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
          · apply RefineF.choice_left
            crush_refine
            crush_parR_map_both_le c11, t2.tau
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, t2.tau
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, vis e2 k2
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, vis e2 k2
          · apply RefineF.choice_left
            crush_refine; crush_parR_map_both_le c11, ret y
          · apply RefineF.choice_right
            crush_refine; crush_parR_map_both_le c12, ret y

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
