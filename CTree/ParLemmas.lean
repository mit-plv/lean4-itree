import CTree.Par

namespace CTree
  theorem parAux_parS_ret_tau_eq {v : α} {t : CTree ε β}
    : parAux (.parS (ret v) t.tau)
      = (parAux (ParState.bothS (ret v) t)).tau
        ⊕ zero
        ⊕ (parAux (ParState.rS (ret v) t)).tau := by
    conv =>
      lhs
      rw [parAux_eq_def, parAux_def]
      rw [parAux_eq_def, parAux_def]
      arg 1; arg 2
      simp only [ret, mk, ret', PFunctor.M.dest_mk]
    conv =>
      arg 1; arg 1; arg 3
      simp only [tau, mk, tau', PFunctor.M.dest_mk]
    conv =>
      arg 1; arg 2
      rw [parAux_eq_def, parAux_def]
      arg 1
      rw [parAux_eq_def, parAux_def]
      simp only [ret, mk, ret', PFunctor.M.dest_mk]
    conv =>
      arg 1; arg 2; arg 2
      rw [parAux_eq_def, parAux_def]
      arg 2
      simp only [tau, mk, tau', PFunctor.M.dest_mk]
    simp only [_fin1Const, _fin0, Fin2.ofNat']

  theorem parAux_parS_ret_ret : parAux (.parS (ret (ε := ε) x) (ret y)) = ret (x, y) ⊕ (zero ⊕ zero) := by
    simp only [parAux]
    crush_corec_eq

  inductive IsParR (t : CTree ε β) (t1 : CTree ε α) (t2 : CTree ε β) : Prop
    | lS : t = map Prod.snd (parAux (.lS t1 t2)) → IsParR t t1 t2
    | rS : t = map Prod.snd (parAux (.rS t1 t2)) → IsParR t t1 t2
    | lrS : t = map Prod.snd (parAux (.lrS t1 t2)) → IsParR t t1 t2
    | bothS : t = map Prod.snd (parAux (.bothS t1 t2)) → IsParR t t1 t2
    | parS : t = map Prod.snd (parAux (.parS t1 t2)) → IsParR t t1 t2

  namespace Euttc
    theorem parR_ret : ((ret x) ‖→ t) ≈ t := by
      apply And.intro
      · apply Refine.coind (λ p1 p2 t1 t2 => p1 = 0 ∧ p2 = 0 ∧ ∃ t, IsParR t1 (ret x) t ∧ t2 = t) _ 0 0
        · repeat apply And.intro rfl _
          exists t
          apply And.intro _ rfl
          exact IsParR.parS rfl
        · intro p1 p2 t1 t2 ⟨hp1, hp2, t, ht1, ht2⟩
          subst hp1 hp2 ht2
          match ht1 with
          | .lS heq => sorry
          | .rS heq => sorry
          | .lrS heq => sorry
          | .bothS heq => sorry
          | .parS heq =>
            subst heq
            apply dMatchOn t2
            · intro v heq
              subst heq
              simp only [parAux_parS_ret_ret, map_choice, map_ret, map_zero]
              apply RefineF.choice_idemp
              · exact RefineF.ret rfl
              · apply RefineF.choice_idemp
                <;> exact RefineF.zero
            · intro c heq
              subst heq
              simp only [parAux_parS_ret_tau_eq, map_choice, map_tau, map_zero]
              apply RefineF.tau_right
              apply RefineF.choice_idemp
              · apply RefineF.tau_left
                apply RefineF.coind 0 0 ENat.top_pos ENat.top_pos
                repeat apply And.intro rfl _
                exists c
                apply And.intro _ rfl
                exact IsParR.bothS rfl
              · apply RefineF.choice_idemp
                · exact RefineF.zero
                · apply RefineF.tau_left
                  apply RefineF.coind 0 0 ENat.top_pos ENat.top_pos
                  repeat apply And.intro rfl _
                  exists c
                  apply And.intro _ rfl
                  exact IsParR.rS rfl
            · sorry
            · sorry
            · sorry
      · sorry

    theorem parR_map : ((map f t1) ‖→ t2) ≈ (t1 ‖→ t2) := by
      sorry

    theorem parR_assoc : ((t1 ‖→ t2) ‖→ t3) ≈ (t1 ‖→ (t2 ‖→ t3)) := by
      sorry

    theorem parR_symm : ((t1 ‖→ t2) ‖→ t3) ≈ ((t2 ‖→ t1) ‖→ t3) := by
      sorry
  end Euttc
end CTree
