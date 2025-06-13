import CTree.Basic
import CTree.Monad
import CTree.Euttc
import Mathlib.Data.Vector3

namespace CTree
  /- Paralle Opeartor -/

  inductive ParState (ε : Type → Type) (α β : Type)
    | lS (t1 : CTree ε α) (t2 : CTree ε β)    -- · ◁ ·
    | rS (t1 : CTree ε α) (t2 : CTree ε β)    -- · ▷ ·
    | lrS (t1 : CTree ε α) (t2 : CTree ε β)   -- (· ◁ ·) ⊕ (· ▷ ·)
    | bothS (t1 : CTree ε α) (t2 : CTree ε β) -- · ⋈ ·
    | parS (t1 : CTree ε α) (t2 : CTree ε β)  -- · ‖ ·

  def parAux (ps : ParState ε α β) : CTree ε (α × β) :=
    corec' (λ {_} rec state =>
      match state with
      | .lS t1 t2 =>
        match t1.dest with
        | ⟨.ret _, _⟩ => .inl <| zero
        | ⟨.tau, c⟩ =>
          .inr <| tau' (rec <| .lS (c _fin0) t2)
        | ⟨.zero, _⟩ => .inl <| zero
        | ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| .lS (cts _fin0) t2) (rec <| .lS (cts _fin1) t2)
        | ⟨.vis _ e, k⟩ =>
          .inr <| vis' e (fun a => rec <| .parS (k <| .up a) t2)
      | .rS t1 t2 =>
        match t2.dest with
        | ⟨.ret _, _⟩ => .inl <| zero
        | ⟨.tau, c⟩ =>
          .inr <| tau' (rec <| .rS t1 (c _fin0))
        | ⟨.zero, _⟩ => .inl <| zero
        | ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| .rS t1 (cts _fin0)) (rec <| .rS t1 (cts _fin1))
        | ⟨.vis _ e, k⟩ =>
          .inr <| vis' e (fun a => rec <| .parS t1 (k {down := a}))
      | .lrS t1 t2 =>
        .inr <| choice' (rec <| .lS t1 t2) (rec <| .rS t1 t2)
      | .bothS t1 t2 =>
        match t1.dest, t2.dest with
        | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => .inl <| ret (x, y)
        | ⟨.tau, c⟩, _ => .inr <| tau' (rec <| .bothS (c _fin0) t2)
        | _, ⟨.tau, c⟩ => .inr <| tau' (rec <| .bothS t1 (c _fin0))
        | ⟨.choice, cts⟩, _ =>
          .inr <| choice' (rec <| .bothS (cts _fin0) t2) (rec <| .bothS (cts _fin1) t2)
        | _, ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| .bothS t1 (cts _fin0)) (rec <| .bothS t1 (cts _fin1))
        | _, _ => .inl <| zero
      | .parS t1 t2 =>
        .inr <| choice' (rec <| .bothS t1 t2) (rec <| .lrS t1 t2)
    ) ps

    infixr:60 " ◁ " => ParState.lS
    infixr:60 " ▷ " => ParState.rS
    infixr:60 " ◁▷ " => ParState.lrS
    infixr:60 " ⋈ " => ParState.bothS
    infixr:60 " ‖ₛ " => ParState.parS

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    parAux (.parS t1 t2)
  infixr:60 " ‖ " => par

  def parR (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    Prod.snd <$> (t1 ‖ t2)
  infixr:60 " ‖→ " => parR

  macro "simp_ctree_mk" : tactic => `(tactic|(
    simp only [
      mk, PFunctor.M.dest_mk,
      ret, ret',
      tau, tau',
      vis, vis',
      zero, zero',
      choice, choice',
    ]
  ))

  /--
  The least amount of theorems needed to unfold a `corec'` call to see the
  `PFunctor.M.mk` constructor.
  -/
  macro "simp_corec_base" : tactic => `(tactic|(
    simp_all (config := {maxSteps := 400000}) only [
      -- `corec`
      corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
      -- `map`
      PFunctor.map,
      -- Get rid of `Sum.bind`
      Bind.bind, Sum.bind
    ]
  ))

  macro "simp_corec_full" : tactic => `(tactic|(
    simp_all only [
      -- `PFunctor.M.corec` related
      corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.corec_def,
      -- Other `PFunctor` things
      PFunctor.map, PFunctor.map_eq, PFunctor.M.dest_mk, PFunctor.M.children_mk,
      -- Get rid of `Sum.bind` in `PFunctor.M.corec'`
      Bind.bind, Sum.bind,
      -- `CTree` constructors
      mk, ret, ret', vis, vis', tau, tau', zero, zero', choice, choice',
      -- General function things
      Function.comp_apply, Function.id_comp, id_eq,
      -- `Vector3` related
      Fin2.ofNat', _fin2Const, _fin1Const, _fin0, _fin1, Vector3.cons_fz, Vector3.cons_fs,
      -- `Nat` related
      Nat.reduceAdd,
      -- Boolean logic
      true_or, and_self,
      -- ULift
      ULift.down, cast_eq
    ]
  ))

  theorem _fin1_elim {P : Prop} (i : ULift (Fin2 1))
    (h : i = .up (.ofNat' 0) → P) : P :=
    match i with
    | .up (.ofNat' 0) => h rfl

  theorem _fin2_elim {P : Prop} (i : ULift (Fin2 2))
    (h1 : i = .up (.ofNat' 0) → P) (h2 : i = .up (.ofNat' 1) → P) : P :=
    match i with
    | .up (.ofNat' 0) => h1 rfl
    | .up (.ofNat' 1) => h2 rfl

  /--
  `crush_corec_eq` tries to prove equality of two `CTree`s that terminate.
  -/
  macro "crush_corec_eq" : tactic => `(tactic|(
    repeat
     (simp_corec_full
      congr
      funext i
      first
        | exact elim0_lift i
        | apply _fin2_elim i <;> intros)
  ))

  theorem par_ret_ret_eq {ε α β} {x : α} {y : β} : (ret (ε := ε) x ‖ ret y) = ret (x, y) ⊕ (zero ⊕ zero) := by
    simp only [par, parAux]
    crush_corec_eq

  theorem par_ret_ret_equiv {ε α β} {x : α} {y : β} : (ret (ε := ε) x ‖ ret y) ≈ ret (x, y) := by
    apply Euttc.eq_trans (t2 := ret (x, y) ⊕ (zero ⊕ zero))
    · rw [par_ret_ret_eq]
    · apply Euttc.eq_trans (t2 := (ret (x, y) ⊕ zero) ⊕ zero)
      · apply Euttc.eq_symm
        exact Euttc.choice_assoc
      · repeat apply Euttc.zero_right_id
        exact Euttc.eq_refl

  def parAux_def (ps : ParState ε α β) : CTree ε (α × β) :=
    match ps with
    | .lS t1 t2 =>
      match t1.dest with
      | ⟨.ret _, _⟩ => zero
      | ⟨.tau, c⟩ => tau (parAux <| .lS (c _fin0) t2)
      | ⟨.zero, _⟩ => zero
      | ⟨.choice, cts⟩ => choice (parAux <| .lS (cts _fin0) t2) (parAux <| .lS (cts _fin1) t2)
      | ⟨.vis _ e, k⟩ => vis e (fun a => parAux <| .parS (k {down := a}) t2)
    | .rS t1 t2 =>
      match t2.dest with
      | ⟨.ret _, _⟩ => zero
      | ⟨.tau, c⟩ => tau (parAux <| .rS t1 (c _fin0))
      | ⟨.zero, _⟩ => zero
      | ⟨.choice, cts⟩ => choice (parAux <| .rS t1 (cts _fin0)) (parAux <| .rS t1 (cts _fin1))
      | ⟨.vis _ e, k⟩ => vis e (fun a => parAux <| .parS t1 (k {down := a}))
    | .lrS t1 t2 => choice (parAux <| .lS t1 t2) (parAux <| .rS t1 t2)
    | .bothS t1 t2 =>
      match t1.dest, t2.dest with
      | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => ret (x, y)
      | ⟨.tau, c⟩, _ => tau (parAux <| .bothS (c _fin0) t2)
      | _, ⟨.tau, c⟩ => tau (parAux <| .bothS t1 (c _fin0))
      | ⟨.choice, cts⟩, _ =>
        choice (parAux <| .bothS (cts _fin0) t2) (parAux <| .bothS (cts _fin1) t2)
      | _, ⟨.choice, cts⟩ =>
        choice (parAux <| .bothS t1 (cts _fin0)) (parAux <| .bothS t1 (cts _fin1))
      | _, _ => zero
    | .parS t1 t2 => choice (parAux <| .bothS t1 t2) (parAux <| .lrS t1 t2)

  macro "simp_ctree" : tactic => `(tactic|(
    simp only [ret, tau, zero, vis, choice, mk, ret', tau', zero', vis', choice', PFunctor.M.dest_mk]
    apply exists_and_eq
    intro i
    try first
    | exact elim0_lift i
    | apply _fin1_elim i; intro heq; subst heq
    | apply _fin2_elim i <;> (intros heq; subst heq)
  ))

  macro "parAux_eq_def_left_right " ps:term : tactic => `(tactic|(
    simp only [parAux, corec', PFunctor.M.corec', PFunctor.M.corec₁, PFunctor.M.dest_corec]
    match ($ps) with
    | .lS t1 t2 =>
      simp only [parAux_def, PFunctor.map, Bind.bind, Sum.bind]
      match t1.dest with
      | ⟨.ret _, _⟩ => simp_ctree
      | ⟨.tau, c⟩ => simp_ctree; exists .lS (c _fin0) t2
      | ⟨.zero, _⟩ => simp_ctree
      | ⟨.choice, cts⟩ =>
        simp_ctree
        · exists .lS (cts _fin0) t2
        · exists .lS (cts _fin1) t2
      | ⟨.vis _ e, k⟩ =>
        simp_ctree; rename_i i
        exists .parS (k i) t2
    | .rS t1 t2 =>
      simp only [parAux_def, PFunctor.map, Bind.bind, Sum.bind]
      match t2.dest with
      | ⟨.ret _, _⟩ => simp_ctree
      | ⟨.tau, c⟩ => simp_ctree; exists .rS t1 (c _fin0)
      | ⟨.zero, _⟩ => simp_ctree
      | ⟨.choice, cts⟩ =>
        simp_ctree
        · exists .rS t1 (cts _fin0)
        · exists .rS t1 (cts _fin1)
      | ⟨.vis _ e, k⟩ =>
        simp_ctree; rename_i i
        exists .parS t1 (k i)
    | .lrS t1 t2 =>
      simp_ctree
      · exists .lS t1 t2
      · exists .rS t1 t2
    | .bothS t1 t2 =>
      simp only [parAux_def, PFunctor.map, Bind.bind, Sum.bind]
      cases t1.dest; rename_i shape1 cont1
      cases t2.dest; rename_i shape2 cont2
      cases shape1 <;> cases shape2 <;> simp_ctree;
      all_goals
        solve
        | exists .bothS t1 (cont2 _fin0)
        | exists .bothS t1 (cont2 _fin1)
        | exists .bothS (cont1 _fin0) t2
        | exists .bothS (cont1 _fin1) t2
    | .parS t1 t2 =>
      simp only [parAux_def, PFunctor.map, Bind.bind, Sum.bind]
      simp_ctree
      · exists .bothS t1 t2
      · exists .lrS t1 t2
  ))

  lemma parAux_eq_def_left (ps : ParState ε α β) :
    ∃ hd k k',
      (parAux ps).dest = ⟨hd, k⟩ ∧
      (parAux ps).dest = ⟨hd, k'⟩ ∧
      ∀ i, ∃ ps, k i = parAux ps ∧ k' i = parAux ps := by
    parAux_eq_def_left_right ps

  lemma parAux_eq_def_right (ps : ParState ε α β) :
    ∃ hd k k',
      (parAux ps).dest = ⟨hd, k⟩ ∧
      (parAux_def ps).dest = ⟨hd, k'⟩ ∧
      ∀ i, ∃ ps, k i = parAux ps ∧ k' i = parAux ps := by
    parAux_eq_def_left_right ps

  theorem parAux_eq_def (ps : ParState ε α β) : parAux ps = parAux_def ps := by
    apply PFunctor.M.bisim (λ t1 t2 => ∃ ps, t1 = parAux ps ∧ (t2 = parAux ps ∨ t2 = parAux_def ps))
    on_goal 2 => exists ps; exact And.intro rfl (.inr rfl)
    clear ps
    intro t1 t2 ⟨ps, ⟨h1, h2⟩⟩
    cases h2 <;> (rename_i h2; subst h1 h2)
    · have ⟨hd, k, k', h1, h2, h3⟩ := parAux_eq_def_left ps
      refine ⟨hd, k, k', h1, h2, ?_⟩
      intro i
      have ⟨ps, h3, h3'⟩ := h3 i
      exact ⟨ps, h3, .inl h3'⟩
    · have ⟨hd, k, k', h1, h2, h3⟩ := parAux_eq_def_right ps
      refine ⟨hd, k, k', h1, h2, ?_⟩
      intro i
      have ⟨ps, h3, h3'⟩ := h3 i
      exact ⟨ps, h3, .inl h3'⟩

  macro "crush_parAux_eq" : tactic => `(tactic|(
    rw [parAux_eq_def, parAux_def]
    try congr
  ))

  /-!
    Lemmas for `◁`
  -/

  theorem parAux_lS_ret : parAux (ret (ε := ε) x ◁ t) = zero := by
    crush_parAux_eq

  /-!
    Lemmas for `▷`
  -/

  theorem parAux_rS_ret_ret : parAux (ret (ε := ε) x ▷ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_tau : parAux (ret (ε := ε) x ▷ tau t) = (parAux (ret (ε := ε) x ▷ t)).tau := by
    crush_parAux_eq

  theorem parAux_rS_ret_zero : parAux (ret (ε := ε) x ▷ zero (ρ := β)) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_choice : parAux (ret (ε := ε) x ▷ c1 ⊕ c2) = parAux (ret x ▷ c1) ⊕ parAux (ret x ▷ c2) := by
    crush_parAux_eq

  theorem parAux_rS_ret_vis : parAux (ret x ▷ vis e k) = vis e λ a => parAux (ret x ‖ₛ k a) := by
    crush_parAux_eq

  /-!
    Lemmas for `◁▷`
  -/

  theorem parAux_lrS : parAux (t1 ◁▷ t2) = parAux (t1 ◁ t2) ⊕ parAux (t1 ▷ t2) := by
    crush_parAux_eq

  /-!
    Lemmas for `⋈`
  -/

  theorem parAux_bothS_ret_ret : parAux (@ret ε ρ x ⋈ ret y) = ret (x, y) := by
    crush_parAux_eq

  theorem parAux_bothS_ret_vis : parAux (@ret ε ρ x ⋈ vis e k) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_ret_tau : parAux (@ret ε ρ x ⋈ tau t) = (parAux (ret x ⋈ t)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_ret_zero : parAux (@ret ε ρ x ⋈ @zero ε σ) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_ret_choice : parAux (@ret ε ρ x ⋈ c1 ⊕ c2) = parAux (ret x ⋈ c1) ⊕ parAux (ret x ⋈ c2) := by
    crush_parAux_eq

  theorem parAux_bothS_vis_ret : parAux (vis e k ⋈ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_vis : parAux (vis e k ⋈ vis e k) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_tau : parAux (vis e k ⋈ tau t) = (parAux (vis e k ⋈ t)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_vis_zero : parAux (vis e k ⋈ zero (ρ := σ)) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_choice : parAux (vis e k ⋈ c1 ⊕ c2) = parAux (vis e k ⋈ c1) ⊕ parAux (vis e k ⋈ c2) := by
    crush_parAux_eq

  theorem parAux_bothS_tau_ret : parAux (tau t ⋈ ret y) = (parAux (t ⋈ ret y)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_tau_vis : parAux (tau t ⋈ vis e k) = (parAux (t ⋈ vis e k)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_tau_tau : parAux (tau t1 ⋈ tau t2) = (parAux (t1 ⋈ tau t2)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_tau_zero : parAux (tau t ⋈ zero (ρ := σ)) = (parAux (t ⋈ zero)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_tau_choice : parAux (tau t ⋈ c1 ⊕ c2) = (parAux (t ⋈ c1 ⊕ c2)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_zero_ret : parAux (@zero ε ρ ⋈ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_vis : parAux (@zero ε ρ ⋈ vis e k) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_tau : parAux (@zero ε ρ ⋈ tau t2) = (parAux (zero ⋈ t2)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_zero_zero : parAux (@zero ε ρ ⋈ @zero ε σ) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_choice : parAux (@zero ε ρ ⋈ c1 ⊕ c2) = parAux (zero ⋈ c1) ⊕ parAux (zero ⋈ c2):= by
    crush_parAux_eq

  theorem parAux_bothS_choice_ret : parAux ((c1 ⊕ c2) ⋈ ret y) = parAux (c1 ⋈ ret y) ⊕ parAux (c2 ⋈ ret y) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_vis : parAux ((c1 ⊕ c2) ⋈ vis e k) = parAux (c1 ⋈ vis e k) ⊕ parAux (c2 ⋈ vis e k) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_tau : parAux ((c1 ⊕ c2) ⋈ tau t2) = (parAux ((c1 ⊕ c2) ⋈ t2)).tau := by
    crush_parAux_eq

  theorem parAux_bothS_choice_zero : parAux ((c1 ⊕ c2) ⋈ zero (ρ := σ)) = parAux (c1 ⋈ zero) ⊕ parAux (c2 ⋈ zero) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_choice : parAux ((c1 ⊕ c2) ⋈ c1 ⊕ c2) = parAux (c1 ⋈ c1 ⊕ c2) ⊕ parAux (c2 ⋈ c1 ⊕ c2) := by
    crush_parAux_eq

  /-!
    Lemmas for `‖ₛ`
  -/

  theorem parAux_parS : parAux (t1 ‖ₛ t2) = parAux (t1 ⋈ t2) ⊕ parAux (t1 ◁▷ t2) := by
    crush_parAux_eq

  theorem parAux_parS_ret : parAux (ret (ε := ε) x ‖ₛ t) = parAux (ret x ⋈ t) ⊕ zero ⊕ parAux (ret x ▷ t) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_tau {v : α} {t : CTree ε β}
    : parAux (ret v ‖ₛ t.tau)
      = (parAux (ParState.bothS (ret v) t)).tau
        ⊕ zero
        ⊕ (parAux (ParState.rS (ret v) t)).tau := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_ret : parAux (ret (ε := ε) x ‖ₛ ret y) = ret (x, y) ⊕ (zero ⊕ zero) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_vis
    : parAux (ret (ε := ε) x ‖ₛ vis e k) = zero ⊕ (zero ⊕ vis e (fun a => parAux <| ret x ‖ₛ k a)) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_zero
    : parAux (ret (ε := ε) x ‖ₛ zero (ρ := β)) = zero ⊕ (zero ⊕ zero) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_choice
    : parAux (ret (ε := ε) x ‖ₛ c1 ⊕ c2)
      = (parAux (ret x ⋈ c1) ⊕ parAux (ret x ⋈ c2))
        ⊕ (zero ⊕ (parAux (ret x ▷ c1) ⊕ parAux (ret x ▷ c2))) := by
    repeat crush_parAux_eq

end CTree
