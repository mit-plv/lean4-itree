import CTree.Basic
import CTree.Monad
import CTree.Euttc
import Mathlib.Data.Vector3

namespace CTree
  /- Parallel Opeartor -/

  inductive ParState (ε : Type u → Type v) (α : Type w1) (β : Type w2)
    | lS (t1 : CTree ε α) (t2 : CTree ε β)    -- · ◁ ·
    | rS (t1 : CTree ε α) (t2 : CTree ε β)    -- · ▷ ·
    | lrS (t1 : CTree ε α) (t2 : CTree ε β)   -- (· ◁ ·) ⊕ (· ▷ ·)
    | bothS (t1 : CTree ε α) (t2 : CTree ε β) -- · ⋈ ·
    | parS (t1 : CTree ε α) (t2 : CTree ε β)  -- · ‖ ·

  /-- Allows the left side to take an event -/
  infixr:60 " ◁ " => ParState.lS
  /-- Allows the right side to take an event -/
  infixr:60 " ▷ " => ParState.rS
  /-- Non-deterministically allows the either side to take an event -/
  infixr:60 " ◁▷ " => ParState.lrS
  /-- Allows both side to return a value -/
  infixr:60 " ⋈ " => ParState.bothS
  /-- Auxillary definition for the parallel operator -/
  infixr:60 " ‖ₛ " => ParState.parS

  def parAux (ps : ParState ε α β) : CTree ε (α × β) :=
    .corec' (λ {_} rec state =>
      match state with
      | t1 ◁ t2 =>
        match t1.dest with
        | ⟨.ret _, _⟩ | ⟨.zero, _⟩ => .inl zero
        | ⟨.tau, c⟩ =>
          .inr <| tau' (rec <| (c _fin0) ‖ₛ t2)
        | ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| (cts _fin0) ◁ t2) (rec <| (cts _fin1) ◁ t2)
        | ⟨.vis _ e, k⟩ =>
          .inr <| vis' e (fun a => rec <| (k a) ‖ₛ t2)
      | t1 ▷ t2 =>
        match t2.dest with
        | ⟨.ret _, _⟩ | ⟨.zero, _⟩ => .inl zero
        | ⟨.tau, c⟩ =>
          .inr <| tau' (rec <| t1 ‖ₛ (c _fin0))
        | ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| t1 ▷ (cts _fin0)) (rec <| t1 ▷ (cts _fin1))
        | ⟨.vis _ e, k⟩ =>
          .inr <| vis' e (fun a => rec <| t1 ‖ₛ (k <| a))
      | t1 ◁▷ t2 =>
        .inr <| choice' (rec <| t1 ◁ t2) (rec <| t1 ▷ t2)
      | t1 ⋈ t2 =>
        match t1.dest, t2.dest with
        | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => .inl <| ret (x, y)
        | ⟨.choice, cts⟩, _ =>
          .inr <| choice' (rec <| (cts _fin0) ⋈ t2) (rec <| (cts _fin1) ⋈ t2)
        | _, ⟨.choice, cts⟩ =>
          .inr <| choice' (rec <| t1 ⋈ (cts _fin0)) (rec <| t1 ⋈ (cts _fin1))
        | _, _ => .inl zero
      | t1 ‖ₛ t2 =>
        .inr <| choice' (rec <| t1 ⋈ t2) (rec <| t1 ◁▷ t2)
    ) ps

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    parAux (t1 ‖ₛ t2)
  infixr:60 " ‖ " => par

  def parR {ε : Type u → Type v} {α : Type w1} {β : Type w2} (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    (t1 ‖ t2).map Prod.snd -- using <$> messes up universes
  infixr:60 " ‖→ " => parR

  def parAux_def (ps : ParState ε α β) : CTree ε (α × β) :=
    match ps with
    | t1 ◁ t2 =>
      match t1.dest with
      | ⟨.ret _, _⟩ => zero
      | ⟨.tau, c⟩ => tau (parAux <| (c _fin0) ‖ₛ t2)
      | ⟨.zero, _⟩ => zero
      | ⟨.choice, cts⟩ => (parAux <| (cts _fin0) ◁ t2) ⊕ (parAux <| (cts _fin1) ◁ t2)
      | ⟨.vis _ e, k⟩ => vis e (fun a => parAux <| (k a) ‖ₛ t2)
    | t1 ▷ t2 =>
      match t2.dest with
      | ⟨.ret _, _⟩ => zero
      | ⟨.tau, c⟩ => tau (parAux <| t1 ‖ₛ (c _fin0))
      | ⟨.zero, _⟩ => zero
      | ⟨.choice, cts⟩ => (parAux <| t1 ▷ (cts _fin0)) ⊕ (parAux <| t1 ▷ (cts _fin1))
      | ⟨.vis _ e, k⟩ => vis e (fun a => parAux <| t1 ‖ₛ (k a))
    | t1 ◁▷ t2 => (parAux <| t1 ◁ t2) ⊕ (parAux <| t1 ▷ t2)
    | .bothS t1 t2 =>
      match t1.dest, t2.dest with
      | ⟨.ret x, _⟩, ⟨.ret y, _⟩ => ret (x, y)
      | ⟨.choice, cts⟩, _ =>
        (parAux <| (cts _fin0) ⋈ t2) ⊕ (parAux <| (cts _fin1) ⋈ t2)
      | _, ⟨.choice, cts⟩ =>
        (parAux <| t1 ⋈ (cts _fin0)) ⊕ (parAux <| t1 ⋈ (cts _fin1))
      | _, _ => zero
    | t1 ‖ₛ t2 => (parAux <| t1 ⋈ t2) ⊕ (parAux <| t1 ◁▷ t2)

  theorem parAux_eq_def (ps : ParState ε α β) : parAux ps = parAux_def ps := by
    rw [parAux]
    simp only [parAux_def]
    match ps with
    | .lS t1 t2 =>
      rw [unfold_corec']; simp only
      apply dMatchOn t1 <;> (intros; rename_i h; subst h) <;>
      prove_unfold_lemma
    | .rS t1 t2 =>
      rw [unfold_corec']; simp only
      apply dMatchOn t2 <;> (intros; rename_i h; subst h) <;>
      prove_unfold_lemma
    | .lrS t1 t2 =>
      rw [unfold_corec']; simp only
      prove_unfold_lemma
    | .bothS t1 t2 =>
      rw [unfold_corec']; simp only
      apply dMatchOn t1 <;> (intros; rename_i h; subst h) <;>
      apply dMatchOn t2 <;> (intros; rename_i h; subst h) <;>
      prove_unfold_lemma
    | .parS t1 t2 =>
      rw [unfold_corec']; simp only
      prove_unfold_lemma

  macro "crush_parAux_eq" : tactic => `(tactic|(
    rw [parAux_eq_def, parAux_def]
    try congr
  ))

  /-!
    Lemmas for `◁`
  -/

  theorem parAux_lS_ret : parAux (ret (ε := ε) x ◁ t) = zero := by
    crush_parAux_eq

  theorem parAux_lS_vis : parAux (vis e k ◁ t2) = vis e λ a => (parAux (k a ‖ₛ t2)) := by
    crush_parAux_eq

  theorem parAux_lS_tau : parAux (tau t1 ◁ t2) = (parAux (t1 ‖ₛ t2)).tau := by
    crush_parAux_eq

  theorem parAux_lS_zero : parAux (@zero ε ρ ◁ t2) = zero := by
    crush_parAux_eq

  theorem parAux_lS_choice : parAux ((c1 ⊕ c2) ◁ t2) = parAux (c1 ◁ t2) ⊕ parAux (c2 ◁ t2) := by
    crush_parAux_eq

  /-!
    Lemmas for `▷`
  -/

  theorem parAux_rS_ret_ret : parAux (ret (ε := ε) x ▷ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_vis : parAux (ret x ▷ vis e k) = vis e λ a => parAux (ret x ‖ₛ k a) := by
    crush_parAux_eq

  theorem parAux_rS_ret_tau : parAux (ret (ε := ε) x ▷ tau t) = (parAux (ret (ε := ε) x ‖ₛ t)).tau := by
    crush_parAux_eq

  theorem parAux_rS_ret_zero : parAux (ret (ε := ε) x ▷ zero (ρ := β)) = zero := by
    crush_parAux_eq

  theorem parAux_rS_ret_choice : parAux (ret (ε := ε) x ▷ c1 ⊕ c2) = parAux (ret x ▷ c1) ⊕ parAux (ret x ▷ c2) := by
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

  theorem parAux_bothS_ret_tau : parAux (@ret ε ρ x ⋈ tau t) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_ret_zero : parAux (@ret ε ρ x ⋈ @zero ε σ) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_ret_choice : parAux (@ret ε ρ x ⋈ c1 ⊕ c2) = parAux (ret x ⋈ c1) ⊕ parAux (ret x ⋈ c2) := by
    crush_parAux_eq

  theorem parAux_bothS_vis_ret : parAux (vis e k ⋈ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_vis : parAux (vis e1 k1 ⋈ vis e2 k2) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_tau : parAux (vis e k ⋈ tau t) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_zero : parAux (vis e k ⋈ zero (ρ := σ)) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_vis_choice : parAux (vis e k ⋈ c1 ⊕ c2) = parAux (vis e k ⋈ c1) ⊕ parAux (vis e k ⋈ c2) := by
    crush_parAux_eq

  theorem parAux_bothS_tau_ret : parAux (tau t ⋈ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_tau_vis : parAux (tau t ⋈ vis e k) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_tau_tau : parAux (tau t1 ⋈ tau t2) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_tau_zero : parAux (tau t ⋈ zero (ρ := σ)) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_tau_choice : parAux (tau t ⋈ c1 ⊕ c2) = parAux (tau t ⋈ c1) ⊕ parAux (tau t ⋈ c2) := by
    crush_parAux_eq

  theorem parAux_bothS_zero_ret : parAux (@zero ε ρ ⋈ ret y) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_vis : parAux (@zero ε ρ ⋈ vis e k) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_tau : parAux (@zero ε ρ ⋈ tau t2) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_zero : parAux (@zero ε ρ ⋈ @zero ε σ) = zero := by
    crush_parAux_eq

  theorem parAux_bothS_zero_choice : parAux (@zero ε ρ ⋈ c1 ⊕ c2) = parAux (zero ⋈ c1) ⊕ parAux (zero ⋈ c2):= by
    crush_parAux_eq

  theorem parAux_bothS_choice_ret : parAux ((c1 ⊕ c2) ⋈ ret y) = parAux (c1 ⋈ ret y) ⊕ parAux (c2 ⋈ ret y) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_vis : parAux ((c1 ⊕ c2) ⋈ vis e k) = parAux (c1 ⋈ vis e k) ⊕ parAux (c2 ⋈ vis e k) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_tau : parAux ((c1 ⊕ c2) ⋈ tau t2) = parAux (c1 ⋈ tau t2) ⊕ parAux (c2 ⋈ tau t2) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_zero : parAux ((c1 ⊕ c2) ⋈ zero (ρ := σ)) = parAux (c1 ⋈ zero) ⊕ parAux (c2 ⋈ zero) := by
    crush_parAux_eq

  theorem parAux_bothS_choice_choice : parAux ((c11 ⊕ c12) ⋈ c21 ⊕ c22) = parAux (c11 ⋈ c21 ⊕ c22) ⊕ parAux (c12 ⋈ c21 ⊕ c22) := by
    crush_parAux_eq

  /-!
    Lemmas for `‖ₛ`
  -/

  theorem parAux_parS : parAux (t1 ‖ₛ t2) = parAux (t1 ⋈ t2) ⊕ parAux (t1 ◁▷ t2) := by
    crush_parAux_eq

  theorem parAux_parS_ret : parAux (ret (ε := ε) x ‖ₛ t) = parAux (ret x ⋈ t) ⊕ zero ⊕ parAux (ret x ▷ t) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_ret : parAux (ret (ε := ε) x ‖ₛ ret y) = ret (x, y) ⊕ (zero ⊕ zero) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_vis
    : parAux (ret (ε := ε) x ‖ₛ vis e k) = zero ⊕ (zero ⊕ vis e (fun a => parAux <| ret x ‖ₛ k a)) := by
    repeat crush_parAux_eq

  theorem parAux_parS_ret_tau {v : α} {t : CTree ε β}
    : parAux (ret v ‖ₛ t.tau) = zero ⊕ zero ⊕ (parAux (ret v ‖ₛ t)).tau := by
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
