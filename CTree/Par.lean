import CTree.Basic
import CTree.Eutt
import CTree.Monad

namespace CTree
  /- Paralle Opeartor -/

  def vis_left {α β} (par : CTree ε α → CTree ε β → CTree ε (α × β))
    (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry

  def bothRet (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry

  -- TODO: How to do the case with two events?
  def biasedEffect (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry
    -- corec' (λ rec (t1, t2) =>
    --   match t1.dest with
    --   | ⟨.ret a, _⟩ => .inl <| zero
    --   | ⟨.tau, c⟩ => .inr <| tau' <| rec (c _fin0, t2)
    --   | ⟨.zero, _⟩ => .inl <| zero
    --   | ⟨.choice, cts⟩ => .inr <| choice' (rec ⟨cts _fin0, t2⟩) (rec (cts _fin1, t2))
    --   | ⟨.vis α e, k⟩ =>
    --     .inr <| vis' e λ a =>
    --       let k := k (.up a)
    --       choice' (rec ⟨k, t2⟩) (bothRet k t2)
    -- ) (t1, t2)
    -- corec (α := sorry) (λ state => sorry) sorry
    -- corec' (λ {X} rec (t1, t2) =>
    --   match t1.dest, t2.dest with
    --   | ⟨.ret a, _⟩, ⟨.ret b, _⟩ => .inl <| ret (a, b)
    --   | ⟨.tau, c⟩, _ => .inr <| tau' <| rec (c _fin0, t2)
    --   | _, ⟨.tau, c⟩ => .inr <| tau' <| rec (t1, c _fin0)
    --   | ⟨.choice, cts⟩, _ => .inr <| choice' (rec ⟨cts _fin0, t2⟩) (rec (cts _fin1, t2))
    --   | _, ⟨.choice, cts⟩ => .inr <| choice' (rec ⟨t1, cts _fin0⟩) (rec (t1, cts _fin1))
    --   | ⟨.vis α1 e1, k1⟩, ⟨.vis α2 e2, k2⟩ =>
    --     let left : P ε (α × β) X := vis' e1 λ a => rec ⟨k1 (.up a), t2⟩
    --     let right : P ε (α × β) X := vis' e2 λ a => rec ⟨t1, k2 (.up a)⟩
    --     .inr <| choice' sorry sorry
    --   | ⟨.vis α' e, k⟩, _ => .inr <| vis' e λ a => rec ⟨k (.up a), t2⟩
    --   | _, ⟨.vis α' e, k⟩ => .inr <| vis' e λ a => rec ⟨t1, k (.up a)⟩
    --   | _, _ => .inl zero
    -- ) (t1, t2)

  def par (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε (α × β) :=
    sorry
  infixr:60 " || " => par

  def parR (t1 : CTree ε α) (t2 : CTree ε β) : CTree ε β :=
    Prod.snd <$> (t1 || t2)
  infixr:60 " ||→ " => parR

  namespace Eutt
    theorem parR_ret : Eutt r ((ret x) ||→ t) t := by
      sorry

    theorem parR_map : Eutt r ((map f t1) ||→ t2) (t1 ||→ t2) := by
      sorry

    theorem parR_assoc : Eutt r ((t1 ||→ t2) ||→ t3) (t1 ||→ (t2 ||→ t3)) := by
      sorry

    theorem parR_symm : Eutt r ((t1 ||→ t2) ||→ t3) ((t2 ||→ t1) ||→ t3) := by
      sorry
  end Eutt

end CTree
