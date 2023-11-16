import Spacetalk.Step
import Spacetalk.VirtualRDA


def dot_prod (n : Nat) (a : Stream' Nat) (b : Stream' Nat) : Stream' Nat :=
  Stream'.reduce (· + ·) n 0 (Stream'.zip (· * ·) a b)

namespace Step
  -- A dot product of length n vectors
  def dot_prod (n : Nat) : Prog rep (.stream .nat → .stream .nat → .stream .nat) :=
    let multiply := .zip (.binop .mul)
    let reduction := .reduce (.binop .add) n 0
    .lam λ a => .lam λ b => .app reduction (.app (.app multiply (.var a)) (.var b))

  def sa : Stream' Nat := id
  def sb : Stream' Nat := id

  def dp (n : Nat) := (dot_prod n).denote sa sb
  def n := 10
  #eval (dp n).get 0

end Step

theorem step_dp_equiv : ∀n : Nat, (Step.dot_prod n).denote = dot_prod n := by
  simp [dot_prod]
