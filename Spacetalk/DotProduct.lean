import Spacetalk.Step
import Spacetalk.SimpleDataflow
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.ClearExcept

def dotProd (n : Nat) (a : Stream' (BitVec 32)) (b : Stream' (BitVec 32)) : Stream' (BitVec 32) :=
  Stream'.reduce (· + ·) n 0 (Stream'.zip (· * ·) a b)

def sa : Stream' (BitVec 32) := λ n => ⟨n % (2 ^ 32), by apply Nat.mod_lt; simp⟩

theorem Nat.sub_one_succ {n : Nat} : 0 < n → n - 1 + 1 = n := by
  intro h
  rw [Nat.sub_add_cancel]
  exact h

namespace Step
  def TwoOne (w : Nat) := .stream (.bitVec w) → .stream (.bitVec w) → .stream (.bitVec w)

  def OneOne (w : Nat) := .stream (.bitVec w) → .stream (.bitVec w)

  def dotProd (w n : Nat) : Prog (TwoOne w) :=
    let multiply : Prog (TwoOne w) := .zip (.mul)
    let reduction : Prog (OneOne w) := .reduce (.add) n 0
    .comp2 reduction multiply
end Step

theorem step_dp_equiv : ∀n : Nat, (Step.dotProd 32 n).denote = dotProd n := by aesop
