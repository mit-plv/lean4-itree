import Mathlib.Data.Stream.Defs

def Stream'.reduce (f : α → β → α) (dim : Nat) (a : α) (s : Stream' β) : Stream' α :=
  λ n =>
    let s_forwarded := s.drop (dim * n)
    let reduction_list := s_forwarded.take dim
    reduction_list.foldl f a
