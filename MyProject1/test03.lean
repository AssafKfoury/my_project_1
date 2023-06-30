
/-# Created on 2023-06-30 -/
/- Copied from 
https://notabug.org/LinusTuring/lean4/src/master/doc/tactics.md 
-/

theorem ex1 : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl h1 =>
    apply Or.inr
    exact h1
  | inr h2 =>
    apply Or.inl
    assumption

#print ex1

-- You can use `match-with` in tactics.
theorem ex2 : p ∨ q → q ∨ p := by
  intro h
  match h with
  | Or.inl _  => apply Or.inr; assumption
  | Or.inr h2 => apply Or.inl; exact h2

-- As we have the `fun+match` syntax sugar for terms,
-- we have the `intro+match` syntax sugar
theorem ex3 : p ∨ q → q ∨ p := by
  intro
  | Or.inl h1 =>
    apply Or.inr
    exact h1
  | Or.inr h2 =>
    apply Or.inl
    assumption

theorem ex4 : p ∨ q → q ∨ p := by
  intro h
  cases h
  apply Or.inr
  assumption
  apply Or.inl
  assumption
  done -- fails with an error here if there are unsolvable goals