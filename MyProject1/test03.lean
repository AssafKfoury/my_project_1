
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

theorem ex5 : p ∨ q → q ∨ p := by
  intro h
  cases h
  focus -- instructs Lean to `focus` on the first goal,
    apply Or.inr
    assumption
    -- it will fail if there are still unsolvable goals here
  focus
    apply Or.inl
    assumption  

theorem ex6 : p ∨ q → q ∨ p := by
  intro h
  cases h
  -- You can still use curly braces and semicolons instead of
  -- whitespace sensitive notation as in the previous example
  { apply Or.inr;
    assumption
    -- It will fail if there are unsolved goals
  }
  { apply Or.inl;
    assumption
  } 

-- Many tactics tag subgoals. The tactic `cases` tag goals using constructor names.
-- The tactic `case tag => tactics` instructs Lean to solve the goal
-- with the matching tag.
theorem ex7 : p ∨ q → q ∨ p := by
  intro h
  cases h
  case inr =>
    apply Or.inl
    assumption
  case inl =>
    apply Or.inr
    assumption

-- Same example for curly braces and semicolons aficionados
theorem ex8 : p ∨ q → q ∨ p := by {
  intro h;
  cases h;
  case inr => {
    apply Or.inl;
    assumption
  }
  case inl => {
    apply Or.inr;
    assumption
  }
}
