/-# Created on 2023-06-20 -/
import Mathlib.Topology.Basic

#check TopologicalSpace

#eval 1+1
#reduce 1+1
#check 1+1

/- same as in `Blank_by_Assaf.lean` following
   Page 13 in HTPI+Lean -/
theorem easy (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := 
    h2 (h1 h3)  

/- a little different from the syntax of 
   `Blank_by_Assaf.lean` in HTPI+Lean -/
theorem easy1 (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := -- by
    have h4 : Q := h1 h3
    show R from h2 h4  
    -- done

theorem easy2 (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := sorry 

theorem easy3 (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := by
   apply h2 _ ; apply h1 _ ; exact h3 
   done

lemma lem1 (P Q R : Prop) : P ∧ Q → P ∧ (Q ∨ R) :=
   (fun hpq : P ∧ Q =>
    have hp : P := hpq.left
    have hq : Q := hpq.right
    show P ∧ (Q ∨ R) from ⟨hp, Or.inl hq⟩)

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp
  done 

theorem test1 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by 
  constructor ; exact hp
  constructor ; exact hq ; exact hp  

theorem test2 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by  
  apply And.intro 
  case left => exact hp 
  case right =>
    apply And.intro
    case left => exact hq
    case right => exact hp

theorem test3 (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp _ 
  exact And.intro hq hp 


#check easy1
#check lem1     

#check And     -- Prop → Prop → Prop
#check Or      -- Prop → Prop → Prop
#check Not     -- Prop → Prop
#check Implies -- Prop → Prop → Prop

#check modus_ponens 

