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
   `Blank_by_Assaf.lean` -/
theorem easy1 (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := by
   have h4 : Q := (h1 h3)
   have h5 : R := (h2 h4)
   exact h5  
   -- show R := (h2 h4)
   done

theorem easy2 (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := sorry 

theorem easy3 (P Q R : Prop) (h1 : P → Q)
   (h2 : Q → R) (h3 : P) : R := by
   apply h2 _ ; apply h1 _ ; exact h3 
   done

#check easy2    