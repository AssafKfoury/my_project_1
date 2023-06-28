/-# Created on 2023-06-28 -/

/- Copied from Theorem Proving in Lean 4, Chapt 5, beginning
   of section `Basic Tactics` -/
example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c h₁ h₂
  exact Eq.trans (Eq.symm h₂) h₁

/- Variation on the preceding by Assaf -/  
example : ∀ a b c : ℕ , a = b → a = c → c = b := by
  intros a b c ; intros h₁ h₂
  rw [Eq.symm h₂] ; exact h₁  
  
/- Another variation on the preceding by Assaf -/  
example : ∀ a b c : ℕ , a = b → a = c → c = b := by
  intros a b c h₁ h₂
  apply Eq.symm ; rw [Eq.symm h₁] ; assumption 

  /- Another variation on the preceding by Assaf -/  
example : ∀ a b c : ℕ , a = b → a = c → c = b := by
  intros a b c h₁ h₂
  rw [←h₂] ; exact h₁ 
  