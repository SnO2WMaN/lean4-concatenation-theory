import ConcatenationTheory.TC3.Preludes
import Mathlib.Tactic.LibrarySearch

namespace ConcatenationTheory.TC3

variable {τ : Type} [TC3Lang τ] [TC3 τ]

open TC3

example (x : τ) : (α ⌢ x ≠ ε) ∧ (x ⌢ α ≠ ε) := by
  apply And.intro
  . sorry
  . sorry

example (x y : τ) : x ⌢ y = ε → (x = ε ∧ y = ε) := by
  intro h;
  sorry

example (x y : τ) : ((x ⌢ α = y ⌢ α ∧ α ⌢ x = α ⌢ y) → x = y) := by
  intro h;
  have ⟨h1, h2⟩ := h;
  have ⟨w1, h3⟩ := ax4 _ _ _ _ h1;
  have ⟨w2, h4⟩ := ax4 _ _ _ _ h2;
  sorry

example (x y z : τ) : (x ⌢ y = z ⌢ α → (y = ε ∨ α ⊑ₑ y)) := by
  intro h;
  have ⟨w, h1⟩ := ax4 _ _ _ _ h;
  cases h1 with
  | inl h1 => rw [h1.right]; simp;
  | inr h1 =>
    have h2 := ax6α _ _ h1.right;
    cases h2 with
    | inr h2 => exact Or.inl h2;
    | inl h2 => sorry

end ConcatenationTheory.TC3
