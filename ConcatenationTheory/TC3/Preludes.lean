import Mathlib.Init.Algebra.Classes

namespace ConcatenationTheory

class TC3Lang (τ : Type) where
  null : τ
  sym1 : τ
  sym2 : τ
  sym3 : τ
  concat: τ → τ → τ

notation "α" => TC3Lang.sym1
notation "β" => TC3Lang.sym2
notation "γ" => TC3Lang.sym3
notation "ε" => TC3Lang.null
infixl:70 " ⌢ " => TC3Lang.concat

namespace TC3Lang

variable {τ : Type} [TC3Lang τ]

def Includes (x y : τ) := ∃ z₁ z₂, z₁ ⌢ x ⌢ z₂ = y
infixl:50 " ⊑ " => Includes

def Starts (x y : τ) := ∃ z, x ⌢ z = y
infixl:50 " ⊑ₛ " => Starts

@[simp]
theorem trivialStarts (x y : τ) : (x ⊑ₛ x ⌢ y) := by exists y;

def Ends (x y : τ) := ∃ z, z ⌢ x = y
infixl:50 " ⊑ₑ " => Ends

@[simp]
theorem trivialEnds (x y : τ) : (x ⊑ₑ y ⌢ x) := by exists y;

end TC3Lang

class TC3 (τ : Type) [TC3Lang τ] where
  ax1: ∀ (x : τ), (ε ⌢ x) = x
  ax2: ∀ (x : τ), (x ⌢ ε) = x
  ax3: ∀ (x y z : τ), (x ⌢ y) ⌢ z = x ⌢ (y ⌢ z)

  ax4: ∀ (x y u v : τ), (x ⌢ y = u ⌢ v) → (∃ w, (x ⌢ w = u ∧ y = w ⌢ v) ∨ (u = x ⌢ w ∧ w ⌢ y = v))

  ax5α: (α : τ) ≠ (ε : τ)
  ax5β: (β : τ) ≠ (ε : τ)
  ax5γ: (γ : τ) ≠ (ε : τ)

  ax6α : ∀ (x y : τ), (x ⌢ y = α) → (x = ε ∨ y = ε)
  ax6β : ∀ (x y : τ), (x ⌢ y = β) → (x = ε ∨ y = ε)
  ax6γ : ∀ (x y : τ), (x ⌢ y = γ) → (x = ε ∨ y = ε)

  ax7αβ : (α : τ) ≠ (β : τ)
  ax7βγ : (β : τ) ≠ (γ : τ)
  ax7γα : (γ : τ) ≠ (α : τ)

section

variable [TC3Lang τ] [TC3 τ]
open TC3

attribute [simp] ax1 ax2 ax3

instance : IsLeftId τ (· ⌢ ·) ε := ⟨ax1⟩
instance : IsRightId τ (· ⌢ ·) ε := ⟨ax2⟩
instance : IsAssociative τ (· ⌢ ·) := ⟨ax3⟩

end
