import Mathlib.Init.Algebra.Classes
import Mathlib.Tactic.LibrarySearch

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

section Relations

variable {τ : Type} [TC3Lang τ]

def Includes (x y : τ) := ∃ z₁ z₂, z₁ ⌢ x ⌢ z₂ = y
infixl:50 " ⊑ " => Includes

def Starts (x y : τ) := ∃ z, x ⌢ z = y
infixl:50 " ⊑ₛ " => Starts

def Ends (x y : τ) := ∃ z, z ⌢ x = y
infixl:50 " ⊑ₑ " => Ends

end Relations

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

open TC3 in
attribute [simp] ax1 ax2 ax3

instance [TC3Lang τ] [TC3 τ] : IsLeftId τ (· ⌢ ·) ε := ⟨TC3.ax1⟩
instance [TC3Lang τ] [TC3 τ] : IsRightId τ (· ⌢ ·) ε := ⟨TC3.ax2⟩
instance [TC3Lang τ] [TC3 τ] : IsAssociative τ (· ⌢ ·) := ⟨TC3.ax3⟩

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

@[simp]
theorem trivial_starts (x y : τ) : (x ⊑ₛ x ⌢ y) := by exists y;

@[simp]
theorem trivial_ends (x y : τ) : (x ⊑ₑ y ⌢ x) := by exists y;

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
end

section Arithmetic

open TC3
variable {τ : Type} [TC3Lang τ] [TC3 τ]

@[simp]
def ofNat : Nat → Option τ
  | 0 => some ε
  | n + 1 => (ofNat n).map (TC3Lang.concat α)
example : ofNat 3 = some (α ⌢ α ⌢ α : τ) := by simp;

@[simp]
def succ (x : Nat) : Option τ := (ofNat x).map (TC3Lang.concat α)
example : succ 2 = some (α ⌢ α ⌢ α : τ) := by simp;

@[simp]
def add (x y : Nat) : Option τ := do
  let x' ← ofNat x;
  let y' ← ofNat y;
  some (x' ⌢ y' : τ)

example : add 1 2 = some (α ⌢ α ⌢ α : τ) := by simp; rfl

end Arithmetic
