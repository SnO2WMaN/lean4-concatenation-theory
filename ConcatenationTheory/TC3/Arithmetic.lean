import ConcatenationTheory.TC3.Preludes

namespace ConcatenationTheory.TC3.Arithmetic

variable {τ : Type} [TC3Lang τ] [TC3 τ]
open TC3

@[simp]
def ofNat : Nat → Option τ
  | 0 => some ε
  | n + 1 => (ofNat n).map (TC3Lang.concat α)
example : ofNat 3 = some (α ⌢ α ⌢ α : τ) := by simp;

noncomputable def isNat (x : τ) : Prop := ∃ n, ofNat n = some x
noncomputable def toNat (x : τ) : Option Nat := none

@[simp]
def succ (x : Nat) : Option τ := (ofNat x).map (TC3Lang.concat α)
example : succ 2 = some (α ⌢ α ⌢ α : τ) := by simp;

noncomputable def isSucc (x y : τ) := ∃ n, ofNat n = some x ∧ succ n = some y

@[simp]
def add (x y : Nat) : Option τ := do
  let x' ← ofNat x;
  let y' ← ofNat y;
  some (x' ⌢ y' : τ)
example : add 1 2 = some (α ⌢ α ⌢ α : τ) := by simp; rfl

noncomputable def isAdd (x y z : τ) := ∃ n m, ofNat n = some x ∧ ofNat m = some y ∧ add n m = some z

abbrev Witness := List (Nat × Nat)

@[simp]
def ofWitness : Witness → Option τ
  | [] => some β
  | (x, y) :: w => do
    let x' ← ofNat x;
    let y' ← ofNat y;
    let w' ← ofWitness w;
    some (β ⌢ x' ⌢ γ ⌢ y' ⌢ w' : τ)

example : ofWitness [] = some (β : τ) := by simp;
example : ofWitness [(0, 0), (1, 2)] = some (β ⌢ ε ⌢ γ ⌢ ε ⌢ β ⌢ α ⌢ γ ⌢ α ⌢ α ⌢ β: τ) := by simp; rfl;

def mkMultWitness (x y : Nat) (w : Witness) : Witness :=
  match y with
  | 0 => (0, 0)::w
  | y + 1 => mkMultWitness x y (((y + 1), x * (y + 1)) :: w)
#eval mkMultWitness 2 3 []

noncomputable def isMult (x y z : τ) := ∃ n m, ofNat n = some x ∧ ofNat m = some y ∧ ofWitness (mkMultWitness n m []) = some z

def mkExpoWitness (x y : Nat) (w : Witness) : Witness :=
  match y with
  | 0 => (0, 1)::w
  | y + 1 => mkExpoWitness x y (((y + 1), x ^ (y + 1)) :: w)
#eval mkExpoWitness 2 0 []

noncomputable def isExpo (x y z : τ) := ∃ n m, ofNat n = some x ∧ ofNat m = some y ∧ ofWitness (mkExpoWitness n m []) = some z

end Arithmetic
