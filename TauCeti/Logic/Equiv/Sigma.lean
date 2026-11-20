/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.Basic

/-!
# Bounded-index prefix equivalences for dependent sums over `ℕ`

For a family `β : ℕ → Type*`, restricting `Σ m : ℕ, β m` to indices `m ≤ k` produces finite-prefix
dependent sums `{p : Σ m : ℕ, β m // p.1 ≤ k}`. At `k = 0` this subtype is equivalent to the
initial fiber `β 0` (`Equiv.sigmaFstLeZeroEquiv`), and at `k + 1` it splits into the prefix up to
`k` together with the new fiber `β (k + 1)` (`Equiv.sigmaFstLeSuccEquiv`). These recurrences
identify stagewise cumulative cell or generator index sets along sequential towers.
-/

public section

namespace Equiv

/-- Elements of `Σ m : ℕ, β m` with `m ≤ 0` correspond to elements of `β 0`. -/
def sigmaFstLeZeroEquiv (β : ℕ → Type*) : {p : Σ m : ℕ, β m // p.1 ≤ 0} ≃ β 0 :=
  (subtypeEquivRight fun _ ↦ Nat.le_zero).trans (sigmaSubtype 0)

@[simp] theorem sigmaFstLeZeroEquiv_apply_zero {β : ℕ → Type*} (x : β 0) :
    sigmaFstLeZeroEquiv β ⟨⟨0, x⟩, Nat.le_refl 0⟩ = x := (rfl)

@[simp] theorem sigmaFstLeZeroEquiv_symm_apply {β : ℕ → Type*} (x : β 0) :
    (sigmaFstLeZeroEquiv β).symm x = ⟨⟨0, x⟩, Nat.le_refl 0⟩ := (rfl)

/-- Elements of `Σ m : ℕ, β m` with `m ≤ k + 1` split into those with `m ≤ k` and `β (k + 1)`. -/
def sigmaFstLeSuccEquiv (β : ℕ → Type*) (k : ℕ) :
    {p : Σ m : ℕ, β m // p.1 ≤ k + 1} ≃ {p : Σ m : ℕ, β m // p.1 ≤ k} ⊕ β (k + 1) where
  toFun p := if hp : p.1.1 ≤ k then Sum.inl ⟨p.1, hp⟩
    else Sum.inr (Nat.le_antisymm p.2 (Nat.gt_of_not_le hp) ▸ p.1.2)
  invFun | Sum.inl p => ⟨p.1, Nat.le_succ_of_le p.2⟩ | Sum.inr x => ⟨⟨k + 1, x⟩, Nat.le_refl _⟩
  left_inv := fun ⟨⟨m, _⟩, hm⟩ ↦ by
    by_cases hmk : m ≤ k
    · simp [hmk]
    · obtain rfl := Nat.le_antisymm hm (Nat.gt_of_not_le hmk); simp [Nat.not_succ_le_self]
  right_inv | Sum.inl ⟨_, hp⟩ => by simp [hp] | Sum.inr _ => by simp [Nat.not_succ_le_self]

@[simp] theorem sigmaFstLeSuccEquiv_apply_of_le {β : ℕ → Type*} {k : ℕ}
    (p : Σ m : ℕ, β m) (hp : p.1 ≤ k) :
    sigmaFstLeSuccEquiv β k ⟨p, Nat.le_succ_of_le hp⟩ = Sum.inl ⟨p, hp⟩ := by
  simp [sigmaFstLeSuccEquiv, hp]

@[simp] theorem sigmaFstLeSuccEquiv_apply_self {β : ℕ → Type*} (k : ℕ) (x : β (k + 1)) :
    sigmaFstLeSuccEquiv β k ⟨⟨k + 1, x⟩, Nat.le_refl (k + 1)⟩ = Sum.inr x := by
  simp [sigmaFstLeSuccEquiv, Nat.not_succ_le_self]

@[simp] theorem sigmaFstLeSuccEquiv_symm_inl {β : ℕ → Type*} {k : ℕ}
    (p : {p : Σ m : ℕ, β m // p.1 ≤ k}) :
    (sigmaFstLeSuccEquiv β k).symm (Sum.inl p) = ⟨p.1, Nat.le_succ_of_le p.2⟩ := (rfl)

@[simp] theorem sigmaFstLeSuccEquiv_symm_inr {β : ℕ → Type*} (k : ℕ) (x : β (k + 1)) :
    (sigmaFstLeSuccEquiv β k).symm (Sum.inr x) = ⟨⟨k + 1, x⟩, Nat.le_refl (k + 1)⟩ := (rfl)

end Equiv
