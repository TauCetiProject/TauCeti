/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Transferring the least mass of a finite set to a new coordinate

Given a probability vector `x : ι →₀ ℝ`, a finite set `σ` of coordinates and a coordinate
`v ∉ σ` of mass zero, move the mass `x a` of a least coordinate `a ∈ σ` off `σ` by subtracting it
from every coordinate of `σ` and adding `σ.card` times it to `v`. The result is nonnegative, has
total mass one, and vanishes at `a`.

## Main declarations

* `Finsupp.exists_transfer_vector`: the transferred vector, with its coordinate formula,
  nonnegativity, vanishing at `a`, and total mass one.
-/

public section

namespace Finsupp

variable {ι : Type*} [DecidableEq ι] {σ : Finset ι} {v : ι}

/-- Moving the mass `x a` of a least coordinate `a` on the starred face `σ` to the new vertex `v`
gives a nonnegative vector of total mass one whose coordinate at `a` is zero. -/
theorem exists_transfer_vector (hvσ : v ∉ σ) {x : ι →₀ ℝ} (hxpos : ∀ i, 0 ≤ x i)
    (hxsum : x.sum (fun _ r => r) = 1) (hxv : x v = 0) {a : ι} (haσ : a ∈ σ)
    (hmin : ∀ i ∈ σ, x a ≤ x i) :
    ∃ y : ι →₀ ℝ, y = x + x a • ((σ.card : ℝ) • Finsupp.single v 1 -
        ∑ i ∈ σ, Finsupp.single i 1) ∧
      (∀ i, y i = x i + x a *
        ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0)) ∧
      (∀ i, 0 ≤ y i) ∧ y a = 0 ∧ y.sum (fun _ r => r) = 1 := by
  have hav : a ≠ v := fun h => hvσ (h ▸ haσ)
  let c : ι →₀ ℝ := ∑ i ∈ σ, Finsupp.single i 1
  let y : ι →₀ ℝ := x + x a • ((σ.card : ℝ) • Finsupp.single v 1 - c)
  have hycoord (i : ι) : y i = x i + x a *
      ((if i = v then (σ.card : ℝ) else 0) - if i ∈ σ then 1 else 0) := by
    simp [y, c, Finsupp.single_apply, eq_comm]
  -- Remove equal mass on σ and transfer it to v, preserving nonnegativity.
  have hypos : ∀ i, 0 ≤ y i := by
    intro i
    rw [hycoord]
    by_cases hiv : i = v
    · subst i
      simp only [hxv, ite_true, hvσ, ite_false, sub_zero, zero_add]
      exact mul_nonneg (hxpos a) (Nat.cast_nonneg _)
    · by_cases his : i ∈ σ
      · simp only [hiv, ite_false, his, ite_true, zero_sub, mul_neg_one]
        linarith [hmin i his]
      · simpa [hiv, his] using hxpos i
  have hya : y a = 0 := by simp [hycoord, haσ, hav]
  have hsum : y.sum (fun _ r => r) = 1 := by
    let S := Finsupp.linearCombination ℝ (fun _ : ι => (1 : ℝ))
    have hS (z : ι →₀ ℝ) : S z = z.sum (fun _ r => r) := by
      simp [S, Finsupp.linearCombination_apply]
    rw [← hS]
    have hSx : S x = 1 := (hS x).trans hxsum
    simp [y, c, map_add, map_smul, map_sub, map_sum, hSx, S]
  exact ⟨y, rfl, hycoord, hypos, hya, hsum⟩

end Finsupp
