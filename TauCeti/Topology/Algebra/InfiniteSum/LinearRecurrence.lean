/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.NoncommRing

/-!
# The sum of a second-order linear recurrence

A summable sequence `d` obeying `d (r + 2) = D * d (r + 1) - S * d r` has a sum `σ` determined by
its first two terms through the characteristic polynomial evaluated at `1`:

`(1 - D + S) * σ = d 0 + (d 1 - D * d 0)`.

This is the evaluation at `x = 1` of the formal identity
`(1 - D x + S x²) ∑ d r xʳ = d 0 + (d 1 - D d 0) x`, and it is how a local Euler factor
`(1 - a_p p^{-s} + c_p p^{-2s})⁻¹` is recovered from a prime-power recurrence for the
coefficients of a Dirichlet series.

## Main results

* `HasSum.one_sub_add_mul_eq_of_linearRec₂`: the identity above.
-/

public section

variable {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
  {D S σ : R} {d : ℕ → R}

/-- **The sum of a second-order linear recurrence.** If `d` has sum `σ` and obeys
`d (r + 2) = D * d (r + 1) - S * d r`, then `(1 - D + S) * σ = d 0 + (d 1 - D * d 0)`. -/
theorem HasSum.one_sub_add_mul_eq_of_linearRec₂ (h : HasSum d σ)
    (hd : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    (1 - D + S) * σ = d 0 + (d 1 - D * d 0) := by
  -- the shifted sums `∑ d (r + 1) = σ - d 0` and `∑ d (r + 2) = σ - d 0 - d 1`
  have h₁ : HasSum (fun r ↦ d (r + 1)) (σ - d 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr h
  have h₂ : HasSum (fun r ↦ d (r + 2)) (σ - (d 0 + d 1)) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).mpr h
  have h₃ : HasSum (fun r ↦ d (r + 2)) (D * (σ - d 0) - S * σ) := by
    simpa only [hd] using (h₁.mul_left D).sub (h.mul_left S)
  calc (1 - D + S) * σ
      = (σ - (d 0 + d 1)) - (D * (σ - d 0) - S * σ) + (d 0 + (d 1 - D * d 0)) := by noncomm_ring
    _ = d 0 + (d 1 - D * d 0) := by rw [h₂.unique h₃, sub_self, _root_.zero_add]
