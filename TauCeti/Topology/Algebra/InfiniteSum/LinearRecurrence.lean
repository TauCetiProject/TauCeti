/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel

/-!
# The sum of a second-order linear recurrence

For a summable sequence `d` obeying `d (r + 2) = D • d (r + 1) - S • d r`, its sum `σ`
satisfies the identity:

`σ - D • σ + S • σ = d 0 + (d 1 - D • d 0)`.

The values lie in a Hausdorff topological additive group, and each fixed scalar acts additively
and continuously. For a nonassociative ring acting on itself by left multiplication, this gives
`(1 - D + S) * σ = d 0 + (d 1 - D * d 0)`.

In an associative ring, this corresponds to evaluating the characteristic polynomial at `1`
in the formal generating-function identity
`(1 - D x + S x²) ∑ d r xʳ = d 0 + (d 1 - D d 0) x`, and it is how a local Euler factor
`(1 - a_p p^{-s} + c_p p^{-2s})⁻¹` is recovered from a prime-power recurrence for the
coefficients of a Dirichlet series.

## Main results

* `HasSum.sub_smul_add_smul_eq_of_linearRec₂`: the scalar-action identity.
* `HasSum.one_sub_add_mul_eq_of_linearRec₂`: the ring identity.
-/

public section

variable {A M : Type*} [AddCommGroup M] [DistribSMul A M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul A M] [T2Space M]
  {D S : A} {σ : M} {d : ℕ → M}

/-- **The sum of a second-order linear recurrence.** If `d` has sum `σ` and obeys
`d (r + 2) = D • d (r + 1) - S • d r`, then
`σ - D • σ + S • σ = d 0 + (d 1 - D • d 0)`. -/
theorem HasSum.sub_smul_add_smul_eq_of_linearRec₂ (h : HasSum d σ)
    (hd : ∀ r, d (r + 2) = D • d (r + 1) - S • d r) :
    σ - D • σ + S • σ = d 0 + (d 1 - D • d 0) := by
  -- the shifted sums `∑ d (r + 1) = σ - d 0` and `∑ d (r + 2) = σ - d 0 - d 1`
  have h₁ : HasSum (fun r ↦ d (r + 1)) (σ - d 0) := by
    simpa using (hasSum_nat_add_iff' 1).mpr h
  have h₂ : HasSum (fun r ↦ d (r + 2)) (σ - (d 0 + d 1)) := by
    simpa [Finset.sum_range_succ] using (hasSum_nat_add_iff' 2).mpr h
  have h₃ : HasSum (fun r ↦ d (r + 2)) (D • (σ - d 0) - S • σ) := by
    simpa only [hd] using (h₁.const_smul D).sub (h.const_smul S)
  calc σ - D • σ + S • σ
      = (σ - (d 0 + d 1)) - (D • (σ - d 0) - S • σ) + (d 0 + (d 1 - D • d 0)) := by
        rw [smul_sub]
        abel
    _ = d 0 + (d 1 - D • d 0) := by rw [h₂.unique h₃, sub_self, _root_.zero_add]

/-- **The sum of a second-order linear recurrence in a ring.** If `d` has sum `σ` and obeys
`d (r + 2) = D * d (r + 1) - S * d r`, then `(1 - D + S) * σ = d 0 + (d 1 - D * d 0)`. -/
theorem HasSum.one_sub_add_mul_eq_of_linearRec₂
    {R : Type*} [NonAssocRing R] [TopologicalSpace R]
    [IsTopologicalAddGroup R] [ContinuousConstSMul R R] [T2Space R]
    {D S σ : R} {d : ℕ → R} (h : HasSum d σ)
    (hd : ∀ r, d (r + 2) = D * d (r + 1) - S * d r) :
    (1 - D + S) * σ = d 0 + (d 1 - D * d 0) := by
  simpa only [smul_eq_mul, sub_mul, add_mul, one_mul] using
    h.sub_smul_add_smul_eq_of_linearRec₂ (D := D) (S := S)
      (by simpa only [smul_eq_mul] using hd)
