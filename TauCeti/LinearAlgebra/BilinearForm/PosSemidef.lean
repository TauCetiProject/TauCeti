/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Positive-semidefinite bilinear forms

This file records a pointwise characterization of positive semidefiniteness for symmetric
bilinear forms. It converts `IsPosSemidef` into diagonal nonnegativity, the form consumed by
quadratic-form signature criteria and other pointwise positivity arguments. Over an ordered ring,
it also bounds the value of a positive-semidefinite form on a sum of `k` vectors by `k` times the
sum of their values, the inequality `‖x₁ + ⋯ + xₖ‖² ≤ k (‖x₁‖² + ⋯ + ‖xₖ‖²)` of inner product
spaces.

## Main results

* `LinearMap.BilinForm.isPosSemidef_iff_forall_nonneg`: a symmetric bilinear form is
  positive-semidefinite exactly when its diagonal values are nonnegative.
* `LinearMap.BilinForm.IsPosSemidef.apply_sum_sum_le_card_mul_sum`: the value of a
  positive-semidefinite form on a sum of vectors is at most the number of summands times the sum
  of their values.
-/

public section

namespace LinearMap.BilinForm

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [LE R]

/-- A symmetric bilinear form is positive-semidefinite if and only if its values on all vectors
are nonnegative. -/
@[grind =]
theorem isPosSemidef_iff_forall_nonneg (B : LinearMap.BilinForm R M) (hB : B.IsSymm) :
    B.IsPosSemidef ↔ ∀ x, 0 ≤ B x x := by
  rw [LinearMap.BilinForm.isPosSemidef_def, LinearMap.BilinForm.isNonneg_def]
  simp only [hB, true_and]

section OrderedRing

variable {R M ι : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [AddCommGroup M]
  [Module R M]

/-- A positive-semidefinite bilinear form satisfies
`B (x₁ + ⋯ + xₖ) (x₁ + ⋯ + xₖ) ≤ k * (B x₁ x₁ + ⋯ + B xₖ xₖ)`. -/
theorem IsPosSemidef.apply_sum_sum_le_card_mul_sum {B : LinearMap.BilinForm R M}
    (hB : B.IsPosSemidef) (s : Finset ι) (x : ι → M) :
    B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤ s.card * ∑ i ∈ s, B (x i) (x i) := by
  -- Each cross term satisfies `2 B(x, y) ≤ B(x, x) + B(y, y)`, since `B(x - y, x - y) ≥ 0`.
  have hpair (i j : ι) : 2 * B (x i) (x j) ≤ B (x i) (x i) + B (x j) (x j) := by
    have h := hB.isNonneg.nonneg (x i - x j)
    simp only [map_sub, LinearMap.sub_apply, hB.isSymm.eq (x j) (x i)] at h
    linarith
  have hsum : 2 * B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤
      2 * (s.card * ∑ i ∈ s, B (x i) (x i)) := by
    simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
    calc ∑ j ∈ s, ∑ i ∈ s, 2 * B (x i) (x j)
        ≤ ∑ j ∈ s, ∑ i ∈ s, (B (x i) (x i) + B (x j) (x j)) :=
          Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun i _ ↦ hpair i j
      _ = ∑ i ∈ s, 2 * (s.card * B (x i) (x i)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
          ring
  exact le_of_mul_le_mul_left hsum two_pos

end OrderedRing

end LinearMap.BilinForm
