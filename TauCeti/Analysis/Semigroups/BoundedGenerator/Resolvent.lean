/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
public import TauCeti.Analysis.Semigroups.Resolvent

/-!
# Resolvent of a bounded generator

This file identifies the Laplace-transform resolvent of the uniformly continuous semigroup
`t ↦ exp (tA)` with the Neumann series for `λI - A`.  For `‖A‖ < λ`, the series

`λ⁻¹ ∑' n, (λ⁻¹ A)ⁿ`

converges in the Banach algebra of bounded operators and is a two-sided inverse of `λI - A`.
The general semigroup resolvent is already a right inverse, so the two operators agree.  This
is the bounded-generator resolvent acceptance example in the one-parameter-semigroups roadmap.

The geometric-series argument uses Mathlib's `summable_geometric_of_norm_lt_one` and its
two multiplication identities for the sum.

## References

See Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section I.3.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

/-- The geometric power series in `λ⁻¹ • A` is summable when `‖A‖ < λ`. -/
theorem summable_pow_inv_smul_of_norm_lt (A : X →L[ℝ] X) {lambda : ℝ}
    (hlambda : ‖A‖ < lambda) : Summable fun n : ℕ => (lambda⁻¹ • A) ^ n := by
  apply summable_geometric_of_norm_lt_one
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (lt_of_le_of_lt (norm_nonneg A) hlambda)]
  exact (inv_mul_lt_one₀ (lt_of_le_of_lt (norm_nonneg A) hlambda)).2 hlambda

/-- The Neumann-series resolvent is a right inverse of `λI - A`. -/
@[simp] theorem sub_mul_inv_smul_tsum_pow (A : X →L[ℝ] X) {lambda : ℝ}
    (hlambda : ‖A‖ < lambda) :
    (lambda • 1 - A) * (lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n) = 1 := by
  have hlambda_pos : 0 < lambda := lt_of_le_of_lt (norm_nonneg A) hlambda
  have hnorm : ‖lambda⁻¹ • A‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlambda_pos]
    exact (inv_mul_lt_one₀ hlambda_pos).2 hlambda
  have hfactor : lambda • (1 - lambda⁻¹ • A) = lambda • 1 - A := by
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hlambda_pos.ne', one_smul]
  rw [← hfactor, smul_mul_smul, mul_inv_cancel₀ hlambda_pos.ne', one_smul,
    mul_neg_geom_series _ hnorm]

/-- The Neumann-series resolvent is a left inverse of `λI - A`. -/
@[simp] theorem inv_smul_tsum_pow_mul_sub (A : X →L[ℝ] X) {lambda : ℝ}
    (hlambda : ‖A‖ < lambda) :
    (lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n) * (lambda • 1 - A) = 1 := by
  have hlambda_pos : 0 < lambda := lt_of_le_of_lt (norm_nonneg A) hlambda
  have hnorm : ‖lambda⁻¹ • A‖ < 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlambda_pos]
    exact (inv_mul_lt_one₀ hlambda_pos).2 hlambda
  have hfactor : lambda • (1 - lambda⁻¹ • A) = lambda • 1 - A := by
    simp only [smul_sub, smul_smul, mul_inv_cancel₀ hlambda_pos.ne', one_smul]
  rw [← hfactor, smul_mul_smul, inv_mul_cancel₀ hlambda_pos.ne', one_smul,
    geom_series_mul_neg _ hnorm]

/-- For `λ > ‖A‖`, the Laplace-transform resolvent of `t ↦ exp (tA)` is the Neumann series
`λ⁻¹ ∑' n, (λ⁻¹ A)ⁿ`. -/
theorem ofBounded_resolvent_eq_boundedGeneratorResolvent (A : X →L[ℝ] X) {lambda : ℝ}
    (hlambda : ‖A‖ < lambda) :
    (ofBounded A).resolvent (ofBounded_hasGrowthBound A) lambda hlambda =
      lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n := by
  let R := (ofBounded A).resolvent (ofBounded_hasGrowthBound A) lambda hlambda
  have hright : (lambda • 1 - A) * R = 1 := by
    ext x
    have h := (ofBounded A).resolventRightInv
      (ofBounded_hasGrowthBound A) lambda hlambda x
    have hgen :
        (ofBounded A).generator
            ⟨R x, by
              rw [generator_domain]
              exact (ofBounded A).resolvent_mem_domain
                (ofBounded_hasGrowthBound A) lambda hlambda x⟩ = A (R x) := by
      simpa using (LinearPMap.ext_iff.mp (ofBounded_generator A)).2
        (x := R x) (hf := by
          rw [generator_domain]
          exact (ofBounded A).resolvent_mem_domain
            (ofBounded_hasGrowthBound A) lambda hlambda x) (hg := Submodule.mem_top)
    rw [hgen] at h
    simpa using h
  have hseries : R = lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n := by calc
    R = 1 * R := (one_mul R).symm
    _ = ((lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n) * (lambda • 1 - A)) * R := by
      rw [inv_smul_tsum_pow_mul_sub A hlambda]
    _ = (lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n) * ((lambda • 1 - A) * R) :=
      mul_assoc _ _ _
    _ = lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n := by rw [hright, mul_one]
  exact hseries

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
