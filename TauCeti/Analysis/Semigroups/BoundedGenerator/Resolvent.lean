/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.BoundedGenerator.Basic
public import TauCeti.Analysis.Semigroups.Resolvent.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Resolvent of a bounded generator

This file identifies the Laplace-transform resolvent of the uniformly continuous semigroup
`t ↦ exp (tA)` with the Neumann series for `λI - A`.  For `‖A‖ < λ`, the series

`λ⁻¹ ∑' n, (λ⁻¹ A)ⁿ`

converges in the Banach algebra of bounded operators and is a two-sided inverse of `λI - A`.
The general semigroup resolvent is already a right inverse, so the two operators agree.  This
connects the integral construction to Mathlib's Banach-algebra resolvent.

The Neumann formula uses Mathlib's `spectrum.units_smul_resolvent_self` and
`geom_series_eq_inverse`.

## References

See Engel--Nagel, *One-Parameter Semigroups for Linear Evolution Equations*, Section I.3.
-/

public section

noncomputable section

open scoped NNReal

namespace TauCeti.Semigroups

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace StronglyContinuousSemigroup

/-- For `λ > ‖A‖`, the Laplace-transform resolvent of `t ↦ exp (tA)` agrees with
Mathlib's Banach-algebra resolvent of `A`. -/
theorem ofBounded_resolvent_eq_resolvent (A : X →L[ℝ] X) {lambda : ℝ} (hlambda : ‖A‖ < lambda) :
    (ofBounded A).resolvent (ofBounded_hasGrowthBound A) lambda hlambda =
      _root_.resolvent A lambda := by
  have hlambda_pos : 0 < lambda := (norm_nonneg A).trans_lt hlambda
  have hmem : lambda ∈ resolventSet ℝ A := spectrum.mem_resolventSet_of_norm_lt_mul <|
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (norm_nonneg A))
      (by simpa only [Real.norm_eq_abs, abs_of_pos hlambda_pos, mul_one] using hlambda)
  have hright : (lambda • 1 - A) *
      (ofBounded A).resolvent (ofBounded_hasGrowthBound A) lambda hlambda = 1 := by
    ext x
    have h := (ofBounded A).resolventRightInv (ofBounded_hasGrowthBound A) lambda hlambda x
    rw [LinearPMap.congr_fun (ofBounded_generator A) _ Submodule.mem_top] at h
    simpa only [LinearMap.toPMap_domain, LinearMap.toPMap_apply, ContinuousLinearMap.coe_coe,
      mul_apply_eq_comp, sub_apply, smul_apply, one_apply_eq_self] using h
  rw [spectrum.resolvent_eq hmem]
  exact (left_inv_eq_right_inv
    (by simpa only [Units.inv_eq_val_inv, hmem.unit_spec, Algebra.algebraMap_eq_smul_one]
      using hmem.unit.inv_val)
    hright).symm

/-- For `λ > ‖A‖`, the Laplace-transform resolvent of `t ↦ exp (tA)` is the Neumann series
`λ⁻¹ ∑' n, (λ⁻¹ A)ⁿ`. -/
@[simp] theorem ofBounded_resolvent_eq_inv_smul_tsum_pow (A : X →L[ℝ] X) {lambda : ℝ}
    (hlambda : ‖A‖ < lambda) : (ofBounded A).resolvent (ofBounded_hasGrowthBound A) lambda hlambda =
      lambda⁻¹ • ∑' n : ℕ, (lambda⁻¹ • A) ^ n := by
  have hlambda_pos : 0 < lambda := (norm_nonneg A).trans_lt hlambda
  have hnorm : ‖lambda⁻¹ • A‖ < 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlambda_pos,
      inv_mul_lt_one₀ hlambda_pos]
    exact hlambda
  have hseries : lambda • _root_.resolvent A lambda = ∑' n : ℕ, (lambda⁻¹ • A) ^ n := by
    simpa only [Units.smul_def, Units.val_mk0, Units.val_inv_eq_inv_val, _root_.resolvent,
      map_one, ← geom_series_eq_inverse _ hnorm] using
      spectrum.units_smul_resolvent_self (r := Units.mk0 lambda hlambda_pos.ne') (a := A)
  rw [ofBounded_resolvent_eq_resolvent A hlambda, ← hseries, inv_smul_smul₀ hlambda_pos.ne']

end StronglyContinuousSemigroup

end TauCeti.Semigroups

end
