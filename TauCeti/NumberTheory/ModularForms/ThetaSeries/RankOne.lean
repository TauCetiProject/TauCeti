/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable

/-!
# Rank-one lattice theta series

For any nonzero vector `v` in a real normed space `E`, the theta series of the rank-one lattice
`ℤ v` is Mathlib's `jacobiTheta` evaluated at `‖v‖² τ` (`ZLattice.thetaSeries_span_singleton`).
In particular, the theta series of `ℤ ∙ 1 ⊆ ℝ` is `jacobiTheta τ`, and the theta series of
`√2 ℤ` is `jacobiTheta (2 τ)`. The period-two expansion of `Θ_ℤ` has constant coefficient one,
coefficient two at each positive square, and zero elsewhere. The coefficient two counts the two
signs of a nonzero integer, as in Mathlib's `hasSum_nat_jacobiTheta`.

The comparison reindexes by `LinearEquiv.toSpanNonzeroSingleton`; the analytic series and its
positive-square summation formula are Mathlib's `jacobiTheta` and `hasSum_nat_jacobiTheta`.
For the lattice theta-series convention see Serre, *A Course in Arithmetic*, Ch. VII §6,
and Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Function Submodule
open UpperHalfPlane (qExpansion)
open scoped Real UpperHalfPlane Pointwise

namespace ZLattice

/-- The theta series of the rank-one lattice `ℤ v` (`v ≠ 0`) in a real normed space is Jacobi's
theta function at `‖v‖² τ`. -/
theorem thetaSeries_span_singleton {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : E} (hv : v ≠ 0) (τ : ℍ) :
    thetaSeries (span ℤ {v}) τ = jacobiTheta ((‖v‖ ^ 2 : ℝ) * (τ : ℂ)) := by
  have : Module.IsTorsionFree ℤ E := Module.IsTorsionFree.trans ℝ
  rw [thetaSeries_apply, jacobiTheta,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ E v hv).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.toSpanNonzeroSingleton_apply, norm_zsmul ℝ,
    Real.norm_eq_abs, mul_pow, sq_abs]
  congr 1
  push_cast
  ring

/-- The theta series of the integer lattice, with exponent `π i n² τ`, is Jacobi's theta
function. -/
theorem thetaSeries_span_one (τ : ℍ) :
    thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ = jacobiTheta τ := by
  simpa using thetaSeries_span_singleton (one_ne_zero (α := ℝ)) τ

/-- Scaling the integer lattice by `√2` gives Jacobi's theta function at `2τ`. -/
theorem thetaSeries_sqrt_two_smul_span_one (τ : ℍ) :
    thetaSeries (Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ)) τ = jacobiTheta (2 * (τ : ℂ)) := by
  have hspan : Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ) = span ℤ {Real.sqrt 2} := by
    simp [smul_span]
  rw [hspan, thetaSeries_span_singleton (Real.sqrt_ne_zero'.mpr two_pos)]
  simp

/-- The period-two coefficients of the rank-one lattice theta series, explicitly supported at
the squares. -/
theorem qExpansion_two_thetaSeries_span_one_coeff (m : ℕ) :
    (qExpansion 2 (thetaSeries (span ℤ {1} : Submodule ℤ ℝ))).coeff m =
      if m = 0 then 1 else if IsSquare m then 2 else 0 := by
  rw [isUnimodular_span_one.isIntegral.qExpansion_two_thetaSeries_coeff,
    representationNumber_span_one]
  split_ifs <;> norm_num

/-- The lattice theta series has the period-two square-supported power series, so its terms
have exactly the same multiplicities as Jacobi's positive-square expansion. -/
theorem hasSum_thetaSeries_span_one_qParam (τ : ℍ) :
    HasSum (fun m : ℕ ↦
      (if m = 0 then 1 else if IsSquare m then 2 else 0 : ℂ) * Periodic.qParam 2 τ ^ m)
      (thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ) := by
  classical
  simpa only [representationNumber_span_one, smul_eq_mul, Nat.cast_ite, Nat.cast_one,
    Nat.cast_ofNat, Nat.cast_zero] using
    isUnimodular_span_one.isIntegral.hasSum_thetaSeries_qParam_two τ

end ZLattice
