/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.ThetaSeries.Functoriality
public import TauCeti.NumberTheory.ModularForms.ThetaSeries.QExpansion
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import TauCeti.LinearAlgebra.Span.Basic

/-!
# Rank-one lattice theta series

The theta series of `ℤ ∙ 1 ⊆ ℝ` is Mathlib's `jacobiTheta`, with exponent `π i n² τ`.
More generally, for `c ≠ 0` the theta series of `c ℤ ⊆ ℝ` is `jacobiTheta (c² τ)`
(`ZLattice.thetaSeries_span_singleton`), so `Θ_{√2 ℤ}(τ) = jacobiTheta (2 τ)`,
`Θ_{2 ℤ}(τ) = jacobiTheta (4 τ)`, and `Θ_{½ ℤ}(τ) = jacobiTheta (τ / 4)`.
The period-two expansion of `Θ_ℤ` has constant coefficient one, coefficient two at each positive
square, and zero elsewhere; the coefficient two counts the two signs of a nonzero integer, as in
Mathlib's `hasSum_nat_jacobiTheta`.

The comparison reindexes by `LinearEquiv.toSpanNonzeroSingleton`; the analytic series and its
positive-square summation formula are Mathlib's `jacobiTheta` and `hasSum_nat_jacobiTheta`.

## Main statements

* `ZLattice.thetaSeries_span_one`, `ZLattice.thetaSeries_span_singleton`,
  `ZLattice.thetaSeries_sqrt_two_smul_span_one`, `ZLattice.thetaSeries_span_two`,
  `ZLattice.thetaSeries_span_one_half`: comparison of `Θ_{c ℤ}` with `jacobiTheta (c² τ)`.
* `ZLattice.qExpansion_two_thetaSeries_span_one_coeff`,
  `ZLattice.hasSum_thetaSeries_span_one_qParam`: the period-two `q`-expansion of `Θ_ℤ`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Ch. VII §6.
* W. Ebeling, *Lattices and Codes*, Ch. 2.
-/

public section

open Complex Function Submodule
open UpperHalfPlane (qExpansion)
open scoped Real UpperHalfPlane Pointwise

namespace ZLattice

/-- The theta series of the integer lattice, with exponent `π i n² τ`, is Jacobi's theta
function. -/
theorem thetaSeries_span_one (τ : ℍ) :
    thetaSeries (span ℤ {1} : Submodule ℤ ℝ) τ = jacobiTheta τ := by
  rw [thetaSeries_apply, jacobiTheta,
    ← (LinearEquiv.toSpanNonzeroSingleton ℤ ℝ 1 one_ne_zero).toEquiv.tsum_eq]
  refine tsum_congr fun n ↦ ?_
  simp [Real.norm_eq_abs, sq_abs]

/-- For a nonzero real number `c`, the theta series of `c ℤ ⊆ ℝ` is Jacobi's theta function at
`c² τ`. -/
theorem thetaSeries_span_singleton {c : ℝ} (hc : c ≠ 0) (τ : ℍ) :
    thetaSeries (span ℤ {c} : Submodule ℤ ℝ) τ = jacobiTheta ((c ^ 2 : ℝ) * (τ : ℂ)) := by
  nth_rw 1 [← mul_one c]
  rw [← smul_eq_mul, ← Submodule.smul_span_singleton, thetaSeries_smul _ hc,
    thetaSeries_span_one, UpperHalfPlane.coe_pos_real_smul, Complex.real_smul]

/-- Scaling the integer lattice by `√2` gives Jacobi's theta function at `2τ`. -/
theorem thetaSeries_sqrt_two_smul_span_one (τ : ℍ) :
    thetaSeries (Real.sqrt 2 • (span ℤ {1} : Submodule ℤ ℝ)) τ = jacobiTheta (2 * (τ : ℂ)) := by
  rw [thetaSeries_smul _ (Real.sqrt_ne_zero'.mpr two_pos), thetaSeries_span_one]
  congr 1
  simp [Complex.real_smul]

/-- The theta series of `2 ℤ ⊆ ℝ` is Jacobi's theta function at `4τ`. -/
theorem thetaSeries_span_two (τ : ℍ) :
    thetaSeries (span ℤ {2} : Submodule ℤ ℝ) τ = jacobiTheta (4 * (τ : ℂ)) := by
  rw [thetaSeries_span_singleton two_ne_zero]
  norm_num

/-- The theta series of `½ ℤ ⊆ ℝ` is Jacobi's theta function at `τ / 4`. -/
theorem thetaSeries_span_one_half (τ : ℍ) :
    thetaSeries (span ℤ {1 / 2} : Submodule ℤ ℝ) τ = jacobiTheta ((τ : ℂ) / 4) := by
  rw [thetaSeries_span_singleton (one_div_ne_zero two_ne_zero)]
  congr 1
  push_cast
  ring

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
