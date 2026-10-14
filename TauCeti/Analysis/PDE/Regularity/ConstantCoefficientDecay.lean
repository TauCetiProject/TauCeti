/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient

/-!
# Decay estimates for elliptic equations with constant coefficients

Let `A` be a constant `n × n` coefficient matrix whose quadratic form satisfies
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` with `0 < λ`, and let `u` be a `C²` solution of

`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0`

on a ball `B_R = ball x₀ R ⊆ ℝⁿ`, with values in a Banach space. This file proves the two decay
estimates on concentric balls `B_ρ ⊆ B_R` that harmonic functions satisfy
(`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sq_le` and
`InnerProductSpace.HarmonicOnNhd.setIntegral_ball_norm_sub_setAverage_sq_le`), now with constants
depending only on `n` and the ellipticity ratio `Λ / λ`:

`∫_{B_ρ} ‖u‖² ≤ C (ρ / R)ⁿ ∫_{B_R} ‖u‖²`,

`∫_{B_ρ} ‖u - u_ρ‖² ≤ C (ρ / R)^(n + 2) ∫_{B_R} ‖u - c‖²`

for every constant `c`, where `u_ρ` is the average of `u` over `B_ρ`.

These are the decay estimates of the frozen problem in the Campanato approach to Schauder
estimates for equations with variable coefficients: on each ball the coefficients are frozen at
the centre, and the solution is compared with a solution of the resulting constant-coefficient
equation. The Laplacian, the case `A = 1`, is not enough there, since the frozen coefficient
matrix is an arbitrary elliptic matrix.

## The argument

Only the symmetric part `S` of `A` enters the operator, because the second derivative of `u` is
symmetric. Let `T = √S`, the positive square root of the positive definite matrix `S`. By the
chain rule `Δ (u ∘ T) = (∑ᵢⱼ (T Tᵀ)ᵢⱼ ∂ᵢ∂ⱼu) ∘ T`
(`TauCeti.laplacian_comp_toEuclideanCLE_apply`), and `T Tᵀ = S`, so `u` solves the equation
exactly when `u ∘ T` is harmonic (`TauCeti.PDE.exists_continuousLinearEquiv_laplacian_comp_eq`
and `TauCeti.PDE.harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero`, in
`TauCeti/Analysis/PDE/Ellipticity/ConstantCoefficient.lean`). Since
`‖T y‖² = yᵀ A y`, the map `T` stretches lengths by at most `√Λ` and its inverse by at most
`1 / √λ`, and the decay estimates for harmonic functions after a linear change of variables
(`TauCeti.setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp`) give the result with the bound
`√(Λ / λ)` on the condition number of `T` in the constant.

## Main declarations

* `TauCeti.PDE.setIntegral_ball_norm_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`: decay of the `L²`
  mass with exponent `n`.
* `TauCeti.PDE.setIntegral_ball_norm_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`:
  decay of the `L²` mean oscillation with exponent `n + 2`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Chapter 5 (decay estimates for constant coefficients and
  Schauder estimates by Campanato's method).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
-/

public section

open InnerProductSpace MeasureTheory Metric
open scoped Topology

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {A : Matrix ι ι ℝ}

variable [CompleteSpace F] {μ : Measure (EuclideanSpace ℝ ι)} [μ.IsAddHaarMeasure] {lam Lam : ℝ}
  {u : EuclideanSpace ℝ ι → F} {x₀ : EuclideanSpace ℝ ι} {ρ R : ℝ}

/-- **Decay of the `L²` mass for constant coefficients.** Let `A` be a square matrix with
`λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u` be a `C²` solution of
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` on the ball `ball x₀ R ⊆ ℝⁿ`, with `‖u‖²` integrable there. Then for every
`0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u‖² ≤ 2ⁿ (Λ / λ)^(n / 2) (ρ / R)ⁿ ∫_{ball x₀ R} ‖u‖²`.

The constant depends only on `n` and the ellipticity ratio `Λ / λ`. -/
theorem setIntegral_ball_norm_sq_le_of_sum_smul_fderiv_fderiv_eq_zero (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hu : ContDiffOn ℝ 2 u (ball x₀ R))
    (hLu : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0)
    (hint : IntegrableOn (fun x ↦ ‖u x‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x‖ ^ 2 ∂μ ≤
      2 ^ Fintype.card ι * √(Lam / lam) ^ Fintype.card ι * (ρ / R) ^ Fintype.card ι *
        ∫ x in ball x₀ R, ‖u x‖ ^ 2 ∂μ := by
  obtain ⟨e, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := F) hlam hA hA'
  have h := setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp e hae hbe
    (harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hu hLu) hint hρ hρR
  rwa [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at h

/-- **Decay of the `L²` mean oscillation for constant coefficients.** Let `A` be a square matrix
with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u` be a `C²` solution of
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼu = 0` on the ball `ball x₀ R ⊆ ℝⁿ`, with `‖u - c‖²` integrable there for some
constant `c`. Then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖u - u_ρ‖² ≤ C (Λ / λ)^((n + 2) / 2) (ρ / R)^(n + 2) ∫_{ball x₀ R} ‖u - c‖²`
with `C = 2^(3n + 10) (n + 1)²`,

where `u_ρ` is the average of `u` over `ball x₀ ρ`. The constant depends only on `n` and the
ellipticity ratio `Λ / λ`. This is the decay estimate of the frozen problem in the Campanato
approach to Schauder estimates for equations with variable coefficients. -/
theorem setIntegral_ball_norm_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hu : ContDiffOn ℝ 2 u (ball x₀ R))
    (hLu : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0)
    {c : F} (hint : IntegrableOn (fun x ↦ ‖u x - c‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ)
    (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖u x - ⨍ y in ball x₀ ρ, u y ∂μ‖ ^ 2 ∂μ ≤
      2 ^ (3 * Fintype.card ι + 10) * (Fintype.card ι + 1) ^ 2 *
        √(Lam / lam) ^ (Fintype.card ι + 2) * (ρ / R) ^ (Fintype.card ι + 2) *
          ∫ x in ball x₀ R, ‖u x - c‖ ^ 2 ∂μ := by
  obtain ⟨e, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := F) hlam hA hA'
  have h := setIntegral_ball_norm_sub_setAverage_sq_le_of_harmonicOnNhd_comp e hae hbe
    (harmonicOnNhd_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hu hLu) hint hρ hρR
  rwa [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at h

end PDE

end TauCeti
