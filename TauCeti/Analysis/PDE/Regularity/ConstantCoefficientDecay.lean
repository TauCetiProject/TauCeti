/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Decay
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import TauCeti.Analysis.PDE.Regularity.Classical
import TauCeti.Analysis.PDE.Regularity.HarmonicReplacement
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap
import TauCeti.Analysis.PDE.Ellipticity.ConstantCoefficient
import TauCeti.Analysis.PDE.EnergyForm.Restriction
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Average

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

for every constant `c`, where `u_ρ` is the average of `u` over `B_ρ`. For a scalar solution the
gradient `∇u` satisfies the same two estimates, and so does the weak gradient of a weak solution
`u ∈ H¹(Ω)` of `-div(A ∇u) = 0` on every ball `B_R ⊆ Ω`.

These are the decay estimates of the frozen problem in the Campanato approach to Schauder
estimates for equations with variable coefficients: on each ball the coefficients are frozen at
the centre, and the solution is compared with a solution of the resulting constant-coefficient
equation. The Laplacian, the case `A = 1`, is not enough there, since the frozen coefficient
matrix is an arbitrary elliptic matrix.

The comparison itself is carried out here for a weak solution in `H¹(Ω)` of
`-div(A ∇u) = -div G` with `G` merely square integrable: the `A`-harmonic replacement `w` of `u`
on `B_r` has the decay above, and the energy estimate `λ ‖∇(u - w)‖_{L²(B_r)} ≤ ‖G - c‖_{L²(B_r)}`
measures the distance between them. For `0 < ρ ≤ r` this gives

`ψ(ρ) ≤ 4 D (ρ / r)^(n + 2) ψ(r) + ((4 D + 2) / λ²) ∫_{B_r} ‖G - c‖²`

in dimension `n`, where `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_t‖²` and `D` is the constant of the decay
estimate for the gradient.

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
`√(Λ / λ)` on the condition number of `T` in the constant. The coordinates of `∇u ∘ T` are
directional derivatives of the harmonic `u ∘ T`, so `∇u ∘ T` is harmonic too
(`TauCeti.PDE.harmonicOnNhd_gradient_comp_of_sum_smul_fderiv_fderiv_eq_zero`), and the same
estimates apply to `∇u`. A weak solution has a smooth representative solving the equation
classically, whose gradient is the weak gradient almost everywhere
(`TauCeti.PDE.UniformlyEllipticOn.exists_contDiffOn_ae_eq_and_divMatrixGradient_eq_zero`).

## Main declarations

* `TauCeti.PDE.setIntegral_ball_norm_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`: decay of the `L²`
  mass with exponent `n`.
* `TauCeti.PDE.setIntegral_ball_norm_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`:
  decay of the `L²` mean oscillation with exponent `n + 2`.
* `TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`: decay of
  the `L²` mass of the gradient of a scalar classical solution, with exponent `n`.
* `PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero`:
  decay of the `L²` mean oscillation of the gradient of a scalar classical solution, with
  exponent `n + 2`.
* `TauCeti.PDE.setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero`: decay of the
  `L²` mass of the weak gradient of a weak solution in `H¹(Ω)`, with exponent `n`.
* `TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero`:
  decay of the `L²` mean oscillation of the weak gradient of a weak solution in `H¹(Ω)`, with
  exponent `n + 2`.
* `TauCeti.PDE.setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq`:
  the comparison with the frozen problem for `-div(A ∇u) = -div G` with `G ∈ L²`.
* `TauCeti.PDE.setIntegral_norm_gradient_sq_le_add_of_frozen` and
  `TauCeti.PDE.setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen`: decay of the `L²`
  mass and of the `L²` mean oscillation of the weak gradient of any `u ∈ H¹(Ω)`, up to its
  energy distance from a weak solution `w` of the constant-coefficient problem on `B_r`.

## References

* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Chapter 5 (decay estimates for constant coefficients and
  Schauder estimates by Campanato's method).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Section 6.1 (reduction of a constant-coefficient operator to the Laplacian by a linear change
  of variables).
-/

public section

open InnerProductSpace MeasureTheory Metric TopologicalSpace
open scoped Gradient Topology

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

section Gradient

variable {g : EuclideanSpace ℝ ι → ℝ}

/-- **Decay of the gradient's `L²` mass for constant coefficients.** Let `A` be a square matrix
with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `g` be a scalar `C²` solution of
`∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼg = 0` on the ball `ball x₀ R ⊆ ℝⁿ`, with `‖∇g‖²` integrable there. Then for every
`0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖∇g‖² ≤ 2ⁿ (Λ / λ)^(n / 2) (ρ / R)ⁿ ∫_{ball x₀ R} ‖∇g‖²`. -/
theorem setIntegral_ball_norm_gradient_sq_le_of_sum_smul_fderiv_fderiv_eq_zero (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hg : ContDiffOn ℝ 2 g (ball x₀ R))
    (hLg : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0)
    (hint : IntegrableOn (fun x ↦ ‖∇ g x‖ ^ 2) (ball x₀ R) μ) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖∇ g x‖ ^ 2 ∂μ ≤
      2 ^ Fintype.card ι * √(Lam / lam) ^ Fintype.card ι * (ρ / R) ^ Fintype.card ι *
        ∫ x in ball x₀ R, ‖∇ g x‖ ^ 2 ∂μ := by
  obtain ⟨e, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  have h := setIntegral_ball_norm_sq_le_of_harmonicOnNhd_comp e hae hbe
    (harmonicOnNhd_gradient_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hg hLg) hint hρ
    hρR
  rwa [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at h

/-- **Decay of the gradient's `L²` mean oscillation for constant coefficients.** Let `A` be a
square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `g` be a scalar `C²` solution
of `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼg = 0` on the ball `ball x₀ R ⊆ ℝⁿ`, with `‖∇g - c‖²` integrable there for some
constant vector `c`. Then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖∇g - (∇g)_ρ‖² ≤ C (Λ / λ)^((n + 2) / 2) (ρ / R)^(n + 2) ∫_{ball x₀ R} ‖∇g - c‖²`
with `C = 2^(3n + 10) (n + 1)²`,

where `(∇g)_ρ` is the average of `∇g` over `ball x₀ ρ`. -/
theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    (hg : ContDiffOn ℝ 2 g (ball x₀ R))
    (hLg : ∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
      fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0)
    {c : EuclideanSpace ℝ ι} (hint : IntegrableOn (fun x ↦ ‖∇ g x - c‖ ^ 2) (ball x₀ R) μ)
    (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖∇ g x - ⨍ y in ball x₀ ρ, ∇ g y ∂μ‖ ^ 2 ∂μ ≤
      2 ^ (3 * Fintype.card ι + 10) * (Fintype.card ι + 1) ^ 2 *
        √(Lam / lam) ^ (Fintype.card ι + 2) * (ρ / R) ^ (Fintype.card ι + 2) *
          ∫ x in ball x₀ R, ‖∇ g x - c‖ ^ 2 ∂μ := by
  obtain ⟨e, hae, hbe, he⟩ := exists_continuousLinearEquiv_laplacian_comp_eq (F := ℝ) hlam hA hA'
  have h := setIntegral_ball_norm_sub_setAverage_sq_le_of_harmonicOnNhd_comp e hae hbe
    (harmonicOnNhd_gradient_comp_of_sum_smul_fderiv_fderiv_eq_zero he isOpen_ball hg hLg) hint hρ
    hρR
  rwa [finrank_euclideanSpace, inv_mul_eq_div, ← Real.sqrt_div' _ hlam.le] at h

end Gradient

section Weak

variable {Omega : Opens (EuclideanSpace ℝ ι)}

/-- A weak solution of `-div(A ∇u) = 0` with constant elliptic `A` has a smooth representative
`g` on a ball `B ⊆ Ω` that solves `∑ᵢⱼ Aᵢⱼ ∂ᵢ∂ⱼg = 0` there classically, and whose gradient is the
weak gradient of `u` almost everywhere on `B`. -/
private theorem exists_contDiffOn_ball_and_gradient_ae_eq (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => A) 0 0 u (v : W1p volume Omega 2) = 0)
    (hball : ball x₀ R ⊆ Omega) :
    ∃ g : EuclideanSpace ℝ ι → ℝ, ContDiffOn ℝ 2 g (ball x₀ R) ∧
      (∀ x ∈ ball x₀ R, ∑ i, ∑ j, A i j •
        fderiv ℝ (fderiv ℝ g) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) = 0) ∧
      (W1p.gradient u : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) =ᵐ[volume.restrict (ball x₀ R)]
        ∇ g := by
  obtain ⟨g, hg, -, hgrad, hdiv⟩ :=
    UniformlyEllipticOn.exists_contDiffOn_ae_eq_and_divMatrixGradient_eq_zero hlam
      (fun ξ => by simpa [Matrix.toQuadraticForm'_apply] using hA ξ) hu
  have hg2 : ContDiffOn ℝ 2 g Omega := hg.of_le (by simp)
  refine ⟨g, hg2.mono hball, fun x hx => ?_, ae_restrict_of_ae_restrict_of_subset hball hgrad⟩
  -- The classical operator `div(A ∇g)` is the contraction of `A` against the Hessian of `g`.
  have hg1 : ContDiffOn ℝ 1 (fderiv ℝ g) Omega := hg2.fderiv_of_isOpen Omega.isOpen (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    (hg1.differentiableOn one_ne_zero).differentiableAt (Omega.isOpen.mem_nhds (hball hx))
  rw [← hdiv x (hball hx), divMatrixGradient_eq_sum_fderiv_fderiv_apply hg2 (hball hx)]
  simp only [fderiv_clm_apply_const_apply hd, EuclideanSpace.basisFun_apply, smul_eq_mul]

/-- **Decay of the weak gradient's `L²` mass for constant coefficients.** Let `A` be a square
matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u ∈ H¹(Ω)` be a weak solution of
`-div(A ∇u) = 0` on an open set `Ω ⊆ ℝⁿ`, that is `∫_Ω ⟨A ∇u, ∇v⟩ = 0` for every `v ∈ H¹₀(Ω)`. If
`ball x₀ R ⊆ Ω`, then for every `0 ≤ ρ ≤ R`,

`∫_{ball x₀ ρ} ‖∇u‖² ≤ 2ⁿ (Λ / λ)^(n / 2) (ρ / R)ⁿ ∫_{ball x₀ R} ‖∇u‖²`.

No boundary condition on `u` is assumed. -/
theorem setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => A) 0 0 u (v : W1p volume Omega 2) = 0)
    (hball : ball x₀ R ⊆ Omega) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
      2 ^ Fintype.card ι * √(Lam / lam) ^ Fintype.card ι * (ρ / R) ^ Fintype.card ι *
        ∫ x in ball x₀ R, ‖W1p.gradient u x‖ ^ 2 := by
  obtain ⟨g, hg, hLg, hgrad⟩ := exists_contDiffOn_ball_and_gradient_ae_eq hlam hA hu hball
  have hgradρ := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR) hgrad
  have hint : IntegrableOn (fun x ↦ ‖∇ g x‖ ^ 2) (ball x₀ R) :=
    (((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)).ae_eq
      hgrad).integrable_norm_pow two_ne_zero
  rw [integral_congr_ae (hgradρ.mono fun x hx => by rw [hx]),
    integral_congr_ae (hgrad.mono fun x hx => by rw [hx])]
  exact setIntegral_ball_norm_gradient_sq_le_of_sum_smul_fderiv_fderiv_eq_zero hlam hA hA' hg hLg
    hint hρ hρR

/-- **Decay of the weak gradient's `L²` mean oscillation for constant coefficients.** Let `A` be
a square matrix with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²` and `0 < λ`, and let `u ∈ H¹(Ω)` be a weak solution
of `-div(A ∇u) = 0` on an open set `Ω ⊆ ℝⁿ`, that is `∫_Ω ⟨A ∇u, ∇v⟩ = 0` for every
`v ∈ H¹₀(Ω)`. If `ball x₀ R ⊆ Ω`, then for every `0 ≤ ρ ≤ R` and every constant vector `c`,

`∫_{ball x₀ ρ} ‖∇u - (∇u)_ρ‖² ≤ C (Λ / λ)^((n + 2) / 2) (ρ / R)^(n + 2) ∫_{ball x₀ R} ‖∇u - c‖²`
with `C = 2^(3n + 10) (n + 1)²`,

where `(∇u)_ρ` is the average of `∇u` over `ball x₀ ρ`. No boundary condition on `u` is assumed.
This is the decay estimate of the frozen problem in Campanato's proof of the Schauder estimates
for divergence-form equations with Hölder continuous coefficients. -/
theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
    (hlam : 0 < lam)
    (hA : ∀ ξ : EuclideanSpace ℝ ι, lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hA' : ∀ ξ : EuclideanSpace ℝ ι, A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {u : W1p volume Omega 2}
    (hu : ∀ v : W1p0 volume Omega 2,
      energyFormH1 (fun _ => A) 0 0 u (v : W1p volume Omega 2) = 0)
    (hball : ball x₀ R ⊆ Omega) (c : EuclideanSpace ℝ ι) (hρ : 0 ≤ ρ) (hρR : ρ ≤ R) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      2 ^ (3 * Fintype.card ι + 10) * (Fintype.card ι + 1) ^ 2 *
        √(Lam / lam) ^ (Fintype.card ι + 2) * (ρ / R) ^ (Fintype.card ι + 2) *
          ∫ x in ball x₀ R, ‖W1p.gradient u x - c‖ ^ 2 := by
  obtain ⟨g, hg, hLg, hgrad⟩ := exists_contDiffOn_ball_and_gradient_ae_eq hlam hA hu hball
  have hgradρ := ae_restrict_of_ae_restrict_of_subset (ball_subset_ball hρR) hgrad
  have : IsFiniteMeasure (volume.restrict (ball x₀ R)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have hint : IntegrableOn (fun x ↦ ‖∇ g x - c‖ ^ 2) (ball x₀ R) :=
    ((((Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)).ae_eq
      hgrad).sub (memLp_const c)).integrable_norm_pow two_ne_zero
  rw [average_congr hgradρ, integral_congr_ae (hgradρ.mono fun x hx => by rw [hx]),
    integral_congr_ae (hgrad.mono fun x hx => by rw [hx])]
  exact setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_sum_smul_fderiv_fderiv_eq_zero
    hlam hA hA' hg hLg hint hρ hρR

end Weak

section Comparison

open scoped Distributions InnerProductSpace

variable {n : ℕ} {A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ}
  {Omega : Opens (EuclideanSpace ℝ (Fin (n + 1)))} {x₀ : EuclideanSpace ℝ (Fin (n + 1))} {ρ r : ℝ}

/-- For a weak solution `u` of `-div(A ∇u) = -div G` on a ball `B_r ⊆ Ω`, with `G - c` square
integrable on `B_r`, there is an `A`-harmonic `w ∈ H¹(B_r)` (that is, `∫ ⟨A∇w, ∇v⟩ = 0` for all
`v ∈ H¹₀(B_r)`) with `∫_{B_r} ‖∇u - ∇w‖² ≤ λ⁻² ∫_{B_r} ‖G - c‖²`. -/
private theorem exists_forall_energyFormH1_eq_zero_setIntegral_norm_gradient_sub_sq_le
    {lam Lam : ℝ} (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    {u : W1p volume Omega 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ r ⊆ Omega) {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (ball x₀ r))) :
    ∃ w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      (∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
        energyFormH1 (fun _ => A) 0 0 w (v : W1p volume _ 2) = 0) ∧
      ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
        (∫ x in ball x₀ r, ‖G x - c‖ ^ 2) / lam ^ 2 := by
  set B : Opens (EuclideanSpace ℝ (Fin (n + 1))) := ⟨ball x₀ r, isOpen_ball⟩
  have hB : B ≤ Omega := hball
  have hlam : 0 < lam := hA.pos
  -- The `A`-harmonic replacement `w` of `u` on `B_r`.
  obtain ⟨w, ⟨hwu, hw⟩, -⟩ :=
    UniformlyEllipticOn.existsUnique_sub_mem_w1p0Submodule_forall_energyFormH1_eq_of_subset_ball
      (Omega := B) (b := 0) (c := 0) hA aestronglyMeasurable_const aestronglyMeasurable_const
      aestronglyMeasurable_const (beta := 0) (fun _ _ => by simp) (gamma := 0)
      (fun _ _ => by simp) (fun _ _ => le_rfl) subset_rfl (by simpa using hlam) 0
      (W1p.restrictL hB u)
  have hw0 : ∀ v : W1p0 volume B 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume B 2) = 0 := fun v => by
    rw [hw v, zero_apply]
  have huw : W1p.restrictL hB u - w ∈ w1p0Submodule volume B 2 := by
    have h := (ClosedSubmodule.mem_toSubmodule_iff (w - W1p.restrictL hB u)
      (w1p0Submodule volume B 2)).2 hwu
    exact (ClosedSubmodule.mem_toSubmodule_iff _ _).1 (sub_mem_comm_iff.1 h)
  -- The energy distance between `u` and `w` is controlled by `G - c`.
  have hAB : UniformlyEllipticOn (B : Set (EuclideanSpace ℝ (Fin (n + 1)))) (fun _ => A) lam Lam :=
    hA
  have hGcB : MemLp (fun x => G x - c) 2
      (volume.restrict (B : Set (EuclideanSpace ℝ (Fin (n + 1))))) := hGc
  have hrep : ∀ v : W1p0 volume B 2,
      energyFormH1 (fun _ => A) 0 0 (W1p.restrictL hB u) (v : W1p volume B 2) =
        ⟪hGcB.toLp, W1p.gradient (v : W1p volume B 2)⟫_ℝ :=
    forall_energyFormH1_restrictL_eq_inner hB
      (memLp_top_const (energyIntegrand A 0 0)) hu hGcB
  have hest : lam * ‖W1p.gradient (W1p.restrictL hB u - w)‖ ≤ ‖hGcB.toLp‖ :=
    hAB.mul_norm_gradient_sub_le aestronglyMeasurable_const huw hw0 hrep
  have hGn : ‖hGcB.toLp‖ ^ 2 = ∫ x in ball x₀ r, ‖G x - c‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [hGcB.coeFn_toLp] with x hx
    rw [hx]
  have hE' : ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
      (∫ x in ball x₀ r, ‖G x - c‖ ^ 2) / lam ^ 2 := by
    calc ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2
        = ‖W1p.gradient (W1p.restrictL hB u - w)‖ ^ 2 :=
          W1p.setIntegral_norm_gradient_sub_sq_eq hB u w
      _ ≤ _ := by
          rw [← hGn, le_div_iff₀ (by positivity), ← mul_pow, mul_comm]
          exact pow_le_pow_left₀ (by positivity) hest 2
  exact ⟨w, hw0, hE'⟩

/-- **Comparison with the frozen problem for constant coefficients.** Let `A` be a constant
coefficient matrix, uniformly elliptic with constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` solve
`-div(A ∇u) = -div G` weakly on an open set `Ω ⊆ ℝ^{n+1}`, that is
`∫_Ω ⟨A ∇u, ∇φ⟩ = ∫_Ω ⟨G, ∇φ⟩` for every test function `φ`. Let `ball x₀ r ⊆ Ω` and let `c` be a
constant vector with `G - c` square integrable on `ball x₀ r`. Then for `0 < ρ ≤ r` the square mean
oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` of the gradient satisfies

`ψ(ρ) ≤ 4 D (ρ / r)^(n + 3) ψ(r) + ((4 D + 2) / λ²) ∫_{B_r} ‖G - c‖²`,

with `D = 2^(3n + 13) (n + 2)² (Λ / λ)^((n + 3) / 2)`. No regularity of `G` and no boundary
condition on `u` is assumed. -/
theorem setIntegral_ball_norm_gradient_sub_setAverage_sq_le_add_of_forall_energyFormH1_eq
    {lam Lam : ℝ} (hA : UniformlyEllipticOn (ball x₀ r) (fun _ => A) lam Lam)
    {u : W1p volume Omega 2}
    {G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))}
    (hu : ∀ φ : 𝓓(Omega, ℝ),
      energyFormH1 (fun _ => A) 0 0 u (W1p.ofTestFunctionₗ volume Omega 2 φ) =
        ∫ x in Omega, ⟪G x, ∇ (φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) x⟫_ℝ)
    (hball : ball x₀ r ⊆ Omega) {c : EuclideanSpace ℝ (Fin (n + 1))}
    (hGc : MemLp (fun x => G x - c) 2 (volume.restrict (ball x₀ r))) (hρ : 0 < ρ)
    (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) * (ρ / r) ^ (n + 3) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        (4 * (2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3)) + 2) / lam ^ 2 *
          ∫ x in ball x₀ r, ‖G x - c‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hlam : 0 < lam := hA.pos
  have hx₀ : x₀ ∈ ball x₀ r := mem_ball_self hr
  have hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2 :=
    fun ξ => (le_abs_self _).trans
      (abs_toQuadraticForm'_le_of_abs_dotProduct_mulVec_le (hA.upper_bound hx₀) ξ)
  obtain ⟨w, hw0, hE'⟩ :=
    exists_forall_energyFormH1_eq_zero_setIntegral_norm_gradient_sub_sq_le hA hu hball hGc
  -- The gradient of the replacement decays from `B_r` to `B_ρ`.
  have hdec := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
    hlam (hA.lower_bound hx₀) hAu hw0 (x₀ := x₀) (R := r) subset_rfl
    (⨍ y in ball x₀ r, W1p.gradient u y) hρ.le hρr
  have hfm : MemLp
      (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp
      (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))) 2
      (volume.restrict (ball x₀ r)) := Lp.memLp (W1p.gradient w)
  have hcomp := setIntegral_norm_sub_setAverage_sq_le_add_of_subset (ball_subset_ball hρr)
    measure_ball_lt_top.ne hfm hHm (by positivity) hdec
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = 2 ^ (3 * n + 13) * (n + 2) ^ 2 * √(Lam / lam) ^ (n + 3) :=
    ⟨_, rfl⟩
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (ρ / r) ^ (n + 3) := ⟨_, rfl⟩
  have hK : 2 ^ (3 * Fintype.card (Fin (n + 1)) + 10) * ((Fintype.card (Fin (n + 1)) : ℝ) + 1) ^ 2 *
      √(Lam / lam) ^ (Fintype.card (Fin (n + 1)) + 2) * (ρ / r) ^ (Fintype.card (Fin (n + 1)) + 2) =
        D * q := by
    rw [hDdef, hqdef, Fintype.card_fin]
    push_cast
    ring
  rw [hK] at hcomp
  have hq1 : q ≤ 1 := hqdef ▸ pow_le_one₀ (by positivity) ((div_le_one hr).2 hρr)
  have hD : 0 ≤ D := hDdef ▸ by positivity
  have hE0 : 0 ≤ ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 :=
    integral_nonneg fun _ => by positivity
  have h1 : (4 * (D * q) + 2) * ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 ≤
      (4 * D + 2) / lam ^ 2 * ∫ x in ball x₀ r, ‖G x - c‖ ^ 2 := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul (by nlinarith) hE' hE0 (by positivity)
  rw [← hDdef, ← hqdef]
  refine hcomp.trans (add_le_add (le_of_eq ?_) h1)
  ring


/-- **Decay of the `L²` mass of the gradient, by comparison.** Let `u ∈ H¹(Ω)`, let
`ball x₀ r ⊆ Ω`, and let `w ∈ H¹(B_r)` solve `-∂ᵢ(Aⁱʲ ∂ⱼw) = 0` weakly on `B_r` for a constant
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²`, `λ > 0`. Then for `0 < ρ ≤ r`
`∫_{B_ρ} ‖∇u‖² ≤ 4 D (ρ / r)^{n+1} ∫_{B_r} ‖∇u‖² + (4 D + 2) ∫_{B_r} ‖∇u - ∇w‖²`, with
`D = 2^{n+1} (Λ / λ)^{(n+1)/2}`. -/
theorem setIntegral_norm_gradient_sq_le_add_of_frozen
    {u : W1p volume Omega 2} {lam Lam : ℝ} (hlam : 0 < lam)
    (hAl : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw0 : ∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume _ 2) = 0)
    (hball : ball x₀ r ⊆ Omega) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x‖ ^ 2 ≤
      4 * (2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) * (ρ / r) ^ (n + 1) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x‖ ^ 2) +
        (4 * (2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) + 2) *
          ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hfm : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    Lp.memLp (W1p.gradient w)
  have hq0 : 0 ≤ ρ / r := by positivity
  have hdec := setIntegral_ball_norm_gradient_sq_le_of_forall_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ r, isOpen_ball⟩) hlam hAl hAu hw0 (x₀ := x₀) (R := r)
    (fun _ hx => hx) hρ.le hρr
  rw [Fintype.card_fin] at hdec
  have hf2 : IntegrableOn (fun x => ‖W1p.gradient u x‖ ^ 2) (ball x₀ r) :=
    hfm.integrable_norm_pow two_ne_zero
  have hH2 : IntegrableOn (fun x => ‖W1p.gradient w x‖ ^ 2) (ball x₀ r) :=
    hHm.integrable_norm_pow two_ne_zero
  have hcomp := MeasureTheory.setIntegral_norm_sub_sq_le_add_of_le (b := 0) (k := 0) (c := 0)
    (D := 2 ^ (n + 1) * √(Lam / lam) ^ (n + 1)) (ball_subset_ball hρr) (by positivity)
    (pow_nonneg hq0 _) (pow_le_one₀ hq0 ((div_le_one hr).2 hρr))
    (by simpa only [sub_zero] using hf2)
    (by simpa only [sub_zero] using hH2.mono_set (ball_subset_ball hρr))
    ((hfm.sub hHm).integrable_norm_pow two_ne_zero) le_rfl
    (by simpa only [sub_zero] using hdec)
  simpa only [sub_zero] using hcomp

/-- **Decay of the mean oscillation of the gradient, by comparison.** Let `u ∈ H¹(Ω)`, let
`ball x₀ r ⊆ Ω`, and let `w ∈ H¹(B_r)` solve `-∂ᵢ(Aⁱʲ ∂ⱼw) = 0` weakly on `B_r` for a constant
matrix `A` with `λ ‖ξ‖² ≤ ξᵀ A ξ ≤ Λ ‖ξ‖²`, `λ > 0`. Then for `0 < ρ ≤ r` the square mean
oscillation `ψ(t) = ∫_{B_t} ‖∇u - (∇u)_{B_t}‖²` satisfies
`ψ(ρ) ≤ 4 D (ρ / r)^{n+3} ψ(r) + (4 D + 2) ∫_{B_r} ‖∇u - ∇w‖²`, with
`D = 2^{3n+13} (n + 2)² (Λ / λ)^{(n+3)/2}`. -/
theorem setIntegral_norm_gradient_sub_setAverage_sq_le_add_of_frozen
    {u : W1p volume Omega 2} {lam Lam : ℝ} (hlam : 0 < lam)
    (hAl : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), lam * ‖ξ‖ ^ 2 ≤ A.toQuadraticForm' ξ)
    (hAu : ∀ ξ : EuclideanSpace ℝ (Fin (n + 1)), A.toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2)
    {w : W1p volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2}
    (hw0 : ∀ v : W1p0 volume (⟨ball x₀ r, isOpen_ball⟩ : Opens (EuclideanSpace ℝ (Fin (n + 1)))) 2,
      energyFormH1 (fun _ => A) 0 0 w (v : W1p volume _ 2) = 0)
    (hball : ball x₀ r ⊆ Omega) (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    ∫ x in ball x₀ ρ, ‖W1p.gradient u x - ⨍ y in ball x₀ ρ, W1p.gradient u y‖ ^ 2 ≤
      4 * (2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)) *
          (ρ / r) ^ (n + 1 + 2) *
          (∫ x in ball x₀ r, ‖W1p.gradient u x - ⨍ y in ball x₀ r, W1p.gradient u y‖ ^ 2) +
        (4 * (2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2)) + 2) *
          ∫ x in ball x₀ r, ‖W1p.gradient u x - W1p.gradient w x‖ ^ 2 := by
  have hr : 0 < r := hρ.trans_le hρr
  have hfm : MemLp (W1p.gradient u : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    (Lp.memLp (W1p.gradient u)).mono_measure (Measure.restrict_mono hball le_rfl)
  have hHm : MemLp (W1p.gradient w : EuclideanSpace ℝ (Fin (n + 1)) →
      EuclideanSpace ℝ (Fin (n + 1))) 2 (volume.restrict (ball x₀ r)) :=
    Lp.memLp (W1p.gradient w)
  have hq0 : 0 ≤ ρ / r := by positivity
  have hρs : ball x₀ ρ ⊆ ball x₀ r := ball_subset_ball hρr
  have hdec := setIntegral_ball_norm_gradient_sub_setAverage_sq_le_of_forall_energyFormH1_eq_zero
    (Omega := ⟨ball x₀ r, isOpen_ball⟩) hlam hAl hAu hw0 (x₀ := x₀) (R := r)
    (fun _ hx => hx) (⨍ y in ball x₀ r, W1p.gradient u y) hρ.le hρr
  rw [Fintype.card_fin] at hdec
  exact MeasureTheory.setIntegral_norm_sub_sq_le_add_of_le hρs
    (D := 2 ^ (3 * (n + 1) + 10) * ((n + 1 : ℕ) + 1) ^ 2 * √(Lam / lam) ^ (n + 1 + 2))
    (by positivity) (pow_nonneg hq0 _)
    (pow_le_one₀ hq0 ((div_le_one hr).2 hρr))
    (hfm.integrableOn_norm_sub_sq_of_subset subset_rfl measure_ball_lt_top.ne _)
    (hHm.integrableOn_norm_sub_sq_of_subset hρs measure_ball_lt_top.ne _)
    ((hfm.sub hHm).integrable_norm_pow two_ne_zero)
    (setIntegral_norm_sub_setAverage_sq_le_setIntegral_norm_sub_sq measure_ball_lt_top.ne
      (hfm.integrableOn_of_subset one_le_two hρs measure_ball_lt_top.ne)
      (hfm.integrableOn_norm_sub_sq_of_subset hρs measure_ball_lt_top.ne _)) hdec

end Comparison

end PDE

end TauCeti
