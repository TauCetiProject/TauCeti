/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Matrix.CovariancePseudoInverse
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Gaussian

import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Analysis.Matrix.Sqrt
import TauCeti.Probability.Distributions.Gaussian.Projection

/-!
# Laws of Gaussian quadratic forms

Let `X` have the multivariate Gaussian law `N(m, S)` on `ℝᵏ`. This file identifies the laws of
three quadratic statistics of `X`.

* For positive-definite `S`, the form `Xᵀ S⁻¹ X` has the noncentral chi-squared law with `k`
  degrees of freedom and noncentrality `mᵀ S⁻¹ m`. The inverse square root of `S` carries `X` to
  a Gaussian vector with identity covariance, whose squared norm is noncentral chi-squared.
* For positive-semidefinite `S` and `m = 0`, the form `Xᵀ S⁺ X` in the Moore–Penrose inverse
  `S⁺ = Matrix.covariancePseudoInverse S` has the chi-squared law with `rank S` degrees of
  freedom. Writing `X = √S Z` with `Z` standard Gaussian, the form is `‖P Z‖²`, where `P = S⁺ S`
  is the orthogonal projection onto the range of `S`.
* For positive-semidefinite `S` and `m = 0`, the squared norm `‖X‖²` has the law of
  `∑ⱼ λⱼ Zⱼ²`, where `λⱼ` are the eigenvalues of `S` and the `Zⱼ` are independent standard
  normal variables.

The `HasLaw` forms transfer the first two statements to random vectors on any probability space.

The central case of the first statement is adapted from the lean-CKSD project
(<https://github.com/bjbraams/lean-CKSD>, `CKSD/LinearModels/Multivariate/SampleLaws.lean`).

## Main results

* `TauCeti.Probability.map_quadForm_inv_multivariateGaussian`: the noncentral chi-squared law of
  `Xᵀ S⁻¹ X`;
* `TauCeti.Probability.map_quadForm_pseudoInverse_multivariateGaussian`: the chi-squared law of
  `Xᵀ S⁺ X` for singular `S`;
* `TauCeti.Probability.map_norm_sq_multivariateGaussian_eq_map_sum_eigenvalues_mul_sq`: the law
  of `‖X‖²` as a weighted sum of squares of independent standard normal variables.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press (1998), Lemma 17.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Gaussian quadratic form in the inverse covariance.** For positive-definite `S`, the
quadratic form `xᵀ S⁻¹ x` under `N(m, S)` has the noncentral chi-squared law with `card ι`
degrees of freedom and noncentrality `mᵀ S⁻¹ m`. -/
theorem map_quadForm_inv_multivariateGaussian (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ)
    (hS : S.PosDef) :
    (multivariateGaussian m S).map (fun x ↦ WithLp.ofLp x ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp x)) =
      noncentralChiSquaredMeasure (Fintype.card ι)
        (WithLp.ofLp m ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp m)).toNNReal := by
  have hq (x : EuclideanSpace ℝ ι) :
      WithLp.ofLp x ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp x) = ‖(CFC.sqrt S)⁻¹.toEuclideanLin x + 0‖ ^ 2 := by
    rw [add_zero, hS.posSemidef.norm_sq_toEuclideanLin_inv_sqrt,
      Matrix.dotProduct_mulVec_eq_inner_toEuclideanLin]
  have hu := hS.isUnit_det_sqrt
  have hT : ((CFC.sqrt S)⁻¹).transpose = (CFC.sqrt S)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, ← Matrix.conjTranspose_eq_transpose_of_trivial,
      (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg S)).isHermitian.eq]
  have hcov : (CFC.sqrt S)⁻¹ * S * ((CFC.sqrt S)⁻¹).transpose = 1 := by
    calc (CFC.sqrt S)⁻¹ * S * ((CFC.sqrt S)⁻¹).transpose
        _ = (CFC.sqrt S)⁻¹ * (CFC.sqrt S * CFC.sqrt S) * (CFC.sqrt S)⁻¹ := by
          rw [hT, CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]
        _ = 1 := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul,
            Matrix.mul_nonsing_inv _ hu]
  have hf : (fun x : EuclideanSpace ℝ ι ↦ WithLp.ofLp x ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp x)) =
      (fun y ↦ ‖y‖ ^ 2) ∘ fun x ↦ (CFC.sqrt S)⁻¹.toEuclideanLin x + 0 := by
    funext x
    exact hq x
  rw [hf, ← Measure.map_map (by fun_prop) (by fun_prop),
    map_affine_multivariateGaussian m hS.posSemidef (CFC.sqrt S)⁻¹ 0, hcov,
    map_norm_sq_multivariateGaussian_noncentral, hq m]
  congr 1
  ext
  simp

/-- **Gaussian quadratic form in the pseudoinverse.** Under `N(0, S)` with `S` positive
semidefinite, the quadratic form `xᵀ S⁺ x` in the Moore–Penrose inverse `S⁺` has the
chi-squared law with `rank S` degrees of freedom. Singular and zero `S` are included. -/
theorem map_quadForm_pseudoInverse_multivariateGaussian (S : Matrix ι ι ℝ)
    (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map
        (fun x ↦ WithLp.ofLp x ⬝ᵥ (S.covariancePseudoInverse *ᵥ WithLp.ofLp x)) =
      chiSquaredMeasure S.rank := by
  have hf : (fun x : EuclideanSpace ℝ ι ↦
        WithLp.ofLp x ⬝ᵥ (S.covariancePseudoInverse *ᵥ WithLp.ofLp x)) ∘
        Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt S) =
      fun z ↦ ‖(LinearMap.range S.toEuclideanLin).starProjection z‖ ^ 2 := by
    funext z
    rw [Function.comp_apply, Matrix.dotProduct_mulVec_eq_inner_toEuclideanLin,
      Matrix.inner_toEuclideanCLM_sqrt_toEuclideanLin,
      Matrix.sqrt_mul_covariancePseudoInverse_mul_sqrt,
      Matrix.toEuclideanLin_covariancePseudoInverse_mul hS, ContinuousLinearMap.coe_coe,
      real_inner_comm]
    have h := (LinearMap.range S.toEuclideanLin).re_inner_starProjection_eq_normSq z
    rw [RCLike.re_to_real] at h
    rw [h, Submodule.starProjection_apply, Submodule.norm_coe]
  rw [multivariateGaussian_zero_eq_map_stdGaussian_sqrt, Measure.map_map (by fun_prop)
    (by fun_prop), hf, Submodule.map_norm_sq_starProjection_stdGaussian,
    Matrix.rank_eq_finrank_range_toEuclideanLin]

/-- **Squared norm of a centred Gaussian vector.** Under `N(0, S)` with `S` positive
semidefinite, `‖x‖²` has the law of `∑ j, λ j * Z j ^ 2`, where `λ` are the eigenvalues of `S`
and the `Z j` are independent standard normal variables. -/
theorem map_norm_sq_multivariateGaussian_eq_map_sum_eigenvalues_mul_sq {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) :
    (multivariateGaussian 0 S).map (fun x ↦ ‖x‖ ^ 2) =
      (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
        (fun z ↦ ∑ j, hS.isHermitian.eigenvalues j * z j ^ 2) := by
  have hB := hS.isHermitian
  rw [multivariateGaussian_zero_eq_map_stdGaussian_sqrt,
    stdGaussian_eq_map_pi_orthonormalBasis hB.eigenvectorBasis,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply]
  have h := Matrix.inner_toEuclideanCLM_sqrt_toEuclideanLin S 1
    (∑ j, z j • hB.eigenvectorBasis j)
  rw [Matrix.mul_one, CFC.sqrt_mul_sqrt_self S hS.nonneg,
    hB.inner_toEuclideanLin_sum_smul_eigenvectorBasis] at h
  simpa [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [Fintype ι] [DecidableEq ι]
  {X : Ω → EuclideanSpace ℝ ι}

/-- For a random vector `X` with law `N(m, S)` and positive-definite `S`, the quadratic form
`Xᵀ S⁻¹ X` has the noncentral chi-squared law with noncentrality `mᵀ S⁻¹ m`. -/
theorem HasLaw.quadForm_inv_multivariateGaussian {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hX : HasLaw X (multivariateGaussian m S) P) (hS : S.PosDef) :
    HasLaw (fun ω ↦ WithLp.ofLp (X ω) ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp (X ω)))
      (noncentralChiSquaredMeasure (Fintype.card ι)
        (WithLp.ofLp m ⬝ᵥ (S⁻¹ *ᵥ WithLp.ofLp m)).toNNReal) P :=
  (HasLaw.mk (by fun_prop) (map_quadForm_inv_multivariateGaussian m S hS)).fun_comp hX

/-- For a random vector `X` with law `N(0, S)` and positive-semidefinite `S`, the quadratic
form `Xᵀ S⁺ X` in the Moore–Penrose inverse has the chi-squared law with `rank S` degrees of
freedom. -/
theorem HasLaw.quadForm_pseudoInverse_multivariateGaussian {S : Matrix ι ι ℝ}
    (hX : HasLaw X (multivariateGaussian 0 S) P) (hS : S.PosSemidef) :
    HasLaw (fun ω ↦ WithLp.ofLp (X ω) ⬝ᵥ (S.covariancePseudoInverse *ᵥ WithLp.ofLp (X ω)))
      (chiSquaredMeasure S.rank) P :=
  (HasLaw.mk (by fun_prop) (map_quadForm_pseudoInverse_multivariateGaussian S hS)).fun_comp hX

end ProbabilityTheory
