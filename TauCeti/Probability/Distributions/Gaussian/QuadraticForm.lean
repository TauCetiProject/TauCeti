/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Spectrum
public import TauCeti.Analysis.Matrix.Sqrt
public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.Multivariate

/-!
# Moment-generating functions of Gaussian quadratic forms

Let `S` be the matrix parameter of a centred multivariate Gaussian and `Θ` a real symmetric
matrix. This file determines exactly when the quadratic statistic `x ↦ ⟪x, Θ x⟫` of that Gaussian
vector has finite exponential moments of order `t`, and computes its moment-generating function
there:

* the integrand is integrable exactly when the pencil `1 - (2 * t) • (√S * Θ * √S)` is positive
  definite, where `√S = CFC.sqrt S`, with no hypothesis on `S`; and
* on that domain the moment-generating function is
  `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-1 / 2)`, which for positive-semidefinite `S` is
  `det (1 - (2 * t) • (Θ * S)) ^ (-1 / 2)`.

The same results are stated for the standard Gaussian vector, in terms of the eigenvalues of the
symmetric matrix. The one-dimensional building blocks, the exponential moments of a weighted sum
of squares of independent standard Gaussian coordinates, live in
`TauCeti.Probability.Distributions.Gaussian.ChiSquared`.

## Main results

* `TauCeti.mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff` — the exact
  exponential-integrability domain of a Gaussian quadratic form;
* `TauCeti.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.mgf_inner_toEuclideanLin_multivariateGaussian` — its moment-generating function on
  that domain, in terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of
  `Θ * S`;
* `TauCeti.cgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.cgf_inner_toEuclideanLin_multivariateGaussian` — the cumulant-generating function,
  `-1 / 2` times the real logarithm of the same determinants;
* `TauCeti.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff` and
  `TauCeti.mgf_inner_toEuclideanLin_stdGaussian` — the same results for the standard Gaussian,
  in terms of the eigenvalues of the symmetric matrix.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 1.2.6
  (the multivariate Gaussian) and Theorem 3.2.3 (the Wishart moment-generating function, which
  is the product of these).
* Roadmap: `TauCetiRoadmap/StandardDistributions/README.md`, Layer 5, item 3,
  **Gaussian quadratic forms**.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

/-! ### The standard Gaussian vector -/

section stdGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {B : Matrix ι ι ℝ} (hB : B.IsHermitian)
  {t : ℝ}
include hB

/-- The exponential moment of order `t` of the quadratic form of a real symmetric matrix `B`
under the standard Gaussian vector is finite exactly when `2 * t * λ < 1` for every eigenvalue
`λ` of `B`. -/
theorem mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff (t : ℝ) :
    t ∈ integrableExpSet (fun x ↦ ⟪x, B.toEuclideanLin x⟫)
        (stdGaussian (EuclideanSpace ℝ ι)) ↔
      ∀ j, 2 * t * hB.eigenvalues j < 1 := by
  rw [← Probability.mem_integrableExpSet_sum_mul_sq_pi_gaussianReal_iff hB.eigenvalues t]
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hB.eigenvectorBasis,
    integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop)),
    Function.comp_def]
  simp only [hB.inner_toEuclideanLin_sum_smul_eigenvectorBasis, RCLike.ofReal_real_eq_id, id_eq,
    Real.norm_eq_abs, sq_abs]

/-- The moment-generating function of the quadratic form of a real symmetric matrix `B` under
the standard Gaussian vector is `∏ j, (1 - 2 * t * λ j) ^ (-1 / 2)` over the eigenvalues `λ j`
of `B`, on its domain. -/
theorem mgf_inner_toEuclideanLin_stdGaussian (ht : ∀ j, 2 * t * hB.eigenvalues j < 1) :
    mgf (fun x ↦ ⟪x, B.toEuclideanLin x⟫) (stdGaussian (EuclideanSpace ℝ ι)) t =
      ∏ j, (1 - 2 * t * hB.eigenvalues j) ^ (-1 / 2 : ℝ) := by
  rw [← Probability.mgf_sum_mul_sq_pi_gaussianReal ht,
    stdGaussian_eq_map_pi_orthonormalBasis hB.eigenvectorBasis,
    mgf_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop), Function.comp_def]
  simp only [hB.inner_toEuclideanLin_sum_smul_eigenvectorBasis, RCLike.ofReal_real_eq_id, id_eq,
    Real.norm_eq_abs, sq_abs]

end stdGaussian

/-! ### The centred multivariate Gaussian vector -/

section multivariateGaussian

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S Θ : Matrix ι ι ℝ} {t : ℝ}

/-- The exponential moment of order `t` of the quadratic form `x ↦ ⟪x, Θ x⟫` of a real
symmetric matrix `Θ` under the centred multivariate Gaussian with matrix parameter `S` is finite
exactly when the pencil `1 - (2 * t) • (√S * Θ * √S)` is positive definite.

No hypothesis on `S` is needed. For a parameter that is not positive semidefinite it is not the
law's covariance: Mathlib's `CFC.sqrt S` is then zero, the pencil is the identity, and the law is
the Dirac measure at the origin. -/
theorem mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff (S : Matrix ι ι ℝ)
    (hΘ : Θ.IsHermitian) (t : ℝ) :
    t ∈ integrableExpSet (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫)
        (multivariateGaussian 0 S) ↔
      (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S hΘ
  rw [hB.posDef_one_sub_smul_iff,
    ← mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff hB t,
    multivariateGaussian_zero_eq_map_stdGaussian_sqrt]
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  rw [integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop)),
    Function.comp_def]
  simp only [Matrix.inner_toEuclideanCLM_sqrt_toEuclideanLin]

/-- On its exponential-integrability domain, the moment-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with matrix parameter `S` is `det (1 - (2 * t) • (√S * Θ * √S)) ^ (-1 / 2)`, for every `S`. -/
theorem mgf_inner_toEuclideanLin_multivariateGaussian_sqrt (S : Matrix ι ι ℝ)
    (hΘ : Θ.IsHermitian) (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    mgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).det ^ (-1 / 2 : ℝ) := by
  have hB := Matrix.isHermitian_sqrt_mul_mul_sqrt S hΘ
  have ht' : ∀ j, 2 * t * hB.eigenvalues j < 1 := (hB.posDef_one_sub_smul_iff (2 * t)).1 ht
  rw [multivariateGaussian_zero_eq_map_stdGaussian_sqrt,
    mgf_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop), Function.comp_def]
  simp only [Matrix.inner_toEuclideanCLM_sqrt_toEuclideanLin]
  have hdet := hB.det_one_sub_smul (2 * t)
  simp only [RCLike.ofReal_real_eq_id, id_eq] at hdet
  rw [mgf_inner_toEuclideanLin_stdGaussian hB ht',
    Real.finsetProd_rpow _ _ (fun j _ ↦ by linarith [ht' j]) _, ← hdet]

/-- On its exponential-integrability domain, the cumulant-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with matrix parameter `S` is `-1 / 2 * log (det (1 - (2 * t) • (√S * Θ * √S)))`, for every `S`. -/
theorem cgf_inner_toEuclideanLin_multivariateGaussian_sqrt (S : Matrix ι ι ℝ)
    (hΘ : Θ.IsHermitian) (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    cgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      -1 / 2 * Real.log (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).det := by
  rw [cgf, mgf_inner_toEuclideanLin_multivariateGaussian_sqrt S hΘ ht, Real.log_rpow ht.det_pos]

/-- On its exponential-integrability domain, the moment-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with positive-semidefinite covariance `S` is `det (1 - (2 * t) • (Θ * S)) ^ (-1 / 2)`. -/
theorem mgf_inner_toEuclideanLin_multivariateGaussian (hS : S.PosSemidef) (hΘ : Θ.IsHermitian)
    (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    mgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      (1 - (2 * t) • (Θ * S)).det ^ (-1 / 2 : ℝ) := by
  rw [mgf_inner_toEuclideanLin_multivariateGaussian_sqrt S hΘ ht,
    hS.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul Θ (2 * t)]

/-- On its exponential-integrability domain, the cumulant-generating function of the quadratic
form `x ↦ ⟪x, Θ x⟫` of a real symmetric matrix `Θ` under the centred multivariate Gaussian
with positive-semidefinite covariance `S` is `-1 / 2 * log (det (1 - (2 * t) • (Θ * S)))`. -/
theorem cgf_inner_toEuclideanLin_multivariateGaussian (hS : S.PosSemidef)
    (hΘ : Θ.IsHermitian) (ht : (1 - (2 * t) • (CFC.sqrt S * Θ * CFC.sqrt S)).PosDef) :
    cgf (fun x ↦ ⟪x, Θ.toEuclideanLin x⟫) (multivariateGaussian 0 S) t =
      -1 / 2 * Real.log (1 - (2 * t) • (Θ * S)).det := by
  rw [cgf_inner_toEuclideanLin_multivariateGaussian_sqrt S hΘ ht,
    hS.det_one_sub_smul_sqrt_mul_mul_sqrt_eq_det_one_sub_smul_mul Θ (2 * t)]

end multivariateGaussian

end TauCeti
