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
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

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

* `TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_multivariateGaussian_iff` — the
  exact
  exponential-integrability domain of a Gaussian quadratic form;
* `TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.Probability.mgf_inner_toEuclideanLin_multivariateGaussian` — its moment-generating
  function on
  that domain, in terms of the sandwich `√S * Θ * √S` and, for positive-semidefinite `S`, of
  `Θ * S`;
* `TauCeti.Probability.cgf_inner_toEuclideanLin_multivariateGaussian_sqrt` and
  `TauCeti.Probability.cgf_inner_toEuclideanLin_multivariateGaussian` — the cumulant-generating
  function,
  `-1 / 2` times the real logarithm of the same determinants;
* `TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff` and
  `TauCeti.Probability.mgf_inner_toEuclideanLin_stdGaussian` — the same results for the standard
  Gaussian,
  in terms of the eigenvalues of the symmetric matrix;
* `Matrix.integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le` — exponential-moment upper bound for
  `∑ i, ((M *ᵥ g) i) ^ 2` under a standard Gaussian product measure.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley (1982), Theorem 1.2.6
  (the multivariate Gaussian) and Theorem 3.2.3 (the Wishart moment-generating function, which
  is the product of these).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti.Probability

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

end TauCeti.Probability

namespace Matrix

/-- Exponential-moment upper bound for `∑ i, ((M *ᵥ g) i) ^ 2` under a standard Gaussian product
measure. -/
theorem integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι κ ℝ) {s : ℝ} (hs_nonneg : 0 ≤ s)
    (hs_bound : 2 * s * ‖M‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun g : κ → ℝ ↦ Real.exp (s * ∑ i, ((M *ᵥ g) i) ^ 2))
        (Measure.pi fun _ : κ ↦ gaussianReal 0 1) ∧
      ∫ g : κ → ℝ, Real.exp (s * ∑ i, ((M *ᵥ g) i) ^ 2)
          ∂(Measure.pi fun _ : κ ↦ gaussianReal 0 1) ≤
        Real.exp (2 * s * ∑ i, ∑ j, M i j ^ 2) := by
  let ν : Measure (κ → ℝ) := Measure.pi fun _ : κ ↦ gaussianReal 0 1
  let Θ : Matrix κ κ ℝ := Mᴴ * M; have hΘ_psd : Θ.PosSemidef := posSemidef_conjTranspose_mul_self M
  have hΘ : Θ.IsHermitian := hΘ_psd.isHermitian
  have hM_conj : Mᴴ = Mᵀ := conjTranspose_eq_transpose_of_trivial M
  have hquad (g : κ → ℝ) :
      ⟪WithLp.toLp 2 g, Θ.toEuclideanLin (WithLp.toLp 2 g)⟫ = ∑ i, ((M *ᵥ g) i) ^ 2 := by
    simp only [Θ, hM_conj, toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    calc ∑ j, ((Mᵀ * M) *ᵥ g) j * g j = g ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ g)) := by
          rw [← mulVec_mulVec, ← dotProduct_comm]; rfl
      _ = ∑ i, ((M *ᵥ g) i) ^ 2 := by
          rw [dotProduct_mulVec, vecMul_transpose]; simp [dotProduct, sq]
  have h2s_eig (j : κ) : 2 * s * hΘ.eigenvalues j ≤ 1 / 2 := by
    let e : EuclideanSpace ℝ κ := hΘ.eigenvectorBasis j
    have heig : hΘ.eigenvalues j ≤ ‖M‖ ^ 2 := by
      calc hΘ.eigenvalues j = ⟪e, (toEuclideanCLM (𝕜 := ℝ) Θ) e⟫ := by
            rw [hΘ.eigenvalues_eq j]
            simp only [e, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
              dotProduct, Pi.star_apply, star_trivial]
            exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
        _ ≤ ‖e‖ * (‖toEuclideanCLM (𝕜 := ℝ) Θ‖ * ‖e‖) :=
            (real_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_left ((toEuclideanCLM (𝕜 := ℝ) Θ).le_opNorm e) (norm_nonneg e))
        _ = ‖M‖ ^ 2 := by
            rw [hΘ.eigenvectorBasis.orthonormal.1 j, l2_opNorm_toEuclideanCLM, sq,
              ← l2_opNorm_conjTranspose_mul_self M]; ring
    exact (mul_le_mul_of_nonneg_left heig (by positivity)).trans hs_bound
  have h2s_lt (j : κ) : 2 * s * hΘ.eigenvalues j < 1 := by linarith [h2s_eig j]
  have htoLp_meas : Measurable (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ) := by fun_prop
  have hint_map : Integrable (fun x : EuclideanSpace ℝ κ ↦ Real.exp (s * ⟪x, Θ.toEuclideanLin x⟫))
      (ν.map (WithLp.toLp 2)) := by
    rw [map_pi_eq_stdGaussian]
    exact (TauCeti.Probability.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff hΘ s).2
      h2s_lt
  have hint_pi : Integrable (fun g : κ → ℝ ↦ Real.exp (s * ∑ i, ((M *ᵥ g) i) ^ 2)) ν :=
    ((integrable_map_measure hint_map.aestronglyMeasurable htoLp_meas.aemeasurable).mp
      hint_map).congr (.of_forall fun g ↦ by dsimp only [Function.comp_def]; rw [hquad g])
  have htrace : ∑ j, hΘ.eigenvalues j = ∑ i, ∑ j, M i j ^ 2 := by
    calc ∑ j, hΘ.eigenvalues j = Θ.trace := by simpa using hΘ.trace_eq_sum_eigenvalues.symm
      _ = ∑ i, ∑ j, M i j ^ 2 := by
          simp only [Θ, hM_conj, trace, diag_apply, sq]; exact Finset.sum_comm
  refine ⟨hint_pi, ?_⟩
  calc ∫ g : κ → ℝ, Real.exp (s * ∑ i, ((M *ᵥ g) i) ^ 2) ∂ν
      = mgf (fun x : EuclideanSpace ℝ κ ↦ ⟪x, Θ.toEuclideanLin x⟫)
          (stdGaussian (EuclideanSpace ℝ κ)) s := by
          rw [← map_pi_eq_stdGaussian, mgf_map htoLp_meas.aemeasurable
            hint_map.aestronglyMeasurable, mgf]
          exact integral_congr_ae
            (.of_forall fun g ↦ by dsimp only [Function.comp_def]; rw [hquad g])
    _ = ∏ j, (1 - 2 * s * hΘ.eigenvalues j) ^ (-1 / 2 : ℝ) :=
          TauCeti.Probability.mgf_inner_toEuclideanLin_stdGaussian hΘ h2s_lt
    _ ≤ ∏ j, Real.exp (2 * s * hΘ.eigenvalues j) :=
          Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (by linarith [h2s_lt j]) _) fun j _ ↦
            Real.one_sub_rpow_neg_half_le_exp
              (mul_nonneg (by positivity) (hΘ_psd.eigenvalues_nonneg j)) (h2s_eig j)
    _ = Real.exp (2 * s * ∑ i, ∑ j, M i j ^ 2) := by rw [← Real.exp_sum, ← Finset.mul_sum, htrace]

end Matrix
