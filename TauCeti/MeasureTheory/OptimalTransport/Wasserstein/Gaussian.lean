/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Brenier
public import TauCeti.Probability.Distributions.Gaussian.PosDefMap

import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Wasserstein distance between Gaussian laws

This file computes the quadratic Wasserstein distance from a finite-dimensional Gaussian law with
positive-definite covariance to one with positive-semidefinite covariance. The optimal map is the
standard positive affine map between the laws, and its squared displacement gives the Bures
covariance term.

## Main results

* `TauCeti.Probability.isKantorovichOptimalTransportMap_affineGeometricMean`: the standard
  positive affine Gaussian map is optimal for the half squared-distance cost.
* `TauCeti.wassersteinEDist_two_multivariateGaussian_rpow_two`: the closed formula for the square
  of the quadratic Wasserstein distance.
* `TauCeti.wassersteinEDist_two_multivariateGaussian`: the corresponding square-root formula.

## References

* C. R. Givens and R. M. Shortt, *A class of Wasserstein metrics for probability distributions*,
  Michigan Math. J. 31 (1984), 231–240.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Ring
open scoped ENNReal MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The closed-form Gaussian (Bures) expression
`‖m₁ - m₂‖² + tr S₁ + tr S₂ - 2 tr (S₁^(1/2) S₂ S₁^(1/2))^(1/2)` in the means and covariances.
For arbitrary matrices it is only an algebraic expression; when `S₁` is positive definite and `S₂`
is positive semidefinite it is the squared quadratic Wasserstein distance between the Gaussian
laws with these parameters (`wassersteinEDist_two_multivariateGaussian_rpow_two`). -/
def gaussianWassersteinSq (m₁ m₂ : EuclideanSpace ℝ ι) (S₁ S₂ : Matrix ι ι ℝ) : ℝ :=
  ‖m₁ - m₂‖ ^ 2 + Matrix.trace S₁ + Matrix.trace S₂ -
    2 * Matrix.trace (CFC.sqrt (CFC.sqrt S₁ * S₂ * CFC.sqrt S₁))

/-- Unfolds `gaussianWassersteinSq` to its defining Bures expression. -/
theorem gaussianWassersteinSq_def (m₁ m₂ : EuclideanSpace ℝ ι) (S₁ S₂ : Matrix ι ι ℝ) :
    gaussianWassersteinSq m₁ m₂ S₁ S₂ =
      ‖m₁ - m₂‖ ^ 2 + Matrix.trace S₁ + Matrix.trace S₂ -
        2 * Matrix.trace (CFC.sqrt (CFC.sqrt S₁ * S₂ * CFC.sqrt S₁)) :=
  (rfl)

/-- The standard positive affine map is optimal for quadratic transport from a nondegenerate
Gaussian law to an arbitrary Gaussian law. -/
theorem Probability.isKantorovichOptimalTransportMap_affineGeometricMean
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef)
    (m₁ m₂ : EuclideanSpace ℝ ι) :
    IsKantorovichOptimalTransportMap
      (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦ ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2))
      (multivariateGaussian m₁ S₁) (multivariateGaussian m₂ S₂)
      (Probability.affineGeometricMean S₁ S₂ m₁ m₂) := by
  let A := geometricMean S₁⁻¹ʳ S₂
  let b := m₂ - A.toEuclideanLin m₁
  let q : EuclideanSpace ℝ ι → ℝ := fun x =>
    ⟪A.toEuclideanLin x, x⟫ / 2 + ⟪b, x⟫
  have hA : A.PosSemidef := by
    exact Matrix.nonneg_iff_posSemidef.mp (geometricMean_nonneg S₁⁻¹ʳ S₂)
  have hlaw : HasLaw (Probability.affineGeometricMean S₁ S₂ m₁ m₂)
      (multivariateGaussian m₂ S₂) (multivariateGaussian m₁ S₁) := {
    aemeasurable :=
      (Probability.measurable_affineGeometricMean S₁ S₂ m₁ m₂).aemeasurable
    map_eq := Probability.map_affineGeometricMean_multivariateGaussian
      m₁ m₂ hS₁ hS₂ }
  refine isKantorovichOptimalTransportMap_of_ae_mem_subdifferential
    IsGaussian.memLp_two_id IsGaussian.memLp_two_id hlaw
      (u := fun x => (q x : EReal)) (.of_forall fun x => ?_)
  have hmap : Probability.affineGeometricMean S₁ S₂ m₁ m₂ x =
      A.toEuclideanLin x + b := by
    rw [Probability.affineGeometricMean_sub]
    dsimp only [A, b]
    rw [map_sub]
    abel
  rw [hmap, mem_subdifferential_coe_iff]
  intro y
  have hpositive : A.toEuclideanLin.IsPositive :=
    Matrix.isPositive_toEuclideanLin_iff.mpr hA
  have hsym : A.toEuclideanLin.IsSymmetric := hpositive.isSymmetric
  have hnonneg : 0 ≤ ⟪A.toEuclideanLin (y - x), y - x⟫ := by
    simpa only [RCLike.re_to_real] using hpositive.re_inner_nonneg_left (y - x)
  dsimp only [q, b]
  simp only [LinearMap.sub_apply, innerₗ_apply_apply, inner_add_right, inner_sub_left,
    inner_sub_right, map_sub] at hnonneg ⊢
  nlinarith [hnonneg, hsym x y, hsym y x, real_inner_comm x (A.toEuclideanLin x),
    real_inner_comm y (A.toEuclideanLin x), real_inner_comm x (A.toEuclideanLin y),
    real_inner_comm m₂ x, real_inner_comm m₂ y,
    real_inner_comm (A.toEuclideanLin m₁) x, real_inner_comm (A.toEuclideanLin m₁) y]

/-- The squared displacement of the standard Gaussian transport map is the Bures formula. -/
theorem Probability.integral_norm_sub_affineGeometricMean_sq
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef)
    (m₁ m₂ : EuclideanSpace ℝ ι) :
    ∫ x, ‖x - Probability.affineGeometricMean S₁ S₂ m₁ m₂ x‖ ^ 2
      ∂(multivariateGaussian m₁ S₁) = gaussianWassersteinSq m₁ m₂ S₁ S₂ := by
  let A := geometricMean S₁⁻¹ʳ S₂
  let B : Matrix ι ι ℝ := 1 - A
  let c : EuclideanSpace ℝ ι := A.toEuclideanLin m₁ - m₂
  let C : Matrix ι ι ℝ := B * S₁ * B.transpose
  have hB (x : EuclideanSpace ℝ ι) : B.toEuclideanLin x = x - A.toEuclideanLin x := by
    rw [map_sub, LinearMap.sub_apply, Matrix.toLpLin_one, LinearMap.id_apply]
  have hfun : (fun x => x - Probability.affineGeometricMean S₁ S₂ m₁ m₂ x) =
      fun x => B.toEuclideanLin x + c := by
    funext x
    rw [Probability.affineGeometricMean_sub, hB]
    dsimp only [A, c]
    rw [map_sub]
    module
  have hC : C.PosSemidef := by
    dsimp only [C]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      hS₁.posSemidef.mul_mul_conjTranspose_same B
  have hmap : (multivariateGaussian m₁ S₁).map
      (fun x => x - Probability.affineGeometricMean S₁ S₂ m₁ m₂ x) =
      multivariateGaussian (m₁ - m₂) C := by
    rw [hfun, Probability.map_affine_multivariateGaussian m₁ hS₁.posSemidef B c]
    congr 1
    rw [hB]
    dsimp only [c]
    module
  have hmeas : AEMeasurable
      (fun x => x - Probability.affineGeometricMean S₁ S₂ m₁ m₂ x)
      (multivariateGaussian m₁ S₁) := by fun_prop
  have hint : Integrable (fun x : EuclideanSpace ℝ ι => ‖x‖ ^ 2)
      ((multivariateGaussian m₁ S₁).map
        fun x => x - Probability.affineGeometricMean S₁ S₂ m₁ m₂ x) := by
    rw [hmap]
    exact (memLp_two_iff_integrable_sq_norm IsGaussian.memLp_two_id.aestronglyMeasurable).mp
      IsGaussian.memLp_two_id
  rw [← integral_map hmeas hint.aestronglyMeasurable, hmap,
    integral_norm_sq_eq_norm_integral_sq_add_trace_covMatrix _ IsGaussian.memLp_two_id,
    integral_id_multivariateGaussian, Probability.covMatrix_multivariateGaussian _ hC]
  dsimp only [C, B, A]
  rw [gaussianWassersteinSq_def, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    hS₁.trace_one_sub_geometricMean_ringInverse_mul_mul_conjTranspose hS₂]
  ring

/-- The Gaussian Wasserstein square is nonnegative when the source covariance is positive
definite and the target covariance is positive semidefinite. -/
theorem gaussianWassersteinSq_nonneg {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef)
    (hS₂ : S₂.PosSemidef) (m₁ m₂ : EuclideanSpace ℝ ι) :
    0 ≤ gaussianWassersteinSq m₁ m₂ S₁ S₂ := by
  rw [← Probability.integral_norm_sub_affineGeometricMean_sq hS₁ hS₂]
  exact integral_nonneg fun x ↦ sq_nonneg ‖x - Probability.affineGeometricMean S₁ S₂ m₁ m₂ x‖

/-- The square of the quadratic Wasserstein distance from a nondegenerate multivariate Gaussian
law to an arbitrary Gaussian law is the sum of the squared distance of their means and the Bures
covariance term. -/
theorem wassersteinEDist_two_multivariateGaussian_rpow_two
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef)
    (m₁ m₂ : EuclideanSpace ℝ ι) :
    wassersteinEDist 2 (multivariateGaussian m₁ S₁) (multivariateGaussian m₂ S₂) ^ (2 : ℝ) =
      ENNReal.ofReal (gaussianWassersteinSq m₁ m₂ S₁ S₂) := by
  let cHalf := fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
    ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)
  let T := Probability.affineGeometricMean S₁ S₂ m₁ m₂
  have hopt := Probability.isKantorovichOptimalTransportMap_affineGeometricMean hS₁ hS₂ m₁ m₂
  have hcost : (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      edist z.1 z.2 ^ (2 : ℝ≥0∞).toReal) = fun z ↦ (2 : ℝ≥0∞) * cHalf z := by
    funext z
    dsimp only [cHalf]
    rw [ENNReal.toReal_ofNat, edist_dist, dist_eq_norm, ENNReal.rpow_two,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
    calc
      ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) =
          ENNReal.ofReal (2 * (‖z.1 - z.2‖ ^ 2 / 2)) := by congr 1; ring
      _ = ENNReal.ofReal 2 * ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) :=
        ENNReal.ofReal_mul (by norm_num)
      _ = (2 : ℝ≥0∞) * ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2) := by norm_num
  have hmem : MemLp (fun x ↦ x - T x) 2 (multivariateGaussian m₁ S₁) :=
    IsGaussian.memLp_two_id.sub (hopt.toHasLaw.memLp IsGaussian.memLp_two_id)
  have hint : Integrable (fun x ↦ ‖x - T x‖ ^ 2) (multivariateGaussian m₁ S₁) :=
    (memLp_two_iff_integrable_sq_norm hmem.aestronglyMeasurable).mp hmem
  rw [← ENNReal.toReal_ofNat 2, wassersteinEDist_rpow_eq_transportCost measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top, hcost, transportCost_const_mul (by norm_num) ENNReal.ofNat_ne_top,
    ← hopt.transportMapCost_eq, transportMapCost_def,
    ← lintegral_const_mul' 2 (fun x ↦ cHalf (x, T x)) ENNReal.ofNat_ne_top]
  calc
    ∫⁻ x, (2 : ℝ≥0∞) * cHalf (x, T x) ∂(multivariateGaussian m₁ S₁) =
        ∫⁻ x, ENNReal.ofReal (‖x - T x‖ ^ 2) ∂(multivariateGaussian m₁ S₁) := by
      apply lintegral_congr
      intro x
      simpa only [ENNReal.toReal_ofNat, edist_dist, dist_eq_norm, ENNReal.rpow_two,
        ← ENNReal.ofReal_pow (norm_nonneg _)] using (congrFun hcost (x, T x)).symm
    _ = ENNReal.ofReal (∫ x, ‖x - T x‖ ^ 2 ∂(multivariateGaussian m₁ S₁)) :=
      (ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun x ↦ sq_nonneg _)).symm
    _ = ENNReal.ofReal (gaussianWassersteinSq m₁ m₂ S₁ S₂) := by
      rw [Probability.integral_norm_sub_affineGeometricMean_sq hS₁ hS₂]

/-- The quadratic Wasserstein distance from a nondegenerate multivariate Gaussian law to an
arbitrary Gaussian law is the square root of the Bures formula. -/
theorem wassersteinEDist_two_multivariateGaussian
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef)
    (m₁ m₂ : EuclideanSpace ℝ ι) :
    wassersteinEDist 2 (multivariateGaussian m₁ S₁) (multivariateGaussian m₂ S₂) =
      ENNReal.ofReal (Real.sqrt (gaussianWassersteinSq m₁ m₂ S₁ S₂)) := by
  have hnonneg := gaussianWassersteinSq_nonneg hS₁ hS₂ m₁ m₂
  calc
    wassersteinEDist 2 (multivariateGaussian m₁ S₁) (multivariateGaussian m₂ S₂) =
        (wassersteinEDist 2 (multivariateGaussian m₁ S₁) (multivariateGaussian m₂ S₂) ^
          (2 : ℝ)) ^ (1 / 2 : ℝ) := by
      rw [← ENNReal.rpow_mul]
      norm_num
    _ = ENNReal.ofReal (gaussianWassersteinSq m₁ m₂ S₁ S₂) ^ (1 / 2 : ℝ) := by
      rw [wassersteinEDist_two_multivariateGaussian_rpow_two hS₁ hS₂]
    _ = ENNReal.ofReal ((gaussianWassersteinSq m₁ m₂ S₁ S₂) ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg hnonneg (by norm_num)
    _ = ENNReal.ofReal (Real.sqrt (gaussianWassersteinSq m₁ m₂ S₁ S₂)) := by
      rw [Real.sqrt_eq_rpow]

end TauCeti

end

end
