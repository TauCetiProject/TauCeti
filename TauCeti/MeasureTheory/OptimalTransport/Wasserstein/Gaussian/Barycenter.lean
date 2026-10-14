/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Gaussian.Basic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Geodesic
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Borel
public import TauCeti.MeasureTheory.OptimalTransport.Cost.Quadratic
public import TauCeti.MeasureTheory.Measure.FrechetMean.TwoPoint
public import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Interpolation and barycenters of two Gaussian laws

The optimal affine map between a nondegenerate Gaussian law and a Gaussian law transports along
straight lines. At time `t`, the resulting law is Gaussian with interpolated mean and covariance
`B S₁ Bᵀ`, where `B = (1-t)I + t A` and `A` is the positive transport matrix. For `t ∈ [0,1]`,
these laws form a quadratic Wasserstein geodesic, so the law at time `t` is a Fréchet barycenter
of the two input laws with weights `1-t` and `t`.

The source covariance is assumed positive definite; the target covariance may be singular.

## References

* M. Agueh and G. Carlier, *Barycenters in the Wasserstein space*, SIAM J. Math. Anal. 43
  (2011), 904–924, for displacement interpolation and Gaussian barycenters.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Ring
open scoped ENNReal MatrixOrder RealInnerProductSpace

namespace TauCeti

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Gaussian law regarded as an element of the quadratic Wasserstein space. Every Gaussian
law has finite second moment, including laws with singular covariance. -/
def Probability.gaussianWassersteinLaw (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    WassersteinSpace 2 (EuclideanSpace ℝ ι) :=
  WassersteinSpace.mk ⟨multivariateGaussian m S, by infer_instance⟩
    (hasFiniteMoment_def.2 ⟨0, by simpa [edist_eq_enorm_sub] using
      (ProbabilityTheory.IsGaussian.memLp_two_id (μ := multivariateGaussian m S)).enorm⟩)

@[simp]
theorem Probability.gaussianWassersteinLaw_coe (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    ((Probability.gaussianWassersteinLaw m S).toProbabilityMeasure : Measure _) =
      multivariateGaussian m S := by
  unfold Probability.gaussianWassersteinLaw
  exact congrArg (fun Q : ProbabilityMeasure (EuclideanSpace ℝ ι) ↦ Q.toMeasure)
    (WassersteinSpace.coe_mk _ _)

/-- The linear part of displacement interpolation between two Gaussian covariances. -/
def gaussianInterpolationMatrix (S₁ S₂ : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  (1 - t) • 1 + t • geometricMean S₁⁻¹ʳ S₂

/-- The interpolation matrix is the affine combination of the identity and transport matrix. -/
theorem gaussianInterpolationMatrix_def (S₁ S₂ : Matrix ι ι ℝ) (t : ℝ) :
    gaussianInterpolationMatrix S₁ S₂ t = (1 - t) • 1 + t • geometricMean S₁⁻¹ʳ S₂ := (rfl)

/-- The covariance of the Gaussian displacement interpolant. -/
def gaussianInterpolationCovariance (S₁ S₂ : Matrix ι ι ℝ) (t : ℝ) : Matrix ι ι ℝ :=
  gaussianInterpolationMatrix S₁ S₂ t * S₁ * (gaussianInterpolationMatrix S₁ S₂ t).transpose

/-- The interpolated covariance is the congruence by the interpolation matrix. -/
theorem gaussianInterpolationCovariance_def (S₁ S₂ : Matrix ι ι ℝ) (t : ℝ) :
    gaussianInterpolationCovariance S₁ S₂ t =
      gaussianInterpolationMatrix S₁ S₂ t * S₁ *
        (gaussianInterpolationMatrix S₁ S₂ t).transpose := (rfl)

/-- At the source endpoint, the interpolation matrix is the identity. -/
@[simp]
theorem gaussianInterpolationMatrix_zero (S₁ S₂ : Matrix ι ι ℝ) :
    gaussianInterpolationMatrix S₁ S₂ 0 = 1 := by
  simp [gaussianInterpolationMatrix]

/-- At the target endpoint, the interpolation matrix is the positive transport matrix. -/
@[simp]
theorem gaussianInterpolationMatrix_one (S₁ S₂ : Matrix ι ι ℝ) :
    gaussianInterpolationMatrix S₁ S₂ 1 = geometricMean S₁⁻¹ʳ S₂ := by
  simp [gaussianInterpolationMatrix]

/-- The source covariance is recovered at time zero. -/
@[simp]
theorem gaussianInterpolationCovariance_zero (S₁ S₂ : Matrix ι ι ℝ) :
    gaussianInterpolationCovariance S₁ S₂ 0 = S₁ := by
  simp [gaussianInterpolationCovariance]

/-- The target covariance is recovered at time one, including a singular target. -/
@[simp]
theorem gaussianInterpolationCovariance_one {S₁ S₂ : Matrix ι ι ℝ}
    (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef) :
    gaussianInterpolationCovariance S₁ S₂ 1 = S₂ := by
  simpa only [gaussianInterpolationCovariance, gaussianInterpolationMatrix_one,
    Matrix.conjTranspose_eq_transpose_of_trivial] using
    hS₁.mul_mul_conjTranspose_geometricMean hS₂

/-- The interpolating matrix acts as the affine combination of the identity and the transport
matrix. -/
theorem toEuclideanLin_gaussianInterpolationMatrix_apply (S₁ S₂ : Matrix ι ι ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ ι) :
    (gaussianInterpolationMatrix S₁ S₂ t).toEuclideanLin x =
      (1 - t) • x + t • (geometricMean S₁⁻¹ʳ S₂).toEuclideanLin x := by
  simp [gaussianInterpolationMatrix, map_add, map_smul]

/-- Affine interpolation from a Gaussian with positive-semidefinite covariance remains Gaussian.
Its mean is linearly interpolated, and its covariance is the congruence by the interpolating
matrix. The formula holds for every real `t`, including extrapolation beyond the endpoints. -/
theorem Probability.map_interpolation_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosSemidef) (t : ℝ) :
    (multivariateGaussian m₁ S₁).map
        (fun x ↦ (1 - t) • x + t • affineGeometricMean S₁ S₂ m₁ m₂ x) =
      multivariateGaussian ((1 - t) • m₁ + t • m₂)
        (gaussianInterpolationCovariance S₁ S₂ t) := by
  let A := geometricMean S₁⁻¹ʳ S₂
  let B := gaussianInterpolationMatrix S₁ S₂ t
  let c := t • (m₂ - A.toEuclideanLin m₁)
  have hfun : (fun x ↦ (1 - t) • x + t • affineGeometricMean S₁ S₂ m₁ m₂ x) =
      fun x ↦ B.toEuclideanLin x + c := by
    funext x
    rw [Probability.affineGeometricMean_sub]
    simp only [smul_add, map_sub, smul_sub]
    rw [toEuclideanLin_gaussianInterpolationMatrix_apply]
    dsimp only [A, B, c]
    simp only [sub_eq_add_neg, smul_neg, smul_add]
    abel
  rw [hfun, map_affine_multivariateGaussian m₁ hS₁ B c]
  congr 1
  · rw [toEuclideanLin_gaussianInterpolationMatrix_apply]
    dsimp only [A, B, c]
    simp only [smul_sub]
    abel

/-- **The Gaussian displacement geodesic.** If the first covariance is positive definite and
the second is positive semidefinite, interpolation along the optimal affine map gives a
quadratic Wasserstein geodesic. Its time-`t` law has the displayed Gaussian mean and covariance.
The second covariance may be singular. -/
theorem Probability.exists_isGeodesicSegment_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef) :
    ∃ γ : ℝ → WassersteinSpace 2 (EuclideanSpace ℝ ι),
      IsGeodesicSegment γ (gaussianWassersteinLaw m₁ S₁)
        (gaussianWassersteinLaw m₂ S₂) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        γ t = gaussianWassersteinLaw ((1 - t) • m₁ + t • m₂)
          (gaussianInterpolationCovariance S₁ S₂ t) := by
  let T := affineGeometricMean S₁ S₂ m₁ m₂
  let π := graphPlan T (multivariateGaussian m₁ S₁)
  have hopt := isKantorovichOptimalTransportMap_affineGeometricMean hS₁ hS₂ m₁ m₂
  have hπhalf : IsOptimalCoupling
      (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
        ENNReal.ofReal (‖z.1 - z.2‖ ^ 2 / 2)) π
      (multivariateGaussian m₁ S₁) (multivariateGaussian m₂ S₂) := by
    exact (isKantorovichOptimalTransportMap_iff_isOptimalCoupling_graphPlan hopt.toHasLaw
      (by fun_prop)).1 hopt
  have hπopt := (isOptimalCoupling_edist_rpow_iff measurable_edist two_ne_zero
    ENNReal.ofNat_ne_top).1 (isOptimalCoupling_edist_rpow_two_of_norm_sub_sq_div_two hπhalf)
  have hπcoupling : IsCoupling π
      ((gaussianWassersteinLaw m₁ S₁).toProbabilityMeasure :
        Measure (EuclideanSpace ℝ ι))
      ((gaussianWassersteinLaw m₂ S₂).toProbabilityMeasure :
        Measure (EuclideanSpace ℝ ι)) := by
    simpa only [gaussianWassersteinLaw_coe] using hπopt.1
  have hπvalue : eLpNorm (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι ↦
      edist z.1 z.2) 2 π =
      wassersteinEDist 2
        ((gaussianWassersteinLaw m₁ S₁).toProbabilityMeasure :
          Measure (EuclideanSpace ℝ ι))
        ((gaussianWassersteinLaw m₂ S₂).toProbabilityMeasure :
          Measure (EuclideanSpace ℝ ι)) := by
    simpa only [gaussianWassersteinLaw_coe] using hπopt.2
  obtain ⟨γ, hγ, hγlaw⟩ :=
    WassersteinSpace.exists_isGeodesicSegment_map_smul_add_smul hπcoupling hπvalue
  refine ⟨γ, hγ, fun t ht ↦ ?_⟩
  apply WassersteinSpace.ext
  apply ProbabilityMeasure.toMeasure_injective
  rw [gaussianWassersteinLaw_coe, hγlaw t ht]
  dsimp only [π]
  rw [graphPlan_def, Measure.map_map]
  · exact map_interpolation_multivariateGaussian m₁ m₂ hS₁.posSemidef t
  · fun_prop
  · exact measurable_id.prodMk (measurable_affineGeometricMean S₁ S₂ m₁ m₂)

/-- **The barycenter of two Gaussian laws.** At quadratic weights `1-t,t`, the Gaussian
displacement interpolant is a finite Fréchet barycenter in `P₂`. Its covariance is the
congruence of the source covariance by `(1-t)I+tA`; the target covariance can be singular. -/
theorem Probability.isFrechetBarycenter_two_multivariateGaussian (m₁ m₂ : EuclideanSpace ℝ ι)
    {S₁ S₂ : Matrix ι ι ℝ} (hS₁ : S₁.PosDef) (hS₂ : S₂.PosSemidef)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    IsFrechetBarycenter 2
      (ENNReal.ofReal (1 - t) • Measure.dirac (gaussianWassersteinLaw m₁ S₁) +
        ENNReal.ofReal t • Measure.dirac (gaussianWassersteinLaw m₂ S₂))
      (gaussianWassersteinLaw ((1 - t) • m₁ + t • m₂)
        (gaussianInterpolationCovariance S₁ S₂ t)) := by
  have := WassersteinSpace.borelSpace (X := EuclideanSpace ℝ ι) (p := 2)
    ENNReal.ofNat_ne_top
  obtain ⟨γ, hγ, hγlaw⟩ := exists_isGeodesicSegment_multivariateGaussian m₁ m₂ hS₁ hS₂
  rw [← hγlaw t ht]
  exact hγ.isFrechetBarycenter_two ht

end TauCeti

end
