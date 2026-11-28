/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Modulus

import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.PrekopaLeindler
import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Product
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Small-ball bounds for proper complex Gaussians

Projecting a proper complex Gaussian with identity covariance onto a complex subspace
gives a Gaussian with identity covariance in an orthonormal basis of that subspace.
Anderson's inequality bounds its shifted small-ball probability by the centered one,
whose squared radius has a gamma distribution in positive dimension.

## References

* T. W. Anderson, *The integral of a symmetric unimodal function over a symmetric convex set
  and some probability inequalities*, Proc. Amer. Math. Soc. 6 (1955), 170–176.
-/

public section

noncomputable section

open Matrix MeasureTheory Metric Module ProbabilityTheory Set WithLp
open scoped ComplexOrder InnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Translating an identity-covariance proper complex Gaussian does not increase the mass
of a Euclidean ball centered at the origin. -/
theorem measureReal_norm_toLp_le_properComplexGaussianMeasure [DecidableEq ι]
    (a : ι → ℂ) (t : ℝ) :
    (properComplexGaussianMeasure a 1).real {x | ‖(toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ t} ≤
      (properComplexGaussianMeasure 0 1).real {x | ‖(toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ t} := by
  have hnorm (x : ι → ℂ) :
      ‖complexToRealEuclidean ι x‖ = ‖(toLp 2 x : EuclideanSpace ℂ ι)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    calc
      _ = inner ℝ (complexToRealEuclidean ι x) (complexToRealEuclidean ι x) :=
        (real_inner_self_eq_norm_sq _).symm
      _ = (inner ℂ (toLp 2 x : EuclideanSpace ℂ ι) (toLp 2 x)).re := by
        rw [inner_complexToRealEuclidean, EuclideanSpace.inner_eq_star_dotProduct]
        simp [dotProduct_comm]
      _ = _ := by
        rw [inner_self_eq_norm_sq_to_K]
        norm_cast
  let e := complexToRealEuclidean ι
  let C : Set (EuclideanSpace ℝ (ι ⊕ ι)) := closedBall 0 t
  have he : e.symm ⁻¹' {x | ‖(toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ t} = C := by
    ext x
    simp [C, ← hnorm, e]
  have h := multivariateGaussian_preimage_add_le (complexGaussianRealCovariance (1 : Matrix ι ι ℂ))
    (C := C) measurableSet_closedBall (convex_closedBall _ _) (by simp [C]) (e a)
  have hball : MeasurableSet {x : ι → ℂ | ‖(toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [properComplexGaussianMeasure_def, properComplexGaussianMeasure_def,
    map_measureReal_apply (by fun_prop) hball, map_measureReal_apply (by fun_prop) hball,
    he, map_zero]
  have hshift := map_add_smul_multivariateGaussian (0 : EuclideanSpace ℝ (ι ⊕ ι))
    ((posSemidef_complexGaussianRealCovariance_iff (1 : Matrix ι ι ℂ)).mpr
      Matrix.PosSemidef.one) (e a) 1
  simp only [one_smul, smul_zero, add_zero, one_pow] at hshift
  rw [← hshift, map_measureReal_apply (by fun_prop) measurableSet_closedBall]
  exact ENNReal.toReal_mono (measure_ne_top _ _) h

private theorem measureReal_norm_toLp_le_pi_properComplexGaussianScalar
    (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (Measure.pi fun _ : ι ↦ properComplexGaussianScalar).real
      {x | ‖(toLp 2 x : EuclideanSpace ℂ ι)‖ ≤ t} ≤
      Real.exp (s * t ^ 2) / (1 + s) ^ Fintype.card ι := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simpa using (measureReal_le_one.trans (Real.one_le_exp (by positivity)) :
      (Measure.pi fun _ : ι ↦ properComplexGaussianScalar).real _ ≤ _)
  have hγ : 0 < (Fintype.card ι : ℝ) := by positivity
  let := isProbabilityMeasure_gammaMeasure hγ one_pos
  have hint := integrable_exp_mul_id_gammaMeasure hγ one_pos (t := -s) (by linarith)
  have h := measure_le_le_exp_mul_mgf (X := id) (t ^ 2) (neg_nonpos.mpr hs) hint
  rw [mgf_id_gammaMeasure hγ one_pos (by linarith), div_one, sub_neg_eq_add,
    Real.rpow_neg (by positivity), Real.rpow_natCast, neg_neg, ← div_eq_mul_inv] at h
  let f (x : ι → ℂ) := ∑ i, ‖x i‖ ^ 2
  refine (measureReal_mono (s₂ := f ⁻¹' Iic (t ^ 2)) ?_).trans ?_
  · intro x hx
    simpa only [mem_preimage, mem_Iic, EuclideanSpace.norm_sq_eq] using
      pow_le_pow_left₀ (norm_nonneg _) hx 2
  · rw [← map_measureReal_apply (f := fun x : ι → ℂ ↦ ∑ i, ‖x i‖ ^ 2)
      (by fun_prop) (s := Iic (t ^ 2)) measurableSet_Iic,
      map_sum_norm_sq_pi_properComplexGaussianScalar]
    exact h

/-- For independent standard proper complex Gaussian coordinates, the probability that a
deterministic translate is within distance `t` of a fixed complex subspace has the gamma
Chernoff bound, with shape given by the complex codimension. -/
theorem measureReal_infDist_toLp_add_le_pi_properComplexGaussianScalar
    (U : Submodule ℂ (EuclideanSpace ℂ ι)) (a : ι → ℂ) (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    (Measure.pi fun _ : ι ↦ properComplexGaussianScalar).real
        {x | infDist (toLp 2 (a + x)) (U : Set (EuclideanSpace ℂ ι)) ≤ t} ≤
      Real.exp (s * t ^ 2) / (1 + s) ^ finrank ℂ Uᗮ := by
  classical
  let d := finrank ℂ Uᗮ
  let b : OrthonormalBasis (Fin d) ℂ Uᗮ := stdOrthonormalBasis ℂ Uᗮ
  let v (j : Fin d) : EuclideanSpace ℂ ι := b j
  let L : Matrix (Fin d) ι ℂ := (Matrix.of fun i j ↦ v j i)ᴴ
  have hv : Orthonormal ℂ v := (Uᗮ.subtypeₗᵢ.orthonormal_comp_iff).mpr b.orthonormal
  have hL : L * Lᴴ = 1 := by
    rw [← Matrix.gram_eq_one_iff_orthonormal.mpr hv,
      Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun ι ℂ)]
    simp [L]
  have hproj (x : ι → ℂ) :
      ‖(toLp 2 (L *ᵥ x) : EuclideanSpace ℂ (Fin d))‖ =
        infDist (toLp 2 x) (U : Set (EuclideanSpace ℂ ι)) := by
    have heq : toLp 2 (L *ᵥ x) = b.repr (Uᗮ.orthogonalProjectionOnto (toLp 2 x)) := by
      ext j
      rw [b.repr_apply_apply,
        Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
      simp [L, mulVec, dotProduct, EuclideanSpace.inner_eq_star_dotProduct, v, mul_comm]
    rw [heq, LinearIsometryEquiv.norm_map]
    rw [← Submodule.norm_coe, Submodule.coe_orthogonalProjectionOnto_apply,
      Uᗮ.norm_starProjection_eq_infDist, Submodule.orthogonal_orthogonal]
  let f (x : ι → ℂ) := L *ᵥ (x + a)
  have hf : Measurable f := by
    unfold f
    fun_prop
  have hmap : (Measure.pi fun _ : ι ↦ properComplexGaussianScalar).map f =
      properComplexGaussianMeasure (L *ᵥ a) 1 := by
    rw [← properComplexGaussianMeasure_zero_one_eq_pi]
    simpa [f, Matrix.mulVec_add, hL] using
      map_affine_properComplexGaussianMeasure (0 : ι → ℂ) Matrix.PosSemidef.one L (L *ᵥ a)
  have hpre : f ⁻¹' {y | ‖(toLp 2 y : EuclideanSpace ℂ (Fin d))‖ ≤ t} =
      {x | infDist (toLp 2 (a + x)) (U : Set (EuclideanSpace ℂ ι)) ≤ t} := by
    ext x
    simp [f, hproj, add_comm]
  rw [← hpre, ← map_measureReal_apply hf (measurableSet_le (by fun_prop) measurable_const), hmap]
  exact (measureReal_norm_toLp_le_properComplexGaussianMeasure (L *ᵥ a) t).trans
    (by simpa only [properComplexGaussianMeasure_zero_one_eq_pi, Fintype.card_fin] using
      measureReal_norm_toLp_le_pi_properComplexGaussianScalar (ι := Fin d) t hs)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- The gamma Chernoff bound for the distance of a shifted, scaled standard complex Gaussian
vector to a fixed complex subspace. The distance threshold scales with the Gaussian coefficient. -/
theorem measureReal_infDist_add_smul_lt_pi_properComplexGaussianScalar
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {Y : Ω → ι → ℂ}
    (hY : HasLaw Y (Measure.pi fun _ ↦ properComplexGaussianScalar) P)
    (U : Submodule ℂ (EuclideanSpace ℂ ι)) (u : ι → ℂ) (a : ℂ) (t : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    P.real {ω | infDist (toLp 2 (u + a • Y ω)) (U : Set _) < ‖a‖ * t} ≤
      Real.exp (s * t ^ 2) / (1 + s) ^ finrank ℂ Uᗮ := by
  let := hY.isProbabilityMeasure
  by_cases ha : a = 0
  · have hpos : 0 ≤ Real.exp (s * t ^ 2) / (1 + s) ^ finrank ℂ Uᗮ := by positivity
    simpa [ha, not_lt.mpr infDist_nonneg] using hpos
  let E : Set (ι → ℂ) := {x | infDist (toLp 2 (a⁻¹ • u + x)) (U : Set _) ≤ t}
  have hE : MeasurableSet E := measurableSet_le
    ((continuous_infDist_pt (U : Set (EuclideanSpace ℂ ι))).measurable.comp (by fun_prop))
    measurable_const
  have hYE := map_measureReal_apply_of_aemeasurable hY.aemeasurable hE
  rw [hY.map_eq] at hYE
  refine (measureReal_mono (s₂ := Y ⁻¹' E) ?_).trans (hYE.ge.trans
    (measureReal_infDist_toLp_add_le_pi_properComplexGaussianScalar U (a⁻¹ • u) t hs))
  intro ω hω
  have heq : toLp 2 (u + a • Y ω) = a • toLp 2 (a⁻¹ • u + Y ω) := by
    ext j
    simp [ha]
  have hproj (y : EuclideanSpace ℂ ι) : ‖Uᗮ.starProjection y‖ = infDist y (U : Set _) := by
    rw [Uᗮ.norm_starProjection_eq_infDist, Submodule.orthogonal_orthogonal]
  have hscale (y : EuclideanSpace ℂ ι) :
      infDist (a • y) (U : Set _) = ‖a‖ * infDist y (U : Set _) := by
    rw [← hproj, ← hproj, map_smul, norm_smul]
  simp only [mem_ofPred_eq, heq, hscale] at hω
  exact ((mul_lt_mul_iff_right₀ (norm_pos_iff.mpr ha)).mp hω).le

end ProbabilityTheory.HasLaw
