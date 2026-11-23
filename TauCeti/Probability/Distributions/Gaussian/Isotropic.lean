/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Projection
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Independence.Map

/-!
# Isotropic Gaussian vectors

A vector with scalar covariance matrix is obtained by scaling and translating a standard
Gaussian. A nonzero scale allows standardization, and the squared length of a centered
projection divided by the variance has chi-squared law with degrees of freedom equal to the
dimension of the subspace. Projections onto two orthogonal subspaces are independent even
at zero scale.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EuclideanSpace

open TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scaling the standard Gaussian by `σ` and translating by `m` gives covariance `σ² I`.
The formula includes `σ = 0`. -/
theorem multivariateGaussian_sq_smul_one_eq_map_stdGaussian
    (m : EuclideanSpace ℝ ι) (σ : ℝ) :
    multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ)) =
      (stdGaussian (EuclideanSpace ℝ ι)).map (fun z ↦ m + σ • z) := by
  -- Specialize the affine Gaussian transport to the standard Gaussian.
  simpa only [multivariateGaussian_zero_one, smul_zero, add_zero] using
    (map_add_smul_multivariateGaussian 0 Matrix.PosSemidef.one m σ).symm

/-- Independent Gaussian coordinates with a common variance give a Euclidean Gaussian vector
with scalar covariance matrix. The means may vary across coordinates. -/
theorem map_pi_gaussianReal_eq_multivariateGaussian (m : EuclideanSpace ℝ ι) (v : ℝ≥0) :
    (Measure.pi fun i ↦ gaussianReal (m i) v).map (WithLp.toLp 2) =
      multivariateGaussian m ((v : ℝ) • (1 : Matrix ι ι ℝ)) := by
  let σ := Real.sqrt (v : ℝ)
  have hσ : σ ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
  have hcoord (i : ι) :
      (gaussianReal 0 1).map (fun x ↦ m i + σ * x) = gaussianReal (m i) v := by
    rw [gaussianReal_map_const_add_const_mul, mul_zero, add_zero, mul_one]
    congr 1
    exact NNReal.coe_injective hσ
  rw [← hσ, multivariateGaussian_sq_smul_one_eq_map_stdGaussian, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp_rw [← hcoord]
  rw [← Measure.pi_map_pi (fun _ ↦ by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

end EuclideanSpace

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

section Standard

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {Z : Ω → E}

/-- A real linear functional of a standard Gaussian is centered Gaussian with variance the
squared norm of the functional. In particular a unit functional has law `gaussianReal 0 1`. -/
theorem HasLaw.strongDual_stdGaussian (hZ : HasLaw Z (stdGaussian E) P)
    (L : StrongDual ℝ E) :
    HasLaw (fun ω ↦ L (Z ω)) (gaussianReal 0 ((‖L‖ ^ 2 : ℝ).toNNReal)) P := by
  refine (HasLaw.mk (by fun_prop) ?_).fun_comp hZ
  rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian, variance_dual_stdGaussian]

end Standard

section Isotropic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {m : EuclideanSpace ℝ ι} {Y : Ω → EuclideanSpace ℝ ι} {σ : ℝ}

/-- Subtracting the mean and dividing by the nonzero scale of an isotropic Gaussian yields
a standard Gaussian vector. -/
theorem HasLaw.standardize_multivariateGaussian_smul_one
    (hY : HasLaw Y (multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ))) P)
    (hσ : σ ≠ 0) :
    HasLaw (fun ω ↦ σ⁻¹ • (Y ω - m)) (stdGaussian (EuclideanSpace ℝ ι)) P := by
  refine (HasLaw.mk (X := fun y : EuclideanSpace ℝ ι ↦ σ⁻¹ • (y - m)) (by fun_prop) ?_).fun_comp hY
  rw [m.multivariateGaussian_sq_smul_one_eq_map_stdGaussian, Measure.map_map (by fun_prop)
    (by fun_prop)]
  have hcomp : (fun y : EuclideanSpace ℝ ι ↦ σ⁻¹ • (y - m)) ∘ (fun z ↦ m + σ • z) =
      id := by
    funext z
    simp [smul_smul, hσ]
  rw [hcomp, Measure.map_id]

/-- The squared norm of any centered projection, divided by the sampling variance, has a
chi-squared law with degrees of freedom equal to the rank of the projection. -/
theorem HasLaw.norm_sq_starProjection_sub_div_multivariateGaussian_smul_one
    (hY : HasLaw Y (multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ))) P)
    (hσ : σ ≠ 0) (K : Submodule ℝ (EuclideanSpace ℝ ι)) :
    HasLaw (fun ω ↦ ‖K.starProjection (Y ω - m)‖ ^ 2 / σ ^ 2)
      (chiSquaredMeasure (Module.finrank ℝ K)) P := by
  have hZ := hY.standardize_multivariateGaussian_smul_one hσ
  refine (hZ.norm_sq_orthogonalProjectionOnto_stdGaussian K).congr ?_
  refine Filter.Eventually.of_forall fun ω ↦ ?_
  simp only [← Submodule.norm_coe, ← Submodule.starProjection_apply, map_smul, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, inv_pow]
  rw [div_eq_inv_mul]

/-- Orthogonal projections of an isotropic Gaussian are independent, including at zero scale. -/
theorem HasLaw.indepFun_orthogonalProjectionOnto_multivariateGaussian_smul_one
    (hY : HasLaw Y (multivariateGaussian m (σ ^ 2 • (1 : Matrix ι ι ℝ))) P)
    {K L : Submodule ℝ (EuclideanSpace ℝ ι)} (hKL : K ⟂ L) :
    IndepFun (fun ω ↦ K.orthogonalProjectionOnto (Y ω))
      (fun ω ↦ L.orthogonalProjectionOnto (Y ω)) P := by
  refine (indepFun_map_iff_comp hY.aemeasurable (f := K.orthogonalProjectionOnto)
    (g := L.orthogonalProjectionOnto) (by fun_prop) (by fun_prop)).1 ?_
  rw [hY.map_eq, m.multivariateGaussian_sq_smul_one_eq_map_stdGaussian,
    indepFun_map_iff_comp (by fun_prop) (by fun_prop) (by fun_prop)]
  have h := (HasLaw.id (μ := stdGaussian (EuclideanSpace ℝ ι)))
    |>.indepFun_orthogonalProjectionOnto_stdGaussian hKL
  simpa [Function.comp_def, map_add, map_smul] using
    h.comp (φ := fun k ↦ K.orthogonalProjectionOnto m + σ • k)
      (ψ := fun l ↦ L.orthogonalProjectionOnto m + σ • l) (by fun_prop) (by fun_prop)

end Isotropic

end ProbabilityTheory
