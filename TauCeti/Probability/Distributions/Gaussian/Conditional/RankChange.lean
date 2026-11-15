/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Continuity
public import TauCeti.Probability.Distributions.Gaussian.LowDimension

/-!
# Gaussian conditioning across a covariance rank change

Let `Z` be standard Gaussian. The covariance of `(Z, tZ)` varies continuously with `t`, so the
joint Gaussian laws converge weakly as `t` tends to zero. The pseudoinverse conditional kernel
has different behaviour: conditioning the first coordinate on the second at zero gives the point
mass at zero for `t ≠ 0`, but at `t = 0` the observation is constant and the kernel returns the
unconditional standard Gaussian law. The observed covariance `[t²]` drops rank at zero, while the
joint covariance retains rank one for every `t`.

This is the basic rank-change example showing why regular conditional distributions need not
depend continuously on a covariance parameter, even when the corresponding joint laws do.

## Main results

* `TauCeti.Probability.continuous_multivariateGaussian_gaussianRankChangeCovariance`: the joint
  laws of `(Z, tZ)` vary weakly continuously with `t`;
* `TauCeti.Probability.gaussianCondKernel_gaussianRankChangeCovariance_zero_of_ne_zero`: at
  nonzero `t`, conditioning at zero gives `δ₀`;
* `TauCeti.Probability.gaussianCondKernel_gaussianRankChangeCovariance_zero_zero`: at `t = 0`, the
  same kernel is the unconditional standard Gaussian law;
* `TauCeti.Probability.not_continuousAt_gaussianCondKernel_gaussianRankChangeCovariance_zero_zero`:
  consequently, these conditional laws are not weakly continuous at zero.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory Topology

namespace TauCeti.Probability

/-- The covariance matrix of the singular Gaussian pair `(Z, tZ)`, where `Z` is standard
Gaussian. -/
def gaussianRankChangeCovariance (t : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ :=
  Matrix.vecMulVec (Sum.elim (fun _ ↦ 1) fun _ ↦ t) (Sum.elim (fun _ ↦ 1) fun _ ↦ t)

/-- `gaussianRankChangeCovariance t` is the outer product of the vector `(1, t)` with itself. -/
theorem gaussianRankChangeCovariance_eq_vecMulVec (t : ℝ) :
    gaussianRankChangeCovariance t =
      Matrix.vecMulVec (Sum.elim (fun _ ↦ 1) fun _ ↦ t) (Sum.elim (fun _ ↦ 1) fun _ ↦ t) := by
  rw [gaussianRankChangeCovariance]

/-- The first-coordinate variance in `gaussianRankChangeCovariance` is one. -/
@[simp]
theorem gaussianRankChangeCovariance_inl_inl (t : ℝ) (i j : Unit) :
    gaussianRankChangeCovariance t (Sum.inl i) (Sum.inl j) = 1 := by
  simp [gaussianRankChangeCovariance_eq_vecMulVec, Matrix.vecMulVec_apply]

/-- The covariance from the first coordinate to the observed coordinate is `t`. -/
@[simp]
theorem gaussianRankChangeCovariance_inl_inr (t : ℝ) (i j : Unit) :
    gaussianRankChangeCovariance t (Sum.inl i) (Sum.inr j) = t := by
  simp [gaussianRankChangeCovariance_eq_vecMulVec, Matrix.vecMulVec_apply]

/-- The covariance from the observed coordinate to the first coordinate is `t`. -/
@[simp]
theorem gaussianRankChangeCovariance_inr_inl (t : ℝ) (i j : Unit) :
    gaussianRankChangeCovariance t (Sum.inr i) (Sum.inl j) = t := by
  simp [gaussianRankChangeCovariance_eq_vecMulVec, Matrix.vecMulVec_apply]

/-- The observed-coordinate variance in `gaussianRankChangeCovariance` is `t²`. -/
@[simp]
theorem gaussianRankChangeCovariance_inr_inr (t : ℝ) (i j : Unit) :
    gaussianRankChangeCovariance t (Sum.inr i) (Sum.inr j) = t ^ 2 := by
  simp [gaussianRankChangeCovariance_eq_vecMulVec, Matrix.vecMulVec_apply, pow_two]

/-- The covariance matrix of `(Z, tZ)` is positive semidefinite for every real `t`. -/
theorem posSemidef_gaussianRankChangeCovariance (t : ℝ) :
    (gaussianRankChangeCovariance t).PosSemidef := by
  simpa [gaussianRankChangeCovariance_eq_vecMulVec] using Matrix.posSemidef_vecMulVec_self_star
    (Sum.elim (fun _ : Unit ↦ (1 : ℝ)) fun _ : Unit ↦ t)

/-- The covariance matrix of `(Z, tZ)` depends continuously on `t`. -/
theorem continuous_gaussianRankChangeCovariance : Continuous gaussianRankChangeCovariance := by
  have hv : Continuous fun t : ℝ ↦ (Sum.elim (fun _ ↦ 1) fun _ ↦ t : Unit ⊕ Unit → ℝ) := by
    refine continuous_pi fun i ↦ ?_
    rcases i with _ | _
    · exact continuous_const
    · exact continuous_id
  exact (hv.matrix_vecMulVec hv).congr fun t ↦ (gaussianRankChangeCovariance_eq_vecMulVec t).symm

/-- The joint Gaussian laws of `(Z, tZ)` vary weakly continuously with `t`, including when the
observed covariance drops rank at `t = 0`. -/
theorem continuous_multivariateGaussian_gaussianRankChangeCovariance :
    Continuous (fun t : ℝ ↦
      (multivariateGaussian (0 : EuclideanSpace ℝ (Unit ⊕ Unit))
        (gaussianRankChangeCovariance t)).toProbabilityMeasure) := by
  exact Continuous.multivariateGaussian continuous_const continuous_gaussianRankChangeCovariance
    posSemidef_gaussianRankChangeCovariance

/-- At a nonzero rank parameter, observing `tZ = 0` determines `Z = 0`, so the displayed
pseudoinverse conditional kernel is the point mass at zero. -/
theorem gaussianCondKernel_gaussianRankChangeCovariance_zero_of_ne_zero {t : ℝ} (ht : t ≠ 0) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
        (gaussianRankChangeCovariance t) 0 =
      Measure.dirac (0 : EuclideanSpace ℝ Unit) := by
  rw [EuclideanSpace.gaussianCondKernel_apply_of_unique_of_posSemidef
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit))
    (posSemidef_gaussianRankChangeCovariance t) 0
    (v₁ := 1) (v₂ := t ^ 2) (ρ := t / |t|)]
  · simp [ht, div_pow, gaussianReal_zero_var, (PiLp.single_eq_zero_iff 2 ()).mpr rfl]
  · simp
  · simp [pow_two]
  · simp [Real.sqrt_sq_eq_abs]

/-- At the rank parameter `t = 0`, the observed coordinate is constant, so the displayed
conditional kernel returns the unconditional standard Gaussian first marginal. -/
theorem gaussianCondKernel_gaussianRankChangeCovariance_zero_zero :
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
        (gaussianRankChangeCovariance 0) 0 =
      multivariateGaussian (0 : EuclideanSpace ℝ Unit) 1 := by
  have hzero : (gaussianRankChangeCovariance 0).submatrix Sum.inr Sum.inr = 0 := by
    ext
    simp
  rw [EuclideanSpace.gaussianCondKernel_of_submatrix_eq_zero _ hzero, map_zero, Prod.fst_zero]
  congr 1
  ext
  simp

/-- Although the joint laws vary weakly continuously, the displayed conditional laws at
observation zero are not weakly continuous when the observed covariance drops rank. -/
theorem not_continuousAt_gaussianCondKernel_gaussianRankChangeCovariance_zero_zero :
    ¬ContinuousAt (fun t : ℝ ↦
      ((0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
        (gaussianRankChangeCovariance t) 0).toProbabilityMeasure) 0 := by
  intro hcontinuous
  let F : ℝ → ProbabilityMeasure (EuclideanSpace ℝ Unit) := fun t ↦
    ((0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
      (gaussianRankChangeCovariance t) 0).toProbabilityMeasure
  let δ : ProbabilityMeasure (EuclideanSpace ℝ Unit) :=
    (Measure.dirac (0 : EuclideanSpace ℝ Unit)).toProbabilityMeasure
  let u : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hu : Tendsto u atTop (𝓝 0) := by
    simpa only [u] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hune (n : ℕ) : u n ≠ 0 := by
    dsimp only [u]
    exact one_div_ne_zero (by positivity)
  have hFδ (n : ℕ) : F (u n) = δ := by
    exact ProbabilityMeasure.toMeasure_injective (by
      simpa only [F, δ, Measure.coe_toProbabilityMeasure] using
        gaussianCondKernel_gaussianRankChangeCovariance_zero_of_ne_zero (hune n))
  have htoF : Tendsto (fun n ↦ F (u n)) atTop (𝓝 (F 0)) := by
    exact hcontinuous.tendsto.comp hu
  have htoδ : Tendsto (fun n ↦ F (u n)) atTop (𝓝 δ) := by
    simpa only [hFδ] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ δ) atTop (𝓝 δ))
  have heq : F 0 = δ := tendsto_nhds_unique htoF htoδ
  have hmeasure :
      multivariateGaussian (0 : EuclideanSpace ℝ Unit) 1 =
        Measure.dirac (0 : EuclideanSpace ℝ Unit) := by
    have hcoe := congrArg (fun μ : ProbabilityMeasure (EuclideanSpace ℝ Unit) ↦
      (μ : Measure (EuclideanSpace ℝ Unit))) heq
    simpa only [F, δ, Measure.coe_toProbabilityMeasure,
      gaussianCondKernel_gaussianRankChangeCovariance_zero_zero] using hcoe
  exact one_ne_zero ((multivariateGaussian_eq_dirac_iff 0 Matrix.PosSemidef.one).mp hmeasure)

end TauCeti.Probability
