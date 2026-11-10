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
unconditional standard Gaussian law.

This is the basic rank-change example showing why regular conditional distributions need not
depend continuously on a covariance parameter, even when the corresponding joint laws do.

## Main results

* `TauCeti.Probability.continuous_multivariateGaussian_rankChange`: the joint laws of `(Z, tZ)`
  vary weakly continuously with `t`;
* `TauCeti.Probability.gaussianCondKernel_rankChange_zero_of_ne`: at nonzero `t`, conditioning at
  zero gives `δ₀`;
* `TauCeti.Probability.gaussianCondKernel_rankChange_zero`: at `t = 0`, the same kernel is the
  unconditional standard Gaussian law;
* `TauCeti.Probability.not_continuousAt_gaussianCondKernel_rankChange_zero`: consequently, these
  conditional laws are not weakly continuous at zero.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory ProbabilityTheory Topology
open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

/-- The covariance matrix of the singular Gaussian pair `(Z, tZ)`, where `Z` is standard
Gaussian. -/
def gaussianRankChangeCovariance (t : ℝ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℝ :=
  let v : Unit ⊕ Unit → ℝ := Sum.elim (fun _ ↦ 1) (fun _ ↦ t)
  Matrix.vecMulVec v v

/-- The covariance matrix of `(Z, tZ)` is positive semidefinite for every real `t`. -/
theorem gaussianRankChangeCovariance_posSemidef (t : ℝ) :
    (gaussianRankChangeCovariance t).PosSemidef := by
  simpa [gaussianRankChangeCovariance] using Matrix.posSemidef_vecMulVec_self_star
    (Sum.elim (fun _ : Unit ↦ (1 : ℝ)) fun _ : Unit ↦ t)

/-- The joint Gaussian laws of `(Z, tZ)` vary weakly continuously with `t`, including at the
rank drop `t = 0`. -/
theorem continuous_multivariateGaussian_rankChange :
    Continuous (fun t : ℝ ↦
      (multivariateGaussian (0 : EuclideanSpace ℝ (Unit ⊕ Unit))
        (gaussianRankChangeCovariance t)).toProbabilityMeasure) := by
  apply Continuous.multivariateGaussian continuous_const
  · unfold gaussianRankChangeCovariance
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.vecMulVec_apply] using (continuous_const : Continuous fun _ : ℝ ↦ (1 : ℝ))
    · simpa only [Matrix.vecMulVec_apply, Sum.elim_inl, Sum.elim_inr, one_mul] using
        (continuous_id' : Continuous fun t : ℝ ↦ t)
    · simpa only [Matrix.vecMulVec_apply, Sum.elim_inl, Sum.elim_inr, mul_one] using
        (continuous_id' : Continuous fun t : ℝ ↦ t)
    · change Continuous fun t : ℝ ↦ t * t
      fun_prop
  · exact gaussianRankChangeCovariance_posSemidef

/-- At a nonzero rank parameter, observing `tZ = 0` determines `Z = 0`, so the displayed
pseudoinverse conditional kernel is the point mass at zero. -/
theorem gaussianCondKernel_rankChange_zero_of_ne {t : ℝ} (ht : t ≠ 0) :
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
        (gaussianRankChangeCovariance t) 0 =
      Measure.dirac (0 : EuclideanSpace ℝ Unit) := by
  rw [EuclideanSpace.gaussianCondKernel_apply_of_unique_of_posSemidef
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit))
    (gaussianRankChangeCovariance_posSemidef t) 0
    (v₁ := 1) (v₂ := t ^ 2) (ρ := t / |t|)]
  · simp only [PiLp.zero_apply, sub_zero, mul_zero, add_zero]
    have habs : |t| ≠ 0 := abs_ne_zero.mpr ht
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 ht)]
    simp only [PUnit.default_eq_unit, sub_self, mul_zero, Real.toNNReal_zero,
      gaussianReal_zero_var, Measure.map_dirac]
    rw [show EuclideanSpace.single default 0 = (0 : EuclideanSpace ℝ Unit) by
      ext
      simp]
  · simp [gaussianRankChangeCovariance, Matrix.vecMulVec_apply]
  · simp [gaussianRankChangeCovariance, Matrix.vecMulVec_apply, pow_two]
  · simp [gaussianRankChangeCovariance, Matrix.vecMulVec_apply, Real.sqrt_sq_eq_abs]

/-- At the rank parameter `t = 0`, the observed coordinate is constant, so the displayed
conditional kernel returns the unconditional standard Gaussian first marginal. -/
theorem gaussianCondKernel_rankChange_zero :
    (0 : EuclideanSpace ℝ (Unit ⊕ Unit)).gaussianCondKernel
        (gaussianRankChangeCovariance 0) 0 =
      multivariateGaussian (0 : EuclideanSpace ℝ Unit) 1 := by
  have hzero : (gaussianRankChangeCovariance 0).submatrix Sum.inr Sum.inr = 0 := by
    ext
    simp [gaussianRankChangeCovariance, Matrix.vecMulVec_apply]
  rw [EuclideanSpace.gaussianCondKernel_of_submatrix_eq_zero _ hzero]
  congr 1
  ext
  simp [gaussianRankChangeCovariance, Matrix.vecMulVec_apply]

/-- Although the joint laws vary weakly continuously, the displayed conditional laws at
observation zero are not weakly continuous at the rank drop. -/
theorem not_continuousAt_gaussianCondKernel_rankChange_zero :
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
    exact Subtype.ext (gaussianCondKernel_rankChange_zero_of_ne (hune n))
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
      gaussianCondKernel_rankChange_zero] using hcoe
  have hchar := congrArg
    (fun μ : Measure (EuclideanSpace ℝ Unit) ↦
      charFun μ (EuclideanSpace.single default 1)) hmeasure
  rw [charFun_multivariateGaussian Matrix.PosSemidef.one, charFun_dirac] at hchar
  have hquad :
      (EuclideanSpace.single (default : Unit) (1 : ℝ)).ofLp ⬝ᵥ
          (EuclideanSpace.single (default : Unit) (1 : ℝ)).ofLp = 1 := by
    simp [dotProduct]
  norm_num [hquad] at hchar
  have hnorm := congrArg norm hchar
  norm_num [Complex.norm_exp] at hnorm

end TauCeti.Probability
