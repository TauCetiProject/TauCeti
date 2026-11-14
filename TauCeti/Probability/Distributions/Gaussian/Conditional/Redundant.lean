/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

import TauCeti.LinearAlgebra.Matrix.RowCol

/-!
# Gaussian conditioning on redundant observations

A rank-one jointly Gaussian vector consists of affine functions of one scalar Gaussian.
Any nonconstant observed block therefore determines the retained block exactly. The conditional
covariance vanishes, and the pseudoinverse regression formula gives a Dirac law, even though
an observed block with several coordinates has singular covariance.

In particular, observing two copies of a standard Gaussian determines that Gaussian. The
conditional kernel is specified at every ambient observation: for two identical copies, its
extension off the diagonal uses the average of the observed coordinates.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype κ] [DecidableEq κ]

/-- For a rank-one joint covariance, a nonzero observed loading removes all conditional
variance, including when the observed covariance is singular. -/
@[simp]
theorem gaussianCondCov_vecMulVec (u : ι → ℝ) (v : κ → ℝ) (hv : v ≠ 0) :
    (vecMulVec (Sum.elim u v) (Sum.elim u v)).gaussianCondCov = 0 := by
  have hd : v ⬝ᵥ v ≠ 0 := fun h ↦ hv (dotProduct_self_eq_zero.mp h)
  simp only [Matrix.gaussianCondCov_def, submatrix_vecMulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, covariancePseudoInverse_vecMulVec]
  ext i j
  simp only [Matrix.sub_apply, Matrix.zero_apply, Matrix.mul_smul,
    Matrix.smul_mul, vecMulVec_mul_vecMulVec, vecMulVec_smul, smul_smul,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  field_simp
  ring

end TauCeti.Probability

namespace EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- For a rank-one covariance, regression onto a nonzero observed loading recovers the
latent scalar by its least-squares coordinate, at every ambient observed value. At zero
observed loading, the formula returns the unconditional mean. -/
theorem gaussianCondMean_vecMulVec (m : EuclideanSpace ℝ (ι ⊕ κ))
    (u : ι → ℝ) (v : κ → ℝ) (x : EuclideanSpace ℝ κ) :
    m.gaussianCondMean (vecMulVec (Sum.elim u v) (Sum.elim u v)) x =
      (sumEquivProd m).1 + WithLp.toLp 2
        (fun i ↦ u i * (v ⬝ᵥ (x - (sumEquivProd m).2)) / (v ⬝ᵥ v)) := by
  simp only [gaussianCondMean_def, submatrix_vecMulVec,
    Sum.elim_comp_inl, Sum.elim_comp_inr, covariancePseudoInverse_vecMulVec]
  congr 1
  ext i
  simp only [Matrix.toLpLin_apply, Matrix.mul_smul, vecMulVec_mul_vecMulVec,
    vecMulVec_smul, Matrix.smul_mulVec, vecMulVec_mulVec, Pi.smul_apply,
    op_smul_eq_smul, smul_eq_mul, WithLp.ofLp_toLp, WithLp.ofLp_sub]
  by_cases hd : v ⬝ᵥ v = 0
  · simp [dotProduct_self_eq_zero.mp hd]
  · field_simp

variable [DecidableEq ι]

/-- A nonconstant block of a rank-one jointly Gaussian vector determines the retained block.
This formula also specifies the kernel away from the observed affine support. -/
theorem gaussianCondKernel_vecMulVec (m : EuclideanSpace ℝ (ι ⊕ κ))
    (u : ι → ℝ) (v : κ → ℝ) (hv : v ≠ 0) (x : EuclideanSpace ℝ κ) :
    m.gaussianCondKernel (vecMulVec (Sum.elim u v) (Sum.elim u v)) x =
      Measure.dirac ((sumEquivProd m).1 + WithLp.toLp 2
        (fun i ↦ u i * (v ⬝ᵥ (x - (sumEquivProd m).2)) / (v ⬝ᵥ v))) := by
  rw [gaussianCondKernel_apply, TauCeti.Probability.gaussianCondCov_vecMulVec u v hv,
    gaussianCondMean_vecMulVec, TauCeti.Probability.multivariateGaussian_zero_right]

/-- For a constant mean and positive constant covariance, the conditional Gaussian kernel
uses the average observation at every ambient input, including off the diagonal support. -/
theorem gaussianCondKernel_toLp_const_of_const [Nonempty κ] (μ : ℝ) {c : ℝ}
    (hc : 0 < c) (x : EuclideanSpace ℝ κ) :
    gaussianCondKernel (WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ μ))
        (Matrix.of fun _ _ ↦ c) x =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ (∑ j, x j) / Fintype.card κ)) := by
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hv : (fun _ : κ ↦ Real.sqrt c) ≠ 0 := by
    intro h
    obtain ⟨j⟩ := ‹Nonempty κ›
    exact hs (congrFun h j)
  have h := gaussianCondKernel_vecMulVec (WithLp.toLp 2 (fun _ ↦ μ))
    (fun _ : ι ↦ Real.sqrt c) (fun _ : κ ↦ Real.sqrt c) hv x
  have hmean : (sumEquivProd (WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ μ))) =
      (WithLp.toLp 2 (fun _ : ι ↦ μ), WithLp.toLp 2 (fun _ : κ ↦ μ)) := by
    ext <;> rfl
  have helim : Sum.elim (fun _ : ι ↦ Real.sqrt c) (fun _ : κ ↦ Real.sqrt c) =
      (fun _ ↦ Real.sqrt c) := by
    simpa only [← Function.const_def] using
      (Sum.elim_const_const (α := ι) (β := κ) (Real.sqrt c))
  rw [helim, vecMulVec_const_const, Real.mul_self_sqrt hc.le, hmean] at h
  rw [h]
  congr 1
  ext i
  simp only [PiLp.add_apply, Pi.sub_apply, dotProduct, mul_sub, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp
  ring

/-- At a constant observation, the constant-parameter conditional Gaussian kernel is the
Dirac law at that observation, for any common mean and positive variance. -/
theorem gaussianCondKernel_toLp_const_of_const_toLp_const [Nonempty κ] (μ : ℝ)
    {c : ℝ} (hc : 0 < c) (z : ℝ) :
    gaussianCondKernel (WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ μ))
        (Matrix.of fun _ _ ↦ c) (WithLp.toLp 2 (fun _ ↦ z)) =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ z)) := by
  simpa using gaussianCondKernel_toLp_const_of_const (ι := ι) μ hc
    (WithLp.toLp 2 (fun _ : κ ↦ z))

/-- With zero mean and positive constant covariance, the conditional Gaussian kernel at a
constant observation is the Dirac law at that observation, even for singular observed covariance. -/
@[simp 1100]
theorem gaussianCondKernel_zero_of_const_toLp_const [Nonempty κ] {c : ℝ}
    (hc : 0 < c) (z : ℝ) :
    (0 : EuclideanSpace ℝ (ι ⊕ κ)).gaussianCondKernel
        (Matrix.of fun _ _ ↦ c) (WithLp.toLp 2 (fun _ ↦ z)) =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ z)) := by
  simpa only [← Pi.zero_def, WithLp.toLp_zero] using
    gaussianCondKernel_toLp_const_of_const_toLp_const (ι := ι) (κ := κ) 0 hc z

end EuclideanSpace

namespace ProbabilityTheory.HasLaw

attribute [local instance] Fintype.ofFinite

/-- Given a nonempty block of copies of a scalar Gaussian, the conditional law of another
block agrees almost everywhere under the observed law with the Dirac law at its average.
This includes zero variance; no off-support claim about `condDistrib` is made. -/
theorem condDistrib_toLp_const_gaussianReal {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Finite ι] [Fintype κ] [Nonempty κ]
    {P : Measure Ω} [IsFiniteMeasure P] {Z : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal μ v) P) :
    condDistrib (Ω := EuclideanSpace ℝ ι) (β := EuclideanSpace ℝ κ)
        (fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω))
        (fun ω ↦ (WithLp.toLp 2 (fun _ ↦ Z ω) : EuclideanSpace ℝ κ)) P =ᵐ[
      P.map (β := EuclideanSpace ℝ κ) (fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω))]
      (fun x ↦ Measure.dirac (α := EuclideanSpace ℝ ι)
        (WithLp.toLp 2 (fun _ ↦ (∑ j, x j) / Fintype.card κ))) := by
  classical
  by_cases hv : v = 0
  · -- The deterministic-function identity also covers the zero-variance boundary.
    let Y : Ω → EuclideanSpace ℝ κ := fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω)
    let f : EuclideanSpace ℝ κ → EuclideanSpace ℝ ι :=
      fun x ↦ WithLp.toLp 2 (fun _ ↦ (∑ j, x j) / Fintype.card κ)
    have hf : Measurable f := by fun_prop
    have hY : AEMeasurable Y P := (by fun_prop : Measurable
      (fun z : ℝ ↦ WithLp.toLp 2 (fun _ : κ ↦ z))).comp_aemeasurable hZ.aemeasurable
    have hcomp : f ∘ Y = (fun ω ↦ WithLp.toLp 2 (fun _ : ι ↦ Z ω)) := by
      funext ω
      simp [f, Y]
    have h := condDistrib_comp_self hY hf
    rw [hcomp] at h
    filter_upwards [h] with x hx
    simpa only [Kernel.deterministic_apply, f] using hx
  let X : Ω → EuclideanSpace ℝ (ι ⊕ κ) := fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω)
  let m : EuclideanSpace ℝ (ι ⊕ κ) := WithLp.toLp 2 (fun _ ↦ μ)
  let S : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ := Matrix.of fun _ _ ↦ (v : ℝ)
  have hX : HasLaw X (multivariateGaussian m S) P := by
    rw [← TauCeti.Probability.map_toLp_const_gaussianReal]
    exact (hasLaw_map (X := fun z : ℝ ↦ WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ z))
      (by fun_prop)).comp hZ
  have hS : S.PosSemidef := by
    have h := (Matrix.posSemidef_vecMulVec_self_star (fun _ : ι ⊕ κ ↦ (1 : ℝ))).smul
      v.coe_nonneg
    have hcov : (v : ℝ) • vecMulVec (fun _ : ι ⊕ κ ↦ (1 : ℝ)) (fun _ ↦ 1) = S := by
      ext
      simp [S, vecMulVec_apply]
    simpa only [star_trivial, hcov] using h
  have h := TauCeti.Probability.condDistrib_multivariateGaussian X m hX hS
  have hblocks (ω : Ω) : EuclideanSpace.sumEquivProd (X ω) =
      (WithLp.toLp 2 (fun _ : ι ↦ Z ω), WithLp.toLp 2 (fun _ : κ ↦ Z ω)) := by
    ext <;> rfl
  simp only [hblocks] at h
  filter_upwards [h] with x hx
  exact hx.trans (EuclideanSpace.gaussianCondKernel_toLp_const_of_const μ
    (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)) x)

end ProbabilityTheory.HasLaw
