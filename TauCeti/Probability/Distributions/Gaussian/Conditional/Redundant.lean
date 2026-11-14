/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

import TauCeti.Data.Matrix.Mul
import TauCeti.LinearAlgebra.Matrix.PosSemidef

/-!
# Gaussian conditioning on redundant observations

A rank-one jointly Gaussian vector consists of affine functions of one scalar Gaussian.
Any nonconstant observed block therefore determines the retained block exactly. The conditional
covariance vanishes, and the pseudoinverse regression formula gives a Dirac law, even though
an observed block with several coordinates has singular covariance.

In particular, any nonempty finite block of identical Gaussian coordinates determines any
retained block of copies, for arbitrary common mean and positive variance. The conditional
kernel is specified at every ambient observation and uses the average observed coordinate,
including off the diagonal support. We also prove the almost-everywhere `condDistrib` identity
for jointly Gaussian vectors and, under mere a.e. measurability, for pathwise copies of any
scalar random variable; the latter includes Gaussian copies of zero variance.

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

end EuclideanSpace

namespace TauCeti.Probability

open EuclideanSpace

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- For a constant mean and positive constant covariance, the conditional Gaussian kernel
uses the average observation at every ambient input, including off the diagonal support. -/
theorem gaussianCondKernel_toLp_const_matrixOf_const [Nonempty κ] (μ : ℝ) {c : ℝ}
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
@[simp 1100]
theorem gaussianCondKernel_toLp_const_matrixOf_const_toLp_const [Nonempty κ] (μ : ℝ)
    {c : ℝ} (hc : 0 < c) (z : ℝ) :
    gaussianCondKernel (WithLp.toLp 2 (fun _ : ι ⊕ κ ↦ μ))
        (Matrix.of fun _ _ ↦ c) (WithLp.toLp 2 (fun _ ↦ z)) =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ z)) := by
  simpa using gaussianCondKernel_toLp_const_matrixOf_const (ι := ι) μ hc
    (WithLp.toLp 2 (fun _ : κ ↦ z))

/-- With zero mean and positive constant covariance, regression is the average observation,
including at ambient inputs outside the diagonal support. -/
@[simp 1100]
theorem gaussianCondKernel_zero_matrixOf_const [Nonempty κ] {c : ℝ}
    (hc : 0 < c) (x : EuclideanSpace ℝ κ) :
    (0 : EuclideanSpace ℝ (ι ⊕ κ)).gaussianCondKernel (Matrix.of fun _ _ ↦ c) x =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ (∑ j, x j) / Fintype.card κ)) := by
  simpa only [← Pi.zero_def, WithLp.toLp_zero] using
    gaussianCondKernel_toLp_const_matrixOf_const (ι := ι) 0 hc x

/-- With zero mean and positive constant covariance, the conditional Gaussian kernel at a
constant observation is the Dirac law at that observation, even for singular observed covariance. -/
theorem gaussianCondKernel_zero_matrixOf_const_toLp_const [Nonempty κ] {c : ℝ}
    (hc : 0 < c) (z : ℝ) :
    (0 : EuclideanSpace ℝ (ι ⊕ κ)).gaussianCondKernel
        (Matrix.of fun _ _ ↦ c) (WithLp.toLp 2 (fun _ ↦ z)) =
      Measure.dirac (WithLp.toLp 2 (fun _ : ι ↦ z)) := by
  simpa using gaussianCondKernel_zero_matrixOf_const (ι := ι) hc
    (WithLp.toLp 2 (fun _ : κ ↦ z))

end TauCeti.Probability

namespace TauCeti.Probability

attribute [local instance] Fintype.ofFinite

/-- Given a nonempty block of copies of an a.e. measurable scalar random variable, the
conditional law of another block is almost everywhere the Dirac law at the observed average.
No off-support claim about `condDistrib` is made. -/
theorem condDistrib_toLp_const {Ω ι κ : Type*} [MeasurableSpace Ω]
    [Finite ι] [Fintype κ] [Nonempty κ]
    {P : Measure Ω} [IsFiniteMeasure P] {Z : Ω → ℝ}
    (hZ : AEMeasurable Z P) :
    condDistrib (Ω := EuclideanSpace ℝ ι) (β := EuclideanSpace ℝ κ)
        (fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω))
        (fun ω ↦ (WithLp.toLp 2 (fun _ ↦ Z ω) : EuclideanSpace ℝ κ)) P =ᵐ[
      P.map (β := EuclideanSpace ℝ κ) (fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω))]
      (fun x ↦ Measure.dirac (α := EuclideanSpace ℝ ι)
        (WithLp.toLp 2 (fun _ ↦ (∑ j, x j) / Fintype.card κ))) := by
  let Y : Ω → EuclideanSpace ℝ κ := fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω)
  let f : EuclideanSpace ℝ κ → EuclideanSpace ℝ ι :=
    fun x ↦ WithLp.toLp 2 (fun _ ↦ (∑ j, x j) / Fintype.card κ)
  have hf : Measurable f := by fun_prop
  have hY : AEMeasurable Y P := (by fun_prop : Measurable
    (fun z : ℝ ↦ WithLp.toLp 2 (fun _ : κ ↦ z))).comp_aemeasurable hZ
  have hcomp : f ∘ Y = (fun ω ↦ WithLp.toLp 2 (fun _ : ι ↦ Z ω)) := by
    funext ω
    simp [f, Y]
  have h := condDistrib_comp_self hY hf
  rw [hcomp] at h
  filter_upwards [h] with x hx
  simpa only [Kernel.deterministic_apply, f] using hx

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open EuclideanSpace TauCeti.Probability

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → EuclideanSpace ℝ (ι ⊕ κ)}

/-- For a jointly Gaussian vector of rank-one covariance, a nonzero observed loading makes
its conditional law almost everywhere a Dirac law at the regression mean. -/
theorem condDistrib_multivariateGaussian_vecMulVec {m : EuclideanSpace ℝ (ι ⊕ κ)}
    {u : ι → ℝ} {v : κ → ℝ}
    (hX : HasLaw X (multivariateGaussian m (vecMulVec (Sum.elim u v) (Sum.elim u v))) P)
    (hv : v ≠ 0) :
    condDistrib (fun ω ↦ (sumEquivProd (X ω)).1)
        (fun ω ↦ (sumEquivProd (X ω)).2) P =ᵐ[
      P.map (fun ω ↦ (sumEquivProd (X ω)).2)]
      (fun x ↦ Measure.dirac ((sumEquivProd m).1 + WithLp.toLp 2
        (fun i ↦ u i * (v ⬝ᵥ (x - (sumEquivProd m).2)) / (v ⬝ᵥ v)))) := by
  have hS : (vecMulVec (Sum.elim u v) (Sum.elim u v)).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star (Sum.elim u v)
  filter_upwards [TauCeti.Probability.condDistrib_multivariateGaussian X m hX hS] with x hx
  exact hx.trans (m.gaussianCondKernel_vecMulVec u v hv x)

/-- Identical jointly Gaussian coordinates of positive variance condition almost everywhere
to the Dirac law at the average observation, including singular observed covariance. -/
theorem condDistrib_multivariateGaussian_toLp_const_matrixOf_const [Nonempty κ]
    {μ c : ℝ}
    (hX : HasLaw X (multivariateGaussian (WithLp.toLp 2 (fun _ ↦ μ))
      (Matrix.of fun _ _ ↦ c)) P) (hc : 0 < c) :
    condDistrib (fun ω ↦ (sumEquivProd (X ω)).1)
        (fun ω ↦ (sumEquivProd (X ω)).2) P =ᵐ[
      P.map (fun ω ↦ (sumEquivProd (X ω)).2)]
      (fun x ↦ Measure.dirac (WithLp.toLp 2
        (fun _ : ι ↦ (∑ j, x j) / Fintype.card κ))) := by
  filter_upwards [TauCeti.Probability.condDistrib_multivariateGaussian X _ hX
    (TauCeti.posSemidef_const_of_nonneg hc.le)] with x hx
  exact hx.trans (gaussianCondKernel_toLp_const_matrixOf_const μ hc x)

end ProbabilityTheory.HasLaw
