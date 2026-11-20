/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Conditional.Basic

import TauCeti.Data.Matrix.Mul
import TauCeti.LinearAlgebra.Matrix.PosSemidef
import TauCeti.Probability.Distributions.Gaussian.Conditional.RankOne

/-!
# Gaussian conditioning on repeated observations

With constant mean and positive constant covariance, the pseudoinverse conditional kernel is a
Dirac measure at the average observed coordinate, even away from the diagonal support. For a
joint law made by replicating a scalar Gaussian, this kernel gives the regular conditional law
of the scalar given the replicated observations.

## References

* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley, 2003.
-/

public section

noncomputable section

open Matrix MeasureTheory ProbabilityTheory
open scoped NNReal

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
  have hcov : (Matrix.of fun _ _ ↦ c : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ) =
      vecMulVec (fun _ ↦ √c) (fun _ ↦ √c) := by
    rw [vecMulVec_const_const, Real.mul_self_sqrt hc.le]
  have hload : ∃ j : κ, (fun _ : ι ⊕ κ ↦ √c) (Sum.inr j) ≠ 0 :=
    ⟨Classical.arbitrary κ, (Real.sqrt_pos.2 hc).ne'⟩
  rw [hcov, gaussianCondKernel_vecMulVec_self _ hload]
  congr 1
  ext i
  rw [gaussianCondMean_vecMulVec_self_apply]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.sq_sqrt hc.le,
    ← Finset.mul_sum, Finset.sum_sub_distrib]
  rw [← mul_assoc, Real.mul_self_sqrt hc.le]
  have hn : (Fintype.card κ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  field_simp [hc.ne']
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

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open EuclideanSpace TauCeti.Probability

variable {Ω ι κ : Type*} [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → EuclideanSpace ℝ (ι ⊕ κ)}

/-- The regular conditional law for jointly Gaussian coordinates with a common mean and
positive constant covariance agrees almost everywhere with the average-observation kernel. -/
theorem condDistrib_multivariateGaussian_toLp_const_matrixOf_const
    [DecidableEq ι] [DecidableEq κ] [Nonempty κ] {μ c : ℝ}
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

/-- A scalar Gaussian of positive variance, conditioned on a nonempty finite block of copies
(in particular, on two copies), has regular conditional law given by the Dirac measure at the
average observation. The observation covariance is singular when there is more than one copy. -/
theorem condDistrib_gaussianReal_toLp_const [Nonempty κ] {Z : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hZ : HasLaw Z (gaussianReal μ v) P) (hv : 0 < v) :
    condDistrib Z (fun ω ↦ WithLp.toLp 2 (fun _ : κ ↦ Z ω)) P =ᵐ[
      P.map (fun ω ↦ WithLp.toLp 2 (fun _ : κ ↦ Z ω))]
      (fun x ↦ Measure.dirac ((∑ j, x j) / Fintype.card κ)) := by
  classical
  let X : Ω → EuclideanSpace ℝ (Unit ⊕ κ) := fun ω ↦ WithLp.toLp 2 (fun _ ↦ Z ω)
  let Y : Ω → EuclideanSpace ℝ Unit := fun ω ↦ (sumEquivProd (X ω)).1
  let A : Ω → EuclideanSpace ℝ κ := fun ω ↦ (sumEquivProd (X ω)).2
  let e : EuclideanSpace ℝ Unit → ℝ := fun y ↦ y ()
  have hX : HasLaw X (multivariateGaussian (WithLp.toLp 2 (fun _ ↦ μ))
      (Matrix.of fun _ _ ↦ (v : ℝ))) P :=
    (HasLaw.mk (by fun_prop) (map_toLp_const_gaussianReal (Unit ⊕ κ) μ v)).fun_comp hZ
  have hA : AEMeasurable A P := by dsimp [A]; fun_prop
  have hY : AEMeasurable Y P := by dsimp [Y]; fun_prop
  have he : Measurable e := by fun_prop
  have hcomp : condDistrib Z A P =ᵐ[P.map A] (condDistrib Y A P).map e :=
    condDistrib_comp hA hY he
  filter_upwards [hcomp, hX.condDistrib_multivariateGaussian_toLp_const_matrixOf_const
    (NNReal.coe_pos.mpr hv)] with x hx havg
  calc
    condDistrib Z A P x = ((condDistrib Y A P).map e) x := hx
    _ = _ := by rw [Kernel.map_apply _ he, havg, Measure.map_dirac' he]

end ProbabilityTheory.HasLaw
