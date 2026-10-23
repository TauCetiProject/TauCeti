/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.LogNormal.Basic
public import TauCeti.Analysis.InnerProductSpace.PiL2

/-!
# Multivariate log-normal laws

The multivariate log-normal law is the coordinatewise exponential of a multivariate Gaussian.
It is concentrated in the positive orthant, and taking coordinatewise logarithms recovers the
Gaussian law. Coordinate marginals are scalar log-normal laws, and log-affine maps transform
its Gaussian parameters by the usual affine covariance rule.

All covariance parameters give probability measures. A covariance that is not positive
semidefinite inherits the Gaussian Dirac fallback; a zero covariance also gives a point mass.
No nonemptiness assumption is made on the finite coordinate type.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The coordinatewise exponential of the Gaussian with log-mean `m` and log-covariance `S`.
An invalid covariance gives the point mass at the coordinatewise exponential of `m`. -/
def multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    Measure (EuclideanSpace ℝ ι) :=
  (multivariateGaussian m S).map (fun x ↦ WithLp.toLp 2 (fun i ↦ Real.exp (x i)))

/-- The defining exponential pushforward of the multivariate log-normal law. -/
theorem multivariateLogNormalMeasure_def (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    multivariateLogNormalMeasure m S =
      (multivariateGaussian m S).map (fun x ↦ WithLp.toLp 2 (fun i ↦ Real.exp (x i))) := (rfl)

/-- Every covariance parameter defines a probability measure, including the invalid fallback. -/
instance isProbabilityMeasure_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) : IsProbabilityMeasure (multivariateLogNormalMeasure m S) := by
  rw [multivariateLogNormalMeasure_def]
  infer_instance

/-- Invalid covariance parameters give a Dirac law. -/
theorem multivariateLogNormalMeasure_of_not_posSemidef (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : ¬ S.PosSemidef) :
    multivariateLogNormalMeasure m S =
      Measure.dirac (WithLp.toLp 2 (fun i ↦ Real.exp (m i))) := by
  rw [multivariateLogNormalMeasure_def, multivariateGaussian_of_not_posSemidef m hS,
    Measure.map_dirac' (by fun_prop)]

/-- Zero log-covariance gives the point mass at `exp m`. -/
@[simp]
theorem multivariateLogNormalMeasure_zero (m : EuclideanSpace ℝ ι) :
    multivariateLogNormalMeasure m 0 =
      Measure.dirac (WithLp.toLp 2 (fun i ↦ Real.exp (m i))) := by
  simp [multivariateLogNormalMeasure_def, multivariateGaussian]

/-- A multivariate log-normal vector has every coordinate strictly positive almost surely. -/
theorem ae_pos_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    ∀ᵐ x ∂multivariateLogNormalMeasure m S, ∀ i, 0 < x i := by
  rw [multivariateLogNormalMeasure_def]
  exact (ae_map_iff (by fun_prop) EuclideanSpace.measurableSet_setOf_forall_pos).mpr
    (ae_of_all _ fun x i ↦ Real.exp_pos (x i))

/-- Coordinatewise logarithms recover the original Gaussian, even at invalid covariances. -/
@[simp]
theorem map_log_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) :
    (multivariateLogNormalMeasure m S).map
        (fun x ↦ WithLp.toLp 2 (fun i ↦ Real.log (x i))) = multivariateGaussian m S := by
  rw [multivariateLogNormalMeasure_def, Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

/-- A coordinate of a multivariate log-normal vector has the scalar log-normal law. -/
@[simp]
theorem map_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    (multivariateLogNormalMeasure m S).map (fun x ↦ x i) =
      logNormalMeasure (m i) (S i i).toNNReal := by
  rw [multivariateLogNormalMeasure_def, logNormalMeasure_map_exp,
    ← (measurePreserving_eval_multivariateGaussian (μ := m) hS (i := i)).map_eq,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- Joint Giry measurability in the log-mean and all raw covariance coordinates. -/
@[fun_prop]
theorem measurable_multivariateLogNormalMeasure :
    Measurable (fun p : EuclideanSpace ℝ ι × (ι → ι → ℝ) ↦
      multivariateLogNormalMeasure p.1 (Matrix.of p.2)) := by
  simp only [multivariateLogNormalMeasure_def]
  exact (Measure.measurable_map _ (by fun_prop)).comp
    (ProbabilityTheory.measurable_multivariateGaussian.comp
      (measurable_fst.prodMk (by fun_prop)))

/-- Coordinatewise exponentiation sends a Gaussian random vector to a log-normal vector. -/
theorem hasLaw_exp_multivariateGaussian {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hX : HasLaw X (multivariateGaussian m S) P) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ Real.exp (X ω i)))
      (multivariateLogNormalMeasure m S) P := by
  simpa only [multivariateLogNormalMeasure_def, Function.comp_def] using
    HasLaw.comp ⟨by fun_prop, multivariateLogNormalMeasure_def m S |>.symm⟩ hX

/-- Log-affine transport: `exp (L log X + c)` has the affinely transformed Gaussian parameters.
The matrix `L` may be rectangular or rank deficient. -/
theorem map_logAffine_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (L : Matrix κ ι ℝ) (c : EuclideanSpace ℝ κ) :
    (multivariateLogNormalMeasure m S).map
        (fun x ↦ WithLp.toLp 2 (fun j ↦ Real.exp
          ((L.toEuclideanLin (WithLp.toLp 2 (fun i ↦ Real.log (x i))) + c) j))) =
      multivariateLogNormalMeasure (L.toEuclideanLin m + c) (L * S * L.transpose) := by
  rw [multivariateLogNormalMeasure_def, multivariateLogNormalMeasure_def,
    ← map_affine_multivariateGaussian m hS L c,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  simp [Function.comp_def]

end TauCeti.Probability
