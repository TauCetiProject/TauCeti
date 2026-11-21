/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.StudentT.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Concentration
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Transforms
import TauCeti.Probability.Distributions.MultivariateT.GaussianLimit
import TauCeti.Probability.Distributions.MultivariateT.Marginal
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Gaussian limits of Student t laws

Student t laws converge weakly to the standard Gaussian law as the degrees of freedom tend to
infinity. More generally, applying a fixed location-scale map gives convergence to the Gaussian
law with the corresponding mean and variance.

The proof specializes the multivariate t Gaussian limit to one coordinate. This keeps the scalar
result synchronized with the multivariate construction, including the precise topology of weak
convergence on `ProbabilityMeasure`.

## Main results

* `TauCeti.Probability.tendsto_studentTMeasure_atTop`: the standard Student t Gaussian limit.
* `TauCeti.Probability.tendsto_map_affine_studentTMeasure_atTop`: its location-scale form.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

/-- Student t laws converge weakly to the standard Gaussian law as the positive degrees of
freedom tend to infinity. -/
theorem tendsto_studentTMeasure_atTop :
    Tendsto (β := ProbabilityMeasure ℝ) (fun ν : Ioi (0 : ℝ) ↦
      (⟨studentTMeasure ν, isProbabilityMeasure_studentTMeasure ν.2⟩ :
        ProbabilityMeasure ℝ)) atTop
      (nhds (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)) := by
  let e : EuclideanSpace ℝ (Fin 1) → ℝ := fun x ↦ x 0
  let T : Ioi (0 : ℝ) → ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)) := fun ν ↦
    ⟨multivariateTMeasure 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ν,
      isProbabilityMeasure_multivariateTMeasure 0 ν.2 Matrix.PosSemidef.one⟩
  let G : ProbabilityMeasure (EuclideanSpace ℝ (Fin 1)) :=
    (multivariateGaussian 0 (1 : Matrix (Fin 1) (Fin 1) ℝ)).toProbabilityMeasure
  have hlim : Tendsto T atTop (nhds G) :=
    tendsto_multivariateTMeasure_atTop (0 : EuclideanSpace ℝ (Fin 1))
      Matrix.PosSemidef.one
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous T G hlim
    (show Continuous e by fun_prop)
  have hT (ν : Ioi (0 : ℝ)) :
      (T ν).map e =
        (⟨studentTMeasure ν, isProbabilityMeasure_studentTMeasure ν.2⟩ :
          ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (multivariateTMeasure 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) ν).map e =
      studentTMeasure ν
    simpa [e] using map_eval_multivariateTMeasure
      (0 : EuclideanSpace ℝ (Fin 1)) Matrix.PosSemidef.one (ν : ℝ) 0
  have hG : G.map e = (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ) := by
    apply ProbabilityMeasure.toMeasure_injective
    change (multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
      (1 : Matrix (Fin 1) (Fin 1) ℝ)).map e = gaussianReal 0 1
    simpa [EuclideanSpace.inner_single_left] using
      map_inner_multivariateGaussian (0 : EuclideanSpace ℝ (Fin 1))
        (EuclideanSpace.single 0 1) Matrix.PosSemidef.one
  simpa only [hT, hG] using hmap

/-- A fixed location-scale image of Student t laws converges weakly to the Gaussian law with
mean `m` and variance `s ^ 2`. This includes the zero-scale Dirac limit and negative scales. -/
theorem tendsto_map_affine_studentTMeasure_atTop (m s : ℝ) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun ν : Ioi (0 : ℝ) ↦
      ProbabilityMeasure.map
        (⟨studentTMeasure ν, isProbabilityMeasure_studentTMeasure ν.2⟩ :
          ProbabilityMeasure ℝ) (fun x ↦ m + s * x)) atTop
      (nhds (⟨gaussianReal m (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0),
        ProbabilityTheory.instIsProbabilityMeasureGaussianReal m _⟩ :
        ProbabilityMeasure ℝ)) := by
  have hlim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun ν : Ioi (0 : ℝ) ↦
      (⟨studentTMeasure ν, isProbabilityMeasure_studentTMeasure ν.2⟩ :
        ProbabilityMeasure ℝ))
    (⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ)
      tendsto_studentTMeasure_atTop
    (show Continuous (fun x : ℝ ↦ m + s * x) by fun_prop)
  convert hlim using 1
  apply congrArg nhds
  apply ProbabilityMeasure.toMeasure_injective
  change gaussianReal m (⟨s ^ 2, sq_nonneg s⟩ : ℝ≥0) =
    (gaussianReal 0 1).map (fun x ↦ m + s * x)
  rw [gaussianReal_map_const_add_const_mul]
  simp only [mul_zero, add_zero, mul_one]
  congr 1

end TauCeti.Probability
