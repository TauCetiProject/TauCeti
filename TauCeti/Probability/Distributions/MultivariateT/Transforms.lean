/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateT.Marginal
public import TauCeti.Probability.Distributions.StudentT.Moments

/-!
# Exponential integrability of multivariate t laws

A linear projection of a multivariate t vector has finite exponential moments at every real
rate if its directional scale is zero, and only at rate zero otherwise. In particular, singular
scale matrices can have both constant projections and projections with polynomial tails. The
location and the positive number of degrees of freedom do not affect this distinction.

The results use `map_inner_multivariateTMeasure`, the exact scalar Student t domain
`integrableExpSet_id_studentTMeasure`, and affine transport of exponential integrability.
They apply to the measure itself and to random vectors with that law.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : Matrix ι ι ℝ} {ν : ℝ}

/-- A directional exponential moment of a multivariate t law is finite exactly when the rate
or the directional scale is zero. This includes singular and zero scale matrices. -/
@[simp]
theorem integrable_exp_mul_inner_multivariateTMeasure_iff (m θ : EuclideanSpace ℝ ι)
    (hν : 0 < ν) (hS : S.PosSemidef) (t : ℝ) :
    Integrable (fun x ↦ Real.exp (t * ⟪θ, x⟫)) (multivariateTMeasure m S ν) ↔
      t = 0 ∨ ⟪θ, S.toEuclideanLin θ⟫ = 0 := by
  have hnonneg := (Matrix.isPositive_toEuclideanLin_iff.mpr hS).inner_nonneg_right θ
  have hdomain := integrableExpSet_id_map_affine (μ := studentTMeasure ν)
    (a := ⟪θ, m⟫) (b := √⟪θ, S.toEuclideanLin θ⟫)
  rw [integrableExpSet_id_studentTMeasure hν] at hdomain
  have hmap := integrable_map_measure (μ := multivariateTMeasure m S ν)
    (f := fun x : EuclideanSpace ℝ ι ↦ ⟪θ, x⟫)
    (g := fun y : ℝ ↦ Real.exp (t * y)) (by fun_prop) (by fun_prop)
  simp only [Function.comp_def] at hmap
  rw [← hmap, map_inner_multivariateTMeasure m θ hS ν]
  simpa only [integrableExpSet, mem_ofPred_eq, id_eq, mem_preimage, mem_singleton_iff,
    mul_eq_zero, Real.sqrt_eq_zero hnonneg, or_comm] using
    Set.ext_iff.mp hdomain t

/-- The exact exponential-integrability domain of a linear projection of a multivariate t law:
all real rates for zero directional scale, and only zero for positive directional scale. -/
theorem integrableExpSet_inner_multivariateTMeasure (m θ : EuclideanSpace ℝ ι)
    (hν : 0 < ν) (hS : S.PosSemidef) :
    integrableExpSet (fun x ↦ ⟪θ, x⟫) (multivariateTMeasure m S ν) =
      if ⟪θ, S.toEuclideanLin θ⟫ = 0 then univ else {0} := by
  ext t
  by_cases h : ⟪θ, S.toEuclideanLin θ⟫ = 0 <;>
    simp [integrableExpSet, integrable_exp_mul_inner_multivariateTMeasure_iff m θ hν hS, h]

/-- A random vector with a multivariate t law has a finite directional exponential moment
exactly when the rate or the directional scale is zero. -/
theorem integrable_exp_mul_inner_of_hasLaw_multivariateTMeasure_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → EuclideanSpace ℝ ι}
    {m : EuclideanSpace ℝ ι} (hν : 0 < ν) (hS : S.PosSemidef)
    (hX : HasLaw X (multivariateTMeasure m S ν) P) (θ : EuclideanSpace ℝ ι) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * ⟪θ, X ω⟫)) P ↔
      t = 0 ∨ ⟪θ, S.toEuclideanLin θ⟫ = 0 := by
  have h := integrable_exp_mul_inner_multivariateTMeasure_iff m θ hν hS t
  rwa [← hX.map_eq, integrable_map_measure (by fun_prop) hX.aemeasurable] at h

end TauCeti.Probability
