/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Affine
public import TauCeti.Probability.Distributions.MultivariateT.Basic
public import TauCeti.Probability.Distributions.StudentT.ChiSquared
import TauCeti.MeasureTheory.Constructions.EuclideanSpace
import TauCeti.Probability.Distributions.Gaussian.Transforms

/-!
# Linear marginals of multivariate t laws

Every real linear functional `x ↦ ⟪θ, x⟫` of a multivariate t vector with location `m`, scale
`S` and `ν` degrees of freedom has the location-scale Student t law with location `⟪θ, m⟫`,
scale `√⟪θ, S θ⟫` and the same degrees of freedom. A zero directional scale gives the point mass
at `⟪θ, m⟫`. In particular the coordinates are location-scale Student t variables, a
one-dimensional multivariate t law is the location-scale Student t law transported to
`EuclideanSpace ℝ ι`, and the lower quantiles of the projections are affine images of Student t
quantiles.

## Main results

* `TauCeti.Probability.map_inner_multivariateTMeasure`: real linear projections are
  location-scale Student t.
* `TauCeti.Probability.map_eval_multivariateTMeasure`: coordinate marginals.
* `TauCeti.Probability.multivariateTMeasure_eq_map_single`: the one-dimensional case.
* `TauCeti.Probability.quantile_multivariateTMeasure_projection`: quantiles of projections.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Linear projections of multivariate t laws.** The projection `x ↦ ⟪θ, x⟫` of a
multivariate t law has the location-scale Student t law with location `⟪θ, m⟫`, scale
`√⟪θ, S θ⟫` and the same degrees of freedom. -/
@[simp]
theorem map_inner_multivariateTMeasure (m θ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (ν : ℝ) :
    (multivariateTMeasure m S ν).map (fun x => ⟪θ, x⟫) =
      (studentTMeasure ν).map fun t => ⟪θ, m⟫ + √⟪θ, S.toEuclideanLin θ⟫ * t := by
  rcases le_or_gt ν 0 with hν | hν
  · rw [multivariateTMeasure_of_nonpos _ _ hν, studentTMeasure_of_nonpos hν, Measure.map_zero,
      Measure.map_zero]
  have := isProbabilityMeasure_chiSquaredMeasure hν.le
  set σ := √⟪θ, S.toEuclideanLin θ⟫
  -- The directional Gaussian factor is a standard Gaussian scaled by `σ`.
  have hG : (multivariateGaussian 0 S).map (fun z => ⟪θ, z⟫) =
      (gaussianReal 0 1).map (σ * ·) := by
    rw [map_inner_multivariateGaussian 0 θ hS, gaussianReal_map_const_mul, mul_zero, mul_one,
      inner_zero_right]
    congr 1
    ext
    simp [σ, Real.sq_sqrt']
  have hinner : Measurable fun z : EuclideanSpace ℝ ι => ⟪θ, z⟫ := by fun_prop
  rw [multivariateTMeasure_of_posSemidef m hν hS, ← map_div_sqrt_chiSquaredMeasure hν,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  -- Project the Gaussian factor before mixing over the chi-squared factor.
  have hprod : ((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)).map
        (Prod.map (fun z => ⟪θ, z⟫) id) =
      ((gaussianReal 0 1).prod (chiSquaredMeasure ν)).map (Prod.map (σ * ·) id) := by
    rw [← Measure.map_prod_map _ _ hinner measurable_id, hG,
      Measure.map_prod_map _ _ (by fun_prop) measurable_id]
  calc ((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)).map
        ((fun x => ⟪θ, x⟫) ∘ fun z => m + √(ν / z.2) • z.1)
      = (((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)).map
          (Prod.map (fun z => ⟪θ, z⟫) id)).map (fun w => ⟪θ, m⟫ + √(ν / w.2) * w.1) := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        funext z
        simp [inner_add_right, inner_smul_right]
    _ = _ := by
        rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)]
        congr 1
        funext w
        dsimp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
        rw [div_eq_mul_inv w.1, ← Real.sqrt_inv, inv_div]
        ring

/-- **Coordinates of multivariate t laws.** The `i`-th coordinate of a multivariate t vector has
the location-scale Student t law with location `m i`, scale `√(S i i)` and the same degrees of
freedom. -/
theorem map_eval_multivariateTMeasure (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (ν : ℝ) (i : ι) :
    (multivariateTMeasure m S ν).map (fun x => x i) =
      (studentTMeasure ν).map fun t => m i + √(S i i) * t := by
  simpa [EuclideanSpace.inner_single_left] using
    map_inner_multivariateTMeasure m (EuclideanSpace.single i 1) hS ν

/-- A one-dimensional multivariate t law is the location-scale Student t law with location
`m default` and scale `√(S default default)`, transported to `EuclideanSpace ℝ ι`. -/
theorem multivariateTMeasure_eq_map_single [Unique ι] (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (ν : ℝ) :
    multivariateTMeasure m S ν =
      ((studentTMeasure ν).map fun t => m default + √(S default default) * t).map
        (EuclideanSpace.single default) := by
  rw [← map_eval_multivariateTMeasure m hS ν default, EuclideanSpace.map_single_map_eval]

/-- **Quantiles of linear projections of multivariate t laws.** For `0 < u < 1`, the lower
quantile of `x ↦ ⟪θ, x⟫` is `⟪θ, m⟫ + √⟪θ, S θ⟫ * q`, where `q` is the lower quantile of the
standard Student t law with the same degrees of freedom. This includes a zero directional
scale. -/
theorem quantile_multivariateTMeasure_projection (m θ : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) {ν u : ℝ} (hν : 0 < ν) (hu : u ∈ Set.Ioo 0 1) :
    ((multivariateTMeasure m S ν).map (fun x => ⟪θ, x⟫)).quantile u =
      ⟪θ, m⟫ + √⟪θ, S.toEuclideanLin θ⟫ * (studentTMeasure ν).quantile u := by
  have := isProbabilityMeasure_studentTMeasure hν
  rw [map_inner_multivariateTMeasure m θ hS ν, quantile_map_affine hu.1 hu.2]
  rcases (Real.sqrt_nonneg ⟪θ, S.toEuclideanLin θ⟫).lt_or_eq with hσ | hσ
  · simp only [hσ, ↓reduceIte]
  · simp [← hσ]

end TauCeti.Probability
