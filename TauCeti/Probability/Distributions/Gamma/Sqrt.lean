/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Real
public import TauCeti.MeasureTheory.Measure.WithDensity
public import TauCeti.Probability.Distributions.ChiSquared
public import TauCeti.Probability.Distributions.Gamma.Basic

/-!
# Square roots of gamma variables

A positive variable whose square is gamma has a density of its own: substituting `x = t ^ 2` in
the gamma density and multiplying by the Jacobian `2 * t` turns
`r ^ a / Γ a * x ^ (a - 1) * exp (-(r * x))` into
`2 * r ^ a / Γ a * t ^ (2 * a - 1) * exp (-(r * t ^ 2))` on the positive half-line. This file
proves that correspondence in both directions: squaring carries the latter law to `gammaMeasure`,
and taking square roots carries `gammaMeasure` back.

At shape `k / 2` and rate `1 / 2` the source law is the chi law with `k` degrees of freedom, whose
density is `2 ^ (1 - k / 2) / Γ (k / 2) * t ^ (k - 1) * exp (-t ^ 2 / 2)`, and the target law is
`TauCeti.Probability.chiSquaredMeasure k`. That is the shape in which a triangular factorisation
meets a chi-squared law: the diagonal entries of a Cholesky factor carry the chi density directly,
and it is their squares that are chi-squared.

## Main results

* `TauCeti.map_sq_withDensity_eq_gammaMeasure` — squaring sends the root-gamma law to
  `gammaMeasure a r`;
* `TauCeti.map_sqrt_gammaMeasure` — the inverse correspondence, the image of `gammaMeasure a r`
  under `Real.sqrt`;
* `TauCeti.Probability.map_sq_withDensity_eq_chiSquaredMeasure` and
  `TauCeti.Probability.map_sqrt_chiSquaredMeasure` — the same pair for the chi and chi-squared
  laws;
* `TauCeti.isProbabilityMeasure_withDensity_rootGamma` and
  `TauCeti.Probability.isProbabilityMeasure_withDensity_chi` — both source laws are normalised.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley, 1994, ch. 18 (the chi distribution) and ch. 17 (the gamma family).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

open scoped ENNReal

namespace TauCeti

variable {a r : ℝ}

/-- **The square of a root-gamma variable is gamma.** On the positive half-line the density
`2 * r ^ a / Γ a * t ^ (2 * a - 1) * exp (-(r * t ^ 2))` is carried by squaring to the gamma law
of shape `a` and rate `r`. -/
theorem map_sq_withDensity_eq_gammaMeasure (a r : ℝ) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
        (2 * r ^ a / Real.Gamma a * t ^ (2 * a - 1) * exp (-(r * t ^ 2)))).map (fun t ↦ t ^ 2) =
      gammaMeasure a r := by
  rw [gammaMeasure_eq_withDensity_restrict_Ioi,
    ← MeasureTheory.map_sq_withDensity_restrict_Ioi (gammaPDF a r)]
  refine congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht' : (0 : ℝ) < t := ht
  rw [gammaPDF_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hsq : (t ^ 2) ^ (a - 1) = t ^ (2 * a - 2) := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_mul ht'.le]
    congr 1
    push_cast
    ring
  have hsplit : t ^ (2 * a - 1) = t ^ (2 * a - 2) * t := by
    rw [show (2 * a - 1 : ℝ) = 2 * a - 2 + 1 by ring, Real.rpow_add_one ht'.ne']
  rw [hsq, hsplit]
  ring

/-- **The square root of a gamma variable has the root-gamma density.** This inverts
`TauCeti.map_sq_withDensity_eq_gammaMeasure`. -/
theorem map_sqrt_gammaMeasure (a r : ℝ) :
    (gammaMeasure a r).map Real.sqrt =
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
        (2 * r ^ a / Real.Gamma a * t ^ (2 * a - 1) * exp (-(r * t ^ 2))) := by
  rw [← map_sq_withDensity_eq_gammaMeasure a r]
  refine Measure.map_sqrt_map_sq _ ?_
  have hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hae] with t ht using le_of_lt ht

/-- **The root-gamma density is normalised**: for a positive shape and rate it carries total mass
one, which is what makes the constant `2 * r ^ a / Γ a` the right one. -/
theorem isProbabilityMeasure_withDensity_rootGamma (ha : 0 < a) (hr : 0 < r) :
    IsProbabilityMeasure ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
      (2 * r ^ a / Real.Gamma a * t ^ (2 * a - 1) * exp (-(r * t ^ 2)))) := by
  have _ : IsProbabilityMeasure (gammaMeasure a r) := isProbabilityMeasure_gammaMeasure ha hr
  refine ⟨?_⟩
  rw [← Set.preimage_univ (f := fun t : ℝ ↦ t ^ 2),
    ← Measure.map_apply (by fun_prop) MeasurableSet.univ,
    map_sq_withDensity_eq_gammaMeasure a r, measure_univ]

namespace Probability

variable {k : ℝ}

/-- **The square of a chi variable is chi-squared.** On the positive half-line the chi density
`2 ^ (1 - k / 2) / Γ (k / 2) * t ^ (k - 1) * exp (-t ^ 2 / 2)` is carried by squaring to the
chi-squared law with `k` degrees of freedom. -/
theorem map_sq_withDensity_eq_chiSquaredMeasure (hk : 0 < k) :
    ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
        ((2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) * t ^ (k - 1) * exp (-t ^ 2 / 2))).map
      (fun t ↦ t ^ 2) = chiSquaredMeasure k := by
  rw [chiSquaredMeasure_eq_gammaMeasure hk,
    ← map_sq_withDensity_eq_gammaMeasure (k / 2) (1 / 2)]
  refine congrArg (Measure.map _) (withDensity_congr_ae ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
  congr 1
  have hrate : (2 : ℝ) * (1 / 2) ^ (k / 2) = (2 : ℝ) ^ (1 - k / 2) := by
    rw [Real.div_rpow zero_le_one (by norm_num), Real.one_rpow,
      Real.rpow_sub (by norm_num), Real.rpow_one]
    ring
  rw [← hrate]
  ring_nf

/-- **The square root of a chi-squared variable has the chi density.** This inverts
`TauCeti.Probability.map_sq_withDensity_eq_chiSquaredMeasure`. -/
theorem map_sqrt_chiSquaredMeasure (hk : 0 < k) :
    (chiSquaredMeasure k).map Real.sqrt =
      (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
        ((2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) * t ^ (k - 1) * exp (-t ^ 2 / 2)) := by
  rw [← map_sq_withDensity_eq_chiSquaredMeasure hk]
  refine Measure.map_sqrt_map_sq _ ?_
  have hae : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), t ∈ Ioi (0 : ℝ) :=
    ae_restrict_mem measurableSet_Ioi
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le hae] with t ht using le_of_lt ht

/-- **The chi density is normalised**: for positive degrees of freedom it carries total mass one,
which is what makes the constant `2 ^ (1 - k / 2) / Γ (k / 2)` the right one. -/
theorem isProbabilityMeasure_withDensity_chi (hk : 0 < k) :
    IsProbabilityMeasure ((volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal
      ((2 : ℝ) ^ (1 - k / 2) / Real.Gamma (k / 2) * t ^ (k - 1) * exp (-t ^ 2 / 2))) := by
  have _ : IsProbabilityMeasure (chiSquaredMeasure k) :=
    isProbabilityMeasure_chiSquaredMeasure hk.le
  refine ⟨?_⟩
  rw [← Set.preimage_univ (f := fun t : ℝ ↦ t ^ 2),
    ← Measure.map_apply (by fun_prop) MeasurableSet.univ,
    map_sq_withDensity_eq_chiSquaredMeasure hk, measure_univ]

end Probability

end TauCeti
