/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.Levy.Basic

/-!
# The Lévy distribution as an inverse Gaussian square

If `Z` is a standard Gaussian variable and `c > 0`, then `m + c / Z ^ 2` has the Lévy law with
location `m` and scale `c`. The square `Z ^ 2` is chi-squared with one degree of freedom, that
is, Gamma with shape and rate `1 / 2`; its inverse is therefore inverse-gamma with shape and
scale `1 / 2`, and scaling by `c` and translating by `m` give the Lévy law.

## Main declarations

* `TauCeti.Probability.gaussianReal_map_add_div_sq` — the measure-level construction;
* `ProbabilityTheory.HasLaw.add_div_sq_gaussianReal` — its random-variable form.

## References

* J. P. Nolan, *Univariate Stable Distributions*, Springer (2020), chapter 1.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {m c : ℝ}

/-- **The Lévy law from a standard Gaussian.** The image of the standard Gaussian law under
`z ↦ m + c / z ^ 2` is the Lévy law with location `m` and scale `c > 0`. -/
theorem gaussianReal_map_add_div_sq (hc : 0 < c) (m : ℝ) :
    (gaussianReal 0 1).map (fun z ↦ m + c / z ^ 2) = levyMeasure m c := by
  have hcomp : (fun z : ℝ ↦ m + c / z ^ 2) = (m + ·) ∘ (c * ·) ∘ Inv.inv ∘ (· ^ 2) := by
    ext z
    simp [div_eq_mul_inv]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_sq,
    chiSquaredMeasure_eq_gammaMeasure one_pos,
    ← inverseGammaMeasure_of_pos one_half_pos one_half_pos,
    inverseGammaMeasure_map_const_mul hc, ← div_eq_mul_one_div, levyMeasure_def]

end Probability

end TauCeti

namespace ProbabilityTheory.HasLaw

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ} {c : ℝ}

/-- If `Z` is standard Gaussian and `c > 0`, then `m + c / Z ^ 2` has the Lévy law with location
`m` and scale `c`. -/
theorem add_div_sq_gaussianReal (hZ : HasLaw Z (gaussianReal 0 1) P) (hc : 0 < c) (m : ℝ) :
    HasLaw (fun ω ↦ m + c / Z ω ^ 2) (TauCeti.Probability.levyMeasure m c) P :=
  (HasLaw.mk (by fun_prop) (TauCeti.Probability.gaussianReal_map_add_div_sq hc m)).fun_comp hZ

end ProbabilityTheory.HasLaw
