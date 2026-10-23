/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Levy.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import TauCeti.Probability.Distributions.Gaussian.ChiSquared

/-!
# The Gaussian construction of the Lévy distribution

If `Z` is a standard Gaussian variable, then `m + c / Z ^ 2` has the Lévy law with location `m`
and scale `c > 0`. The square `Z ^ 2` is chi-squared with one degree of freedom, that is, Gamma
with shape and rate `1 / 2` (`gaussianReal_map_sq`), so `1 / Z ^ 2` is inverse-gamma with shape
and scale `1 / 2`, which is the standard Lévy law; positive affine transport then gives the
general case. The value of `c / Z ^ 2` at `Z = 0` is irrelevant, since that event is null.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

namespace TauCeti

namespace Probability

variable {m c : ℝ}

/-- **The Gaussian construction of the Lévy law.** If `Z` is standard Gaussian and `c > 0`, then
`m + c / Z ^ 2` has the Lévy law with location `m` and scale `c`. -/
theorem gaussianReal_map_add_div_sq (hc : 0 < c) (m : ℝ) :
    (gaussianReal 0 1).map (fun z ↦ m + c / z ^ 2) = levyMeasure m c := by
  have hfun : (fun z : ℝ ↦ m + c / z ^ 2) =
      (fun x ↦ m + c * x) ∘ Inv.inv ∘ fun z : ℝ ↦ z ^ 2 := by
    funext z
    simp [div_eq_mul_inv]
  have hstd : (chiSquaredMeasure 1).map Inv.inv = levyMeasure 0 1 := by
    rw [chiSquaredMeasure_eq_gammaMeasure one_pos, levyMeasure_zero_left,
      inverseGammaMeasure_of_pos one_half_pos one_half_pos]
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map measurable_inv (by fun_prop), gaussianReal_map_sq, hstd,
    ← levyMeasure_eq_map_affine_levyMeasure_zero_one hc]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}

/-- The random-variable form of the Gaussian construction: if `Z` is standard Gaussian and
`c > 0`, then `m + c / Z ^ 2` has the Lévy law with location `m` and scale `c`. -/
theorem hasLaw_levyMeasure_of_hasLaw_gaussianReal (hc : 0 < c) (m : ℝ)
    (hZ : HasLaw Z (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ m + c / Z ω ^ 2) (levyMeasure m c) P :=
  (HasLaw.mk (by fun_prop) (gaussianReal_map_add_div_sq hc m)).comp hZ

end Probability

end TauCeti
