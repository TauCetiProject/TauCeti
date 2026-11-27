/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi
public import TauCeti.Analysis.BoundedVariation.ReducedBoundary.Ball
import TauCeti.Analysis.BoundedVariation.Ball
import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# De Giorgi's structure theorem on a ball

De Giorgi's structure theorem worked out for a ball `B = ball c r` with `r > 0` in a real inner
product space of dimension `n ≥ 2`. The reduced boundary of `B` is the sphere
(`TauCeti.reducedBoundary_ball`), with outer normal `(x − c) / r` (`TauCeti.outerNormal_ball`), so:

* the perimeter measure is Hausdorff measure on the sphere, `|Dχ_B| = Hⁿ⁻¹⌊sphere c r`
  (`variationMeasure_indicator_ball`);
* `Dχ_B = −((x − c) / r) Hⁿ⁻¹⌊sphere c r`, in the form of the Gauss–Green formula
  `∫_B div φ = ∫_{sphere c r} ⟪φ, (x − c) / r⟫ dHⁿ⁻¹`
  (`integral_trace_fderiv_mul_indicator_ball_eq_setIntegral_inner`);
* `P(B) = Hⁿ⁻¹(sphere c r)` (`perimeter_ball_eq_euclideanHausdorffMeasure_sphere`), which is
  `n ω_n r ^ (n − 1)` by `TauCeti.euclideanHausdorffMeasure_sphere`, where `ω_n` is the volume of
  the unit ball. The closing example checks that this agrees with `TauCeti.perimeter_ball`.
-/

open MeasureTheory Metric Module Set TopologicalSpace
open scoped ENNReal RealInnerProductSpace

public noncomputable section

namespace TauCeti.Examples.DeGiorgiBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {c : E} {r : ℝ}

/-- **The perimeter measure of a ball is Hausdorff measure on its sphere**,
`|Dχ_B| = Hⁿ⁻¹⌊sphere c r`, as measures on the whole space viewed as the open set `⊤`. -/
theorem variationMeasure_indicator_ball (hn : 2 ≤ finrank ℝ E) (hr : 0 < r) :
    variationMeasure volume (⊤ : Opens E) ((ball c r).indicator 1) =
      (μHE[finrank ℝ E - 1].restrict (sphere c r)).comap (↑) := by
  rw [variationMeasure_eq_comap_restrict_reducedBoundary hn, reducedBoundary_ball hr]

/-- **`Dχ_B = −((x − c) / r) Hⁿ⁻¹⌊sphere c r`**: for every compactly supported `C¹` vector field
`φ`, `∫_B div φ = ∫_{sphere c r} ⟪φ, (x − c) / r⟫ dHⁿ⁻¹`. -/
theorem integral_trace_fderiv_mul_indicator_ball_eq_setIntegral_inner (hn : 2 ≤ finrank ℝ E)
    (hr : 0 < r) {φ : E → E} (hφ : ContDiff ℝ 1 φ) (hc : HasCompactSupport φ) :
    ∫ x, LinearMap.trace ℝ E (fderiv ℝ φ x : E →ₗ[ℝ] E) * (ball c r).indicator 1 x =
      ∫ x in sphere c r, ⟪φ x, r⁻¹ • (x - c)⟫ ∂μHE[finrank ℝ E - 1] := by
  rw [integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hn
    (locallyIntegrableOn_indicator_const measurableSet_ball.nullMeasurableSet 1)
    forall_isCompact_exists_totalVariationOn_indicator_ball_ne_top
    hφ hc (by simp), reducedBoundary_ball hr]
  exact setIntegral_congr_fun isClosed_sphere.measurableSet fun x hx => by
    rw [outerNormal_ball hr hx]

/-- **The perimeter of a ball is the area of its sphere**: `P(B) = Hⁿ⁻¹(sphere c r)`. By
`TauCeti.euclideanHausdorffMeasure_sphere` both are `n ω_n r ^ (n − 1)`. -/
theorem perimeter_ball_eq_euclideanHausdorffMeasure_sphere (hn : 2 ≤ finrank ℝ E)
    (hr : 0 < r) :
    perimeter volume ⊤ (ball c r) = μHE[finrank ℝ E - 1] (sphere c r) := by
  rw [perimeter_eq_euclideanHausdorffMeasure_reducedBoundary hn
    (locallyIntegrableOn_indicator_const measurableSet_ball.nullMeasurableSet 1)
    forall_isCompact_exists_totalVariationOn_indicator_ball_ne_top,
    reducedBoundary_ball hr]

/-- The two formulas agree: `TauCeti.perimeter_ball` computes the same perimeter as
`n r ^ (n − 1) ω_n`. -/
example (hn : 2 ≤ finrank ℝ E) (hr : 0 < r) :
    finrank ℝ E * ENNReal.ofReal (r ^ (finrank ℝ E - 1)) * volume (ball (0 : E) 1) =
      μHE[finrank ℝ E - 1] (sphere c r) := by
  rw [← perimeter_ball hr, perimeter_ball_eq_euclideanHausdorffMeasure_sphere hn hr]

end TauCeti.Examples.DeGiorgiBall
