/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace

/-!
# Bessel-potential spaces as spaces of tempered distributions

An element `u` of Mathlib's Bessel-potential space `H^{s,p}(E, F)` is a tempered distribution
`u.toDistr`, namely `J^{-s} f` for its `Lᵖ` function `f`. This file bundles this inclusion as a
continuous linear map, so that the spaces `H^{s,p}` for different `s` can be compared inside
`𝓢'(E, F)`, for example as compatible couples for interpolation.

## Main declarations

* `BesselPotentialSpace.toDistrCLM`: the inclusion `H^{s,p}(E, F) →L[ℂ] 𝓢'(E, F)`.
* `BesselPotentialSpace.toDistrCLM_injective`: it is injective.
-/

public section

noncomputable section

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BesselPotentialSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

namespace BesselPotentialSpace

variable (E F) in
/-- The inclusion of the Bessel-potential space `H^{s,p}` into the tempered distributions, as a
continuous linear map: an element is the tempered distribution `J^{-s} f` of its `Lᵖ`
function `f`. -/
def toDistrCLM (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)] : H^{s, p}(E, F) →L[ℂ] 𝓢'(E, F) :=
  besselPotential E F (-s) ∘L Lp.toTemperedDistributionCLM F volume p ∘L
    (toLpₗᵢ E F s p).toContinuousLinearEquiv.toContinuousLinearMap

@[simp]
theorem toDistrCLM_apply {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{s, p}(E, F)) :
    toDistrCLM E F s p u = u.toDistr := by
  simp [toDistrCLM]

theorem toDistrCLM_injective {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] :
    Function.Injective (toDistrCLM E F s p) := fun u v h ↦
  ext (by simpa using h)

end BesselPotentialSpace
