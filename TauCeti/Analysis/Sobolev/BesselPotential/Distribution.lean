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
* `BesselPotentialSpace.norm_copy`, `BesselPotentialSpace.memSobolev_toDistr_of_eq`: moving an
  element along an equality of orders `s = s'`.
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

/-- Transferring an element of `H^{s,p}` to `H^{s',p}` along `s = s'` keeps its norm. -/
@[simp]
theorem norm_copy {s s' : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{s, p}(E, F)) (hs : s = s') :
    ‖u.copy s' hs‖ = ‖u‖ := by
  rw [← norm_toLp_eq, toLp_copy _ hs, norm_toLp_eq]

/-- The tempered distribution of an element of `H^{t,p}` lies in `H^{s,p}` when `t = s`. -/
theorem memSobolev_toDistr_of_eq {s t : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : H^{t, p}(E, F))
    (h : t = s) : MemSobolev s p u.toDistr :=
  h ▸ u.memSobolev_toDistr

end BesselPotentialSpace
