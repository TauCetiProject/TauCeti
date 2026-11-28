/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.Topology.EMetricSpace.Weak
public import TauCeti.Order.Interval.Set.RealGrid

/-!
# Measurability of extended distances and uniform real grids

## Extended distance on `ℝ≥0∞`

`ℝ≥0∞` carries the extended distance `edist a b = max (a - b) (b - a)` of a weak extended metric
space, which is not jointly continuous for the order topology, so Mathlib's `measurable_edist`
does not apply to it. The distance is nevertheless Borel measurable, because truncated
subtraction is. This lets the Wasserstein distance be used for laws on `[0, ∞]`, such as the
distribution of an extended-valued random variable.

## Uniform real grids

Each half-open real grid cell is Borel measurable, so it can be used in
measurable decompositions of the real line, including spectral measures.

## Measurable rescaling factors

If a family of measurable functions `J f : X → ℝ≥0∞` changes at each point `y` only by a finite
nonzero factor independent of `f`, these factors can be chosen measurably in `y`
(`MeasureTheory.exists_measurable_mul_eq_of_scale`).

## References

`MeasureTheory.exists_measurable_mul_eq_of_scale` is adapted from grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC),
`src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean` (`New.exists_measurable_mul_eq_of_scale`).
-/

public section

open MeasureTheory
open scoped ENNReal

/-- The extended distance on `ℝ≥0∞` is jointly measurable. -/
@[fun_prop]
theorem ENNReal.measurable_edist : Measurable fun z : ℝ≥0∞ × ℝ≥0∞ ↦ edist z.1 z.2 := by
  simp only [ENNReal.edist_eq_max]
  fun_prop

namespace Real

/-- Each half-open interval cell of a real grid is Borel measurable. -/
@[simp, measurability]
theorem measurableSet_gridCell (ε : ℝ) (k : ℤ) :
    MeasurableSet (gridCell ε k) := by
  rw [gridCell_eq_Ico]
  exact measurableSet_Ico

end Real

namespace MeasureTheory

/-- **Measurable rescaling of a family of functions.** Let `J` send measurable functions
`X → ℝ≥0∞` to measurable functions, and suppose that at each point `y` every `J f y` differs from
`J f x₀` by the same finite nonzero factor `r y` (independent of `f`). Then for every measurable
`β` there is a measurable `g` with `g y * J f y = β y * J f x₀` for all `y` and measurable `f`:
the factors `y ↦ r y` can be chosen measurably. -/
theorem exists_measurable_mul_eq_of_scale {X : Type*} [MeasurableSpace X]
    {J : (X → ℝ≥0∞) → X → ℝ≥0∞} {x₀ : X} (hJ : ∀ f, Measurable f → Measurable (J f))
    (h_scale : ∀ y, ∃ r : ℝ≥0∞, r ≠ 0 ∧ r ≠ ∞ ∧ ∀ f, Measurable f → r * J f y = J f x₀)
    {β : X → ℝ≥0∞} (hβ : Measurable β) :
    ∃ g : X → ℝ≥0∞, Measurable g ∧ ∀ y f, Measurable f → g y * J f y = β y * J f x₀ := by
  by_cases! h_const : ∀ y f, Measurable f → J f y = J f x₀
  · exact ⟨β, hβ, fun y f hf ↦ by rw [h_const y f hf]⟩
  -- Otherwise some `J f` is finite and nonzero everywhere; the factor at `y` is `J f x₀ / J f y`.
  obtain ⟨y₀, f, hf, h_ne⟩ := h_const
  obtain ⟨r, hr_zero, hr_top, hr⟩ := h_scale y₀
  have h_zero : J f x₀ ≠ 0 := fun h ↦ h_ne (by simpa [h, hr_zero] using hr f hf)
  have h_top : J f x₀ ≠ ∞ := fun h ↦
    h_ne (by simpa [h, hr_zero, hr_top, ENNReal.mul_eq_top] using hr f hf)
  refine ⟨fun x ↦ β x * (J f x₀ / J f x), hβ.mul (measurable_const.div (hJ f hf)),
    fun x φ hφ ↦ ?_⟩
  obtain ⟨s, hs_zero, -, hs⟩ := h_scale x
  have hx_zero : J f x ≠ 0 := fun h ↦ h_zero (by rw [← hs f hf, h, mul_zero])
  have hx_top : J f x ≠ ∞ := fun h ↦ h_top (by rw [← hs f hf, h, ENNReal.mul_top hs_zero])
  have h_div : J f x₀ / J f x = s := by
    rw [← hs f hf, ENNReal.mul_div_cancel_right hx_zero hx_top]
  simp only [h_div, mul_assoc, hs φ hφ]

end MeasureTheory
