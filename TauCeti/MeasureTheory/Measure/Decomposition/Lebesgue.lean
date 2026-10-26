/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# The Radon–Nikodym derivative on null sets and at atoms

On a `μ`-null set `s`, the Radon–Nikodym derivative `μ.rnDeriv ν` vanishes `ν`-almost everywhere
(`MeasureTheory.Measure.ae_rnDeriv_eq_zero_of_measure_eq_zero`): its integral over a measurable
hull of `s` is at most `μ s = 0`.

The Radon–Nikodym derivative `μ.rnDeriv ν` is a fixed representative of an almost-everywhere
defined density, so in general its value at a single point carries no information. At a point
`x` with measurable singleton and `ν {x} ≠ 0`, it does: the singular part of `μ` with respect to
`ν` cannot charge `{x}`, and so `μ.rnDeriv ν x * ν {x} = μ {x}`. On a countable space with
measurable singletons every point of positive `ν`-mass is such an atom, and the derivative is the
ratio of the masses there.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α}

/-- The Radon–Nikodym derivative of `μ` with respect to `ν` vanishes `ν`-almost everywhere on a
`μ`-null set. -/
theorem ae_rnDeriv_eq_zero_of_measure_eq_zero {s : Set α} (hs : μ s = 0) :
    ∀ᵐ x ∂ν, x ∈ s → μ.rnDeriv ν x = 0 := by
  have h : ∫⁻ x in toMeasurable μ s, μ.rnDeriv ν x ∂ν = 0 :=
    le_antisymm ((withDensity_apply_le _ _).trans <|
      (le_iff'.1 (withDensity_rnDeriv_le μ ν) _).trans (by rw [measure_toMeasurable, hs])) zero_le
  rw [lintegral_eq_zero_iff (measurable_rnDeriv μ ν)] at h
  exact ((ae_restrict_iff' (measurableSet_toMeasurable μ s)).1 h).mono fun x hx hxs ↦
    hx (subset_toMeasurable μ s hxs)

variable [MeasurableSingletonClass α] {x : α}

/-- At an atom `x` of `ν`, the Radon–Nikodym derivative of `μ` with respect to `ν`, weighted by the
mass of the atom, is the `μ`-mass of `x`: the singular part of `μ` does not charge `{x}`. -/
theorem rnDeriv_mul_measure_singleton [μ.HaveLebesgueDecomposition ν] (hx : ν {x} ≠ 0) :
    μ.rnDeriv ν x * ν {x} = μ {x} := by
  have hsing : μ.singularPart ν {x} = 0 := by
    have hs := mutuallySingular_singularPart μ ν
    by_cases hxs : x ∈ hs.nullSet
    · exact measure_mono_null (Set.singleton_subset_iff.2 hxs) hs.measure_nullSet
    · exact absurd (measure_mono_null (Set.singleton_subset_iff.2 hxs) hs.measure_compl_nullSet)
        hx
  conv_rhs => rw [haveLebesgueDecomposition_add μ ν]
  rw [add_apply, hsing, zero_add, withDensity_apply _ (measurableSet_singleton x),
    lintegral_singleton]

/-- At an atom `x` of finite positive `ν`-mass, the Radon–Nikodym derivative of `μ` with respect to
`ν` is the ratio `μ {x} / ν {x}` of the masses. -/
theorem rnDeriv_eq_measure_singleton_div [μ.HaveLebesgueDecomposition ν] (hx : ν {x} ≠ 0)
    (hx' : ν {x} ≠ ∞) : μ.rnDeriv ν x = μ {x} / ν {x} := by
  rw [ENNReal.eq_div_iff hx hx', mul_comm, rnDeriv_mul_measure_singleton hx]

end MeasureTheory.Measure
