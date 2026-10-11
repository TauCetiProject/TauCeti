/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.Lebesgue

/-!
# The Radon–Nikodym derivative at an atom

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

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] {μ ν : Measure α} {x : α}

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
