/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Masses of the marginals of a measure on a finite product

For a measure `π` on `α × β` with measurable singletons, the mass that the first marginal
`π.map Prod.fst` gives to a point `x` is the sum of the masses of the points `(x, y)` of the row
over `x`, when `β` is finite, and symmetrically for the second marginal. Mathlib records this for
the extended masses (`MeasureTheory.measure_preimage_fst_singleton_eq_sum`); this file states it
for the real masses `Measure.real`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] [MeasurableSpace β]
  [MeasurableSingletonClass β] {π : Measure (α × β)}

/-- The real mass of a point under the first marginal of a measure on `α × β`, with `β` finite, is
the sum of the real masses of the points of its row. -/
theorem map_fst_real_singleton [Fintype β] (x : α)
    (h : ∀ y, π {(x, y)} ≠ ∞ := by finiteness) :
    (π.map Prod.fst).real {x} = ∑ y, π.real {(x, y)} := by
  rw [map_measureReal_apply measurable_fst (measurableSet_singleton x), measureReal_def,
    measure_preimage_fst_singleton_eq_sum, ENNReal.toReal_sum fun y _ ↦ h y]
  rfl

/-- The real mass of a point under the second marginal of a measure on `α × β`, with `α` finite,
is the sum of the real masses of the points of its column. -/
theorem map_snd_real_singleton [Fintype α] (y : β)
    (h : ∀ x, π {(x, y)} ≠ ∞ := by finiteness) :
    (π.map Prod.snd).real {y} = ∑ x, π.real {(x, y)} := by
  rw [map_measureReal_apply measurable_snd (measurableSet_singleton y), measureReal_def,
    measure_preimage_snd_singleton_eq_sum, ENNReal.toReal_sum fun x _ ↦ h x]
  rfl

end MeasureTheory.Measure
