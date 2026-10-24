/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Marginal masses and sections of product measures

For a measure `π` on `α × β` with measurable singletons, the mass that the first marginal
`π.map Prod.fst` gives to a point `x` is the sum of the masses of the points `(x, y)` of the row
over `x`, when `β` is finite, and symmetrically for the second marginal. Mathlib records this for
the extended masses (`MeasureTheory.measure_preimage_fst_singleton_eq_sum`); this file states it
for the real masses `Measure.real`.

It also records that almost every section of an almost-everywhere measurable function on a
product `μ.prod ν` is almost-everywhere measurable (`AEMeasurable.prodMk_left`), the counterpart of
Mathlib's `MeasureTheory.AEStronglyMeasurable.prodMk_left`.

Finally, for a measurable map `f` into an additive group, the law of `f z.1 - f z.2` under
`μ.prod μ` is symmetric (`MeasureTheory.Measure.map_neg_map_sub_prod_self`): swapping the two
identical factors negates the difference.
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

/-- The law of the difference `f z.1 - f z.2` of two coordinates of a product measure `μ.prod μ`
is symmetric: swapping the two identical factors negates the difference. -/
theorem map_neg_map_sub_prod_self {γ G : Type*} [MeasurableSpace γ] [MeasurableSpace G]
    [AddGroup G] [MeasurableNeg G] [MeasurableSub₂ G] (μ : Measure γ) [SFinite μ] {f : γ → G}
    (hf : Measurable f) :
    ((μ.prod μ).map fun z => f z.1 - f z.2).map Neg.neg =
      (μ.prod μ).map fun z => f z.1 - f z.2 := by
  rw [map_map measurable_neg (by fun_prop)]
  conv_lhs => rw [← prod_swap]
  rw [map_map (measurable_neg.comp (by fun_prop)) measurable_swap]
  congr 1
  funext z
  simp

end MeasureTheory.Measure

/-- Almost every section of an almost-everywhere measurable function on `μ.prod ν` is
almost-everywhere measurable. This is the counterpart for `AEMeasurable` of
`MeasureTheory.AEStronglyMeasurable.prodMk_left`. -/
theorem AEMeasurable.prodMk_left {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β}
    [MeasureTheory.SFinite ν] {f : α × β → γ} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEMeasurable (fun y ↦ f (x, y)) ν := by
  filter_upwards [MeasureTheory.Measure.ae_ae_of_ae_prod hf.ae_eq_mk] with x hx
  exact ⟨_, hf.measurable_mk.comp measurable_prodMk_left, hx⟩
