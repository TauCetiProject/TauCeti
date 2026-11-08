/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Almost-everywhere vanishing outside the topological support

If the topological support `tsupport f` of a function `f : α → β` is contained in a set `s`, then
`f` vanishes everywhere on the open set `(tsupport f)ᶜ`, which contains `sᶜ` and is measurable in
any `OpensMeasurableSpace`. Consequently `f =ᵐ[μ.restrict sᶜ] 0` without any measurability
assumption on `s` or `f`.

The file also records the total mass of a rescaled restriction.

## Main results

* `MeasureTheory.Measure.smul_restrict_univ`: `(s • μ.restrict A) univ = s * μ A`.
* `MeasureTheory.ae_restrict_compl_eq_zero_of_tsupport_subset`: if `tsupport f ⊆ s`, then
  `f =ᵐ[μ.restrict sᶜ] 0`.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

/-- A function whose topological support lies in `s` vanishes almost everywhere on `sᶜ`. -/
theorem ae_restrict_compl_eq_zero_of_tsupport_subset {α β : Type*} [MeasurableSpace α]
    [TopologicalSpace α] [OpensMeasurableSpace α] [Zero β] {μ : Measure α} {s : Set α}
    {f : α → β} (hf : tsupport f ⊆ s) : f =ᵐ[μ.restrict sᶜ] 0 :=
  ae_restrict_of_ae_restrict_of_subset (compl_subset_compl.2 hf) <|
    ae_restrict_of_forall_mem (isClosed_tsupport f).isOpen_compl.measurableSet fun _ hx ↦
      image_eq_zero_of_notMem_tsupport hx

namespace Measure

/-- The total mass of the restriction to `A` of a measure, rescaled by `s`. -/
theorem smul_restrict_univ {α : Type*} [MeasurableSpace α] (s : ℝ≥0∞) (μ : Measure α)
    (A : Set α) : (s • μ.restrict A) univ = s * μ A := by
  simp only [_root_.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul]

end Measure

end MeasureTheory
