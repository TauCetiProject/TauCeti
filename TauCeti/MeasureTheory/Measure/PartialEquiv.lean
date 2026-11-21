/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Equiv.PartialEquiv
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Null images under partial equivalences

For a partial equivalence `e : PartialEquiv α β` and a measure `μ` on `β`, the image under `e` of
the points of its source where a property fails is `μ`-null exactly when the property holds at the
preimage of `μ`-almost every point of the target. This reads almost-everywhere statements through
charts.

## Main results

* `PartialEquiv.measure_image_setOf_not_inter_source_eq_zero_iff`: the image of the failure set is
  null if and only if the property holds at `e.symm y` for almost every `y ∈ e.target`.
-/

public section

open MeasureTheory Set

namespace PartialEquiv

/-- The image under `e` of the points of its source where `p` fails is null exactly when `p` holds
at the preimage of almost every point of the target of `e`. -/
theorem measure_image_setOf_not_inter_source_eq_zero_iff {α β : Type*} [MeasurableSpace β]
    (e : PartialEquiv α β) (μ : Measure β) {p : α → Prop} :
    μ (e '' ({x | ¬p x} ∩ e.source)) = 0 ↔ ∀ᵐ y ∂μ, y ∈ e.target → p (e.symm y) := by
  rw [MeasureTheory.ae_iff, inter_comm, PartialEquiv.image_source_inter_eq']
  simp only [inter_def, preimage_ofPred_eq, mem_ofPred_eq, not_imp]

end PartialEquiv
