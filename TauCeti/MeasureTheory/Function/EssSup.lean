/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.EssSup
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Topology.Semicontinuity.Basic

/-!
# Essential suprema on the support of a measure

For a nonnegative extended-valued lower semicontinuous function, its essential supremum is
its pointwise supremum on the support, provided that support is conull. In particular this
holds on hereditarily Lindelöf spaces, without a finiteness assumption on the measure.

This identifies essential bounds on continuous observables, such as distance from a fixed
point, with geometric bounds on the support. Lower semicontinuity is important: an upward
change at a single null point need not affect the essential supremum.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] {μ : Measure X}

/-- The essential supremum of a lower semicontinuous nonnegative extended-valued function
is its supremum on the support, whenever the support is conull. -/
theorem essSup_eq_iSup_support (f : X → ℝ≥0∞)
    (hf : LowerSemicontinuous f) (hμ : μ.support ∈ ae μ) :
    essSup f μ = ⨆ x ∈ μ.support, f x := by
  apply le_antisymm
  · exact essSup_le_of_ae_le _ (by
      filter_upwards [hμ] with x hx
      exact le_iSup₂_of_le x hx le_rfl)
  · have hsub := μ.support_subset_of_isClosed (hf.isClosed_preimage (essSup f μ))
      (ENNReal.ae_le_essSup f)
    exact iSup₂_le fun x hx ↦ hsub hx

end TauCeti
