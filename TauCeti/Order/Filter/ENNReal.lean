/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.ENNReal

/-!
# Subadditivity of the upper limit in `ℝ≥0∞`

Mathlib's `ENNReal.limsup_add_le` asks the filter to be closed under countable intersections, a
hypothesis its proof uses but the statement does not need: the upper limit of a sum of
`ℝ≥0∞`-valued functions is at most the sum of their upper limits along every filter
(`ENNReal.limsup_add_le'`). Neighbourhood filters, along which difference quotients are taken, are
not closed under countable intersections.
-/

public section

open Filter
open scoped ENNReal

namespace ENNReal

variable {α : Type*} {f : Filter α}

/-- The upper limit of a sum of `ℝ≥0∞`-valued functions is at most the sum of their upper limits,
along any filter. -/
theorem limsup_add_le' (u v : α → ℝ≥0∞) : f.limsup (u + v) ≤ f.limsup u + f.limsup v := by
  simp only [limsup_eq_iInf_iSup, iInf_subtype']
  rw [ENNReal.iInf_add_iInf fun s t ↦ ⟨⟨s.1 ∩ t.1, inter_mem s.2 t.2⟩, add_le_add
    (biSup_mono Set.inter_subset_left) (biSup_mono Set.inter_subset_right)⟩]
  exact iInf_mono fun s ↦ iSup₂_le fun a ha ↦ add_le_add (le_biSup u ha) (le_biSup v ha)

end ENNReal
