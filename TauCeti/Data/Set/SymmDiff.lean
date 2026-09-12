/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.SymmDiff

/-!
# Symmetric differences of intersections

The symmetric difference of an intersection with a set lies in the union of the symmetric
differences: the intersection member of Mathlib's `Set.union_symmDiff_subset` family, obtained
from the union member by complementation.
-/

public section

namespace Set

open scoped symmDiff

variable {α : Type*} {s t u : Set α}

/-- `(s ∩ t) ∆ u ⊆ s ∆ u ∪ t ∆ u`. -/
theorem inter_symmDiff_subset : (s ∩ t) ∆ u ⊆ s ∆ u ∪ t ∆ u := by
  simpa only [← compl_inter, compl_symmDiff_compl] using
    (union_symmDiff_subset (s := sᶜ) (t := tᶜ) (u := uᶜ))

end Set
