/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompleteLattice.Basic
public import Mathlib.Order.Minimal

/-!
# A directed family in a well-founded meet-semilattice attains its bound

In a complete meet-semilattice whose strict order is well founded, a nonempty downward-directed
family of elements contains its own infimum: a minimal member of the family is below every other
member, by directedness, so it *is* the infimum.

Mathlib's nearest statement is `CompleteLattice.IsSupClosedCompact`, which concludes `sSup s ∈ s`
from `WellFoundedGT` for a set closed under binary suprema. Directedness is weaker than closure —
a chain is directed but rarely closed — and it is what descending filtrations supply, so the two
do not subsume one another.

## Main results

* `Directed.exists_eq_iInf`: a nonempty downward-directed family in a complete meet-semilattice
  with `WellFoundedLT` attains its infimum.
-/

public section

/-- **A nonempty downward-directed family in a well-founded complete meet-semilattice attains its
infimum.**

Only arbitrary infima are used, so `CompleteSemilatticeInf` is the natural hypothesis; a complete
lattice is the case of interest.

Nonemptiness of the index is needed: over an empty index the infimum is the greatest element
and no member attains it. -/
theorem Directed.exists_eq_iInf {α : Type*} [CompleteSemilatticeInf α] [WellFoundedLT α]
    {ι : Sort*} [Nonempty ι] {f : ι → α} (hf : Directed (· ≥ ·) f) : ∃ i, f i = ⨅ j, f j := by
  obtain ⟨a, hmin⟩ := exists_minimal_of_wellFoundedLT (· ∈ Set.range f) (Set.range_nonempty f)
  obtain ⟨i, rfl⟩ := hmin.1
  refine ⟨i, ?_⟩
  -- The indexed infimum is the infimum of the range, which is the set a minimal member lives in.
  rw [← sInf_range]
  -- A minimal member of a downward-directed family is below every member of it.
  refine le_antisymm (le_sInf ?_) (sInf_le (Set.mem_range_self i))
  rintro _ ⟨j, rfl⟩
  exact hf.directedOn_range.le_of_minimal hmin ⟨j, rfl⟩
