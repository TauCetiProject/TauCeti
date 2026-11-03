/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Order.Minimal

/-!
# A directed family in a well-founded order attains its infimum

In a partial order whose strict order is well founded, a nonempty downward-directed family has a
least member: a minimal member is below every other member, by directedness. Whenever `sInf`
returns greatest lower bounds that exist (`OrderInfSet`), for instance in a complete
meet-semilattice, that least member is therefore the infimum of the family.

Mathlib's nearest statement is `CompleteLattice.IsSupClosedCompact`, which concludes `sSup s ∈ s`
from `WellFoundedGT` for a set closed under binary suprema. It is phrased for sup-closed sets, so
it does not directly cover an arbitrary directed family — a chain is directed but rarely closed —
and a directed family is what a descending filtration supplies.

## Main results

* `Directed.exists_eq_iInf`: a nonempty downward-directed family in a partial order with
  `WellFoundedLT` and an `OrderInfSet` structure attains its infimum.
-/

public section

/-- **A nonempty downward-directed family in a well-founded partial order attains its infimum.**

The only property of `sInf` used is that it returns a greatest lower bound whenever one exists
(`OrderInfSet`), so this covers every complete meet-semilattice, in particular every complete
lattice.

Nonemptiness of the index is needed: over an empty index there is no member to attain the
infimum. (In a complete meet-semilattice that empty infimum is the top element.) -/
theorem Directed.exists_eq_iInf {α : Type*} [PartialOrder α] [OrderInfSet α] [WellFoundedLT α]
    {ι : Sort*} [Nonempty ι] {f : ι → α} (hf : Directed (· ≥ ·) f) : ∃ i, f i = ⨅ j, f j := by
  obtain ⟨a, hmin⟩ := exists_minimal_of_wellFoundedLT (· ∈ Set.range f) (Set.range_nonempty f)
  obtain ⟨i, rfl⟩ := hmin.1
  -- By directedness, a minimal member of the range is its least element, hence its infimum.
  exact ⟨i, (hf.directedOn_range.minimal_iff_isLeast.mp hmin).isGLB.iInf_eq.symm⟩
