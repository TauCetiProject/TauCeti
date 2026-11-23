/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Infima under the descending chain condition

In a complete lattice satisfying the descending chain condition (`WellFoundedLT`), every indexed
infimum is already the infimum of a finite subfamily: in the order dual, which satisfies the
ascending chain condition, every element is compact. For the lattice of submodules of an Artinian
module, an intersection of submodules is a finite intersection.

## Main results

* `WellFoundedLT.exists_finset_iInf_eq`: an indexed infimum is the infimum of a finite subfamily.
-/

public section

/-- **Infima under the descending chain condition are finite**: in a complete lattice with
`WellFoundedLT`, an indexed infimum is the infimum of a finite subfamily. -/
theorem WellFoundedLT.exists_finset_iInf_eq {α ι : Type*} [CompleteLattice α] [WellFoundedLT α]
    (p : ι → α) : ∃ s : Finset ι, ⨅ i ∈ s, p i = ⨅ i, p i := by
  -- In the order dual, which satisfies the ascending chain condition, `⨅ i, p i` is compact.
  have hk : IsCompactElement (OrderDual.toDual (⨅ i, p i)) := .of_wellFoundedGT _
  obtain ⟨s, hs⟩ := hk.exists_finset_of_le_iSup (fun i ↦ OrderDual.toDual (p i)) le_rfl
  exact ⟨s, le_antisymm hs (le_iInf₂ fun i _ ↦ iInf_le p i)⟩
