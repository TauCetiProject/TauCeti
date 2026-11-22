/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Module

import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Intersections of submodules of an Artinian module

In an Artinian module every indexed intersection of submodules is already the intersection of a
finite subfamily (`TauCeti.IsArtinian.exists_finset_iInf_eq`): in the order dual of the lattice of
submodules every element is compact.
-/

public section

namespace TauCeti

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- **Intersections in an Artinian module are finite**: an indexed intersection of submodules of an
Artinian module is the intersection of a finite subfamily. -/
theorem IsArtinian.exists_finset_iInf_eq [IsArtinian R M] {ι : Type*} (p : ι → Submodule R M) :
    ∃ s : Finset ι, ⨅ i ∈ s, p i = ⨅ i, p i := by
  -- In the order dual of the lattice of submodules, which is Noetherian, `⨅ i, p i` is compact.
  have hk : IsCompactElement (OrderDual.toDual (⨅ i, p i)) := .of_wellFoundedGT _
  obtain ⟨s, hs⟩ := hk.exists_finset_of_le_iSup (fun i ↦ OrderDual.toDual (p i)) le_rfl
  exact ⟨s, le_antisymm hs (le_iInf₂ fun i _ ↦ iInf_le p i)⟩

end TauCeti
