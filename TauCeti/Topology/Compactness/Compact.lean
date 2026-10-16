/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact

/-!
# Compactness utilities

General lemmas about compact subsets of topological spaces.
-/

public section

namespace TauCeti

open Set

variable {X : Type*} [TopologicalSpace X]

/-- Compactness of `U ∩ S` for a compact set `U` may be checked on open pieces of `U` around
each of its points. -/
theorem _root_.IsCompact.inter_of_forall_exists {U S : Set X} (hU : IsCompact U)
    (h : ∀ x ∈ U, ∃ U' ⊆ U, IsOpen U' ∧ x ∈ U' ∧ IsCompact (U' ∩ S)) : IsCompact (U ∩ S) := by
  choose! W hWU hWo hxW hWc using h
  obtain ⟨t, htU, htf, ht⟩ :=
    hU.elim_finite_subcover_image hWo fun x hx ↦ mem_biUnion hx (hxW x hx)
  have heq : U ∩ S = ⋃ x ∈ t, W x ∩ S := by
    rw [← iUnion₂_inter]
    exact subset_antisymm (inter_subset_inter_left S ht)
      (inter_subset_inter_left S (iUnion₂_subset fun x hx ↦ hWU x (htU hx)))
  rw [heq]
  exact htf.isCompact_biUnion fun x hx ↦ hWc x (htU hx)

end TauCeti

end
