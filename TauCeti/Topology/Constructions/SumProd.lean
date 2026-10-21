/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions.SumProd

/-!
# Interiors and fibres in product spaces

A subset of a product has empty interior if all its vertical fibres have empty interior.
This lets fibrewise empty-interior results apply to subsets of arbitrary topological products,
without countability, separation, or finite-dimensionality assumptions on either factor.
-/

public section

open Set

namespace TauCeti

/-- A subset of a product has empty interior if every vertical fibre has empty interior. -/
theorem interior_eq_empty_of_forall_interior_preimage_prodMk_eq_empty {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {s : Set (X × Y)}
    (hs : ∀ x, interior (Prod.mk x ⁻¹' s) = ∅) : interior s = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro ⟨x, y⟩ hxy
  have hy := preimage_interior_subset_interior_preimage (Continuous.prodMk_right x) hxy
  simp only [hs x, mem_empty_iff_false] at hy

end TauCeti
