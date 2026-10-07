/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Closed images under addition

Addition carries a closed relation to a closed set if its second coordinate lies in a
compact set. This applies to bounded displacements in proper normed spaces, even when
the first coordinate ranges over a noncompact set. The argument uses Mathlib's closed
projection from a product with a compact space.
-/

public section

open Set

/-- The sums of a closed relation form a closed set if the second coordinate is contained
in a compact set. -/
theorem IsClosed.image_add_of_snd_subset {G : Type*} [TopologicalSpace G]
    [AddGroup G] [IsTopologicalAddGroup G] {s : Set (G × G)} (hs : IsClosed s)
    {C : Set G} (hC : IsCompact C) (hsub : Prod.snd '' s ⊆ C) :
    IsClosed ((fun p : G × G => p.1 + p.2) '' s) := by
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  have hc : Continuous (fun p : G × C => (p.1 - p.2, (p.2 : G))) :=
    (continuous_fst.sub (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have heq : (fun p : G × G => p.1 + p.2) '' s =
      Prod.fst '' ((fun p : G × C => (p.1 - p.2, (p.2 : G))) ⁻¹' s) := by
    ext z
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1 + p.2, ⟨p.2, hsub ⟨p, hp, rfl⟩⟩), by simpa, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p.1 - p.2, p.2), hp, by simp⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace _ (hs.preimage hc)
