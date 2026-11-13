/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated

/-!
# Closed images of closed sets under maps that are proper on a larger set

The image of a closed set on which a map is continuous is closed, provided the set lies in a set
whose intersection with every preimage of a compact set is compact. The target is a Hausdorff
compactly coherent space.
-/

public section

/-- The image of a closed set `S` on which `f` is continuous is closed, provided `S` lies in a set
`N` whose intersection with every preimage `f ⁻¹' K` of a compact set is compact. -/
theorem _root_.IsClosed.image_of_isCompact_inter_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] [CompactlyCoherentSpace Y] {f : X → Y} {S N : Set X}
    (hS : IsClosed S) (hcont : ContinuousOn f S) (hSN : S ⊆ N)
    (hprop : ∀ K : Set Y, IsCompact K → IsCompact (N ∩ f ⁻¹' K)) : IsClosed (f '' S) := by
  have hpre : ∀ K : Set Y, IsCompact K → IsCompact (S.domRestrict f ⁻¹' K) := by
    intro K hK
    rw [Subtype.isCompact_iff]
    have himg : ((↑) : S → X) '' (S.domRestrict f ⁻¹' K) = S ∩ (N ∩ f ⁻¹' K) := by
      ext z
      constructor
      · rintro ⟨⟨z, hz⟩, hzK, rfl⟩
        exact ⟨hz, hSN hz, hzK⟩
      · rintro ⟨hz, -, hzK⟩
        exact ⟨⟨z, hz⟩, hzK, rfl⟩
    rw [himg]
    exact (hprop K hK).inter_left hS
  have himgclosed := (isProperMap_iff_isCompact_preimage.2
    ⟨hcont.domRestrict, fun K hK ↦ hpre K hK⟩).isClosedMap _ isClosed_univ
  rwa [Set.image_univ, Set.range_domRestrict] at himgclosed
