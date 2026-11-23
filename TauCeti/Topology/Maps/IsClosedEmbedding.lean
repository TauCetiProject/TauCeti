/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Open thickenings along a closed embedding

Let `φ : A → Z` be a closed embedding such that a subset `X` of `Z` together with the image of `φ`
is all of `Z`, and let `O` be an open subset of `A` containing every point which `φ` sends into
`X`. Then `X ∪ φ(O)` is open in `Z` (`Topology.IsClosedEmbedding.isOpen_union_image`): its
complement is the image of the closed set `A ∖ O`. When `Z` is obtained from `X` by attaching `A`
along the points sent into `X`, this thickens `X` to an open neighbourhood.
-/

public section

open Set

namespace Topology.IsClosedEmbedding

variable {A Z : Type*} [TopologicalSpace A] [TopologicalSpace Z] {O : Set A} {X : Set Z}
  {φ : A → Z}

/-- **The thickening of a subset along a closed embedding is open.** Let `φ : A → Z` be a closed
embedding such that `X` together with the image of `φ` is all of `Z`, and let `O` be an open subset
of `A` containing every point which `φ` sends into `X`. Then `X ∪ φ(O)` is open in `Z`: its
complement is the image of the closed set `A ∖ O`. -/
theorem isOpen_union_image (hφ : IsClosedEmbedding φ) (hO : IsOpen O)
    (hφX : ∀ a, φ a ∈ X → a ∈ O) (hcover : X ∪ range φ = univ) : IsOpen (X ∪ φ '' O) := by
  have hc : (X ∪ φ '' O)ᶜ = φ '' Oᶜ := by
    ext z
    refine ⟨fun hz ↦ ?_, ?_⟩
    · obtain ⟨a, rfl⟩ : z ∈ range φ :=
        (hcover.symm ▸ mem_univ z : z ∈ X ∪ range φ).resolve_left fun hzX ↦ hz (Or.inl hzX)
      exact ⟨a, fun ha ↦ hz (Or.inr ⟨a, ha, rfl⟩), rfl⟩
    · rintro ⟨a, ha, rfl⟩ (hX | ⟨b, hb, hba⟩)
      exacts [ha (hφX a hX), ha (hφ.injective hba ▸ hb)]
  rw [← isClosed_compl_iff, hc]
  exact hφ.isClosedMap _ hO.isClosed_compl

end Topology.IsClosedEmbedding
