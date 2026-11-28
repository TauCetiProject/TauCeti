/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ConnectedComponents

/-!
# Connected components of a category

Supplements `Mathlib.CategoryTheory.ConnectedComponents` by characterizing connectedness of a
category in terms of its type of connected components: `ConnectedComponents J` has a unique
element if and only if `J` is connected (`CategoryTheory.nonempty_unique_connectedComponents_iff`).
This matches the analogous characterization for simplicial sets
(`SSet.isConnected_iff_nonempty_unique`) and lets connectedness be transferred along bijections on
connected components such as `π₀ (nerve C) ≃ ConnectedComponents C`.
-/

public section

universe v u
namespace CategoryTheory

/-- `ConnectedComponents J` has a single element if and only if `J` is connected. -/
lemma nonempty_unique_connectedComponents_iff (J : Type u) [Category.{v} J] :
    Nonempty (Unique (ConnectedComponents J)) ↔ CategoryTheory.IsConnected J := by
  rw [unique_iff_subsingleton_and_nonempty]
  refine ⟨fun ⟨hsub, ⟨z⟩⟩ ↦ ?_, fun _ ↦
    ⟨⟨_root_.Quotient.ind₂ fun a b ↦ _root_.Quotient.sound (isPreconnected_zigzag a b)⟩,
      ⟨ConnectedComponents.mk (Classical.arbitrary J)⟩⟩⟩
  obtain ⟨j₀, -⟩ := _root_.Quotient.exists_rep z
  have : Nonempty J := ⟨j₀⟩
  exact zigzag_isConnected fun a b ↦ _root_.Quotient.exact (hsub.elim _ _)

end CategoryTheory
