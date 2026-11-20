/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path
import TauCeti.Topology.ConnectedComponents

/-!
# Separation by a path

A path separates two points inside a set when both points remain after the path's range is removed
and lie in different connected components of the resulting cut set. This is the topological
relation used to compare successive crosscuts in a prime-end chain.

The definition includes membership in the cut set, so it is false for a point on the path or
outside the ambient set. It depends only on the path's range: reversing the path changes nothing,
and a topological embedding preserves the relation.

## Main declarations

* `Path.SeparatesIn` -- a path separates two points inside a set.
* `Path.separatesIn_symm` -- reversing the path does not change separation.
* `Path.exists_separatesIn_iff_not_isPreconnected` -- a path separates some pair of points exactly
  when the cut set is not preconnected.
* `Path.separatesIn_map_iff` -- separation is invariant under topological embeddings.
-/

public section

open Set Topology

namespace Path

universe u v

variable {X : Type u} [TopologicalSpace X] {x y : X}
  (γ : Path x y) (U : Set X) (z w : X)

/-- A path separates two points in `U` when both points lie in `U \ range γ` and belong to
different connected components of that cut set. -/
def SeparatesIn : Prop :=
  z ∈ U \ range γ ∧ w ∈ U \ range γ ∧
    connectedComponentIn (U \ range γ) z ≠ connectedComponentIn (U \ range γ) w

/-- The defining characterization of separation by a path. -/
theorem separatesIn_def :
    γ.SeparatesIn U z w ↔
      z ∈ U \ range γ ∧ w ∈ U \ range γ ∧
        connectedComponentIn (U \ range γ) z ≠ connectedComponentIn (U \ range γ) w :=
  Iff.rfl

/-- Separation by a path is symmetric in the two points. -/
theorem separatesIn_comm : γ.SeparatesIn U z w ↔ γ.SeparatesIn U w z := by
  rw [separatesIn_def, separatesIn_def]
  tauto

/-- A path does not separate a point from itself. -/
@[simp]
theorem not_separatesIn_self : ¬ γ.SeparatesIn U z z := by
  simp [SeparatesIn]

/-- A path separates some pair of points in `U` exactly when removing its range from `U` leaves a
set that is not preconnected. -/
theorem exists_separatesIn_iff_not_isPreconnected :
    (∃ z w, γ.SeparatesIn U z w) ↔ ¬ IsPreconnected (U \ range γ) := by
  constructor
  · rintro ⟨z, w, hz, hw, hne⟩ hpre
    exact hne ((hpre.connectedComponentIn hz).trans (hpre.connectedComponentIn hw).symm)
  · intro hpre
    by_contra! h
    refine hpre (isPreconnected_of_forall_pair fun z hz w hw =>
      ⟨connectedComponentIn (U \ range γ) z, connectedComponentIn_subset _ _,
        mem_connectedComponentIn hz, ?_, isPreconnected_connectedComponentIn⟩)
    -- `γ` does not separate `z` from `w`, so they have the same component in the cut set
    rw [not_not.mp fun hne => h z w ⟨hz, hw, hne⟩]
    exact mem_connectedComponentIn hw

/-- Reversing a path does not change which points it separates. -/
@[simp]
theorem separatesIn_symm : γ.symm.SeparatesIn U z w ↔ γ.SeparatesIn U z w := by
  simp only [SeparatesIn, Path.symm_range]

/-- A topological embedding preserves separation by a path. For an ambient homeomorphism `e`, use
`e.isEmbedding`. -/
@[simp]
theorem separatesIn_map_iff {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : IsEmbedding f) :
    (γ.map hf.continuous).SeparatesIn (f '' U) (f z) (f w) ↔ γ.SeparatesIn U z w := by
  have hcut : f '' U \ range (γ.map hf.continuous) = f '' (U \ range γ) := by
    rw [map_coe, range_comp, image_sdiff hf.injective]
  -- `f` carries each connected component of the cut set onto a component of its image
  have hcomp (q : X) : connectedComponentIn (f '' (U \ range γ)) (f q) =
      f '' connectedComponentIn (U \ range γ) q := by
    rw [← hf.isInducing.image_connectedComponentIn_preimage
      ((connectedComponentIn_subset _ _).trans (image_subset_range _ _)),
      hf.injective.preimage_image]
  simp only [SeparatesIn, hcut, hcomp, hf.injective.mem_set_image,
    hf.injective.image_injective.ne_iff]

end Path

end
