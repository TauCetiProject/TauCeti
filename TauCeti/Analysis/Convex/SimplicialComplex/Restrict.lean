/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import TauCeti.Analysis.Convex.Extreme

/-!
# Restricting a geometric simplicial complex to a set

For a geometric simplicial complex `K` and a set `B`, the faces of `K` all of whose vertices lie
in `B` form a subcomplex `K.restrict B`. When `B` is convex, its underlying space lies in
`|K| ∩ B`.

When moreover `B` is an extreme subset of `|K|` (for instance a face of a convex polytope which
`K` triangulates), the restriction triangulates exactly `|K| ∩ B`
(`Geometry.SimplicialComplex.space_restrict_of_isExtreme`): the face of `K` carrying a point of
`B` can be shrunk to a face with all its vertices in `B`. So a triangulation of a convex polytope
induces a triangulation of each of its faces. This is what lets triangulations of polytopes
meeting along common faces be compared, and glued, face by face.

## Main definitions

* `Geometry.SimplicialComplex.restrict`: the subcomplex of the faces with all vertices in a set.

## Main results

* `Geometry.SimplicialComplex.exists_subset_mem_restrict_faces`: a point of an extreme subset
  `B` of `|K|` lies in the convex hull of a face of `K.restrict B`, which can be chosen inside any
  given face of `K` whose convex hull contains the point.
* `Geometry.SimplicialComplex.space_restrict_of_isExtreme`: `|K.restrict B| = |K| ∩ B` when `B`
  is a convex extreme subset of `|K|`.
-/

public section

open Finset Set

namespace Geometry.SimplicialComplex

section OrderedRing

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {K : SimplicialComplex 𝕜 E} {B C : Set E} {s : Finset E}

/-- The subcomplex of `K` consisting of the faces all of whose vertices lie in `B`. -/
def restrict (K : SimplicialComplex 𝕜 E) (B : Set E) : SimplicialComplex 𝕜 E where
  faces := {s | s ∈ K.faces ∧ (s : Set E) ⊆ B}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsB⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht =>
      ⟨K.down_closed hs hts ht, (coe_subset.2 hts).trans hsB⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

@[simp]
theorem mem_restrict_faces : s ∈ (K.restrict B).faces ↔ s ∈ K.faces ∧ (s : Set E) ⊆ B :=
  Iff.rfl

theorem restrict_le : K.restrict B ≤ K := fun _ hs => hs.1

theorem restrict_mono (h : B ⊆ C) : K.restrict B ≤ K.restrict C :=
  fun _ hs => ⟨hs.1, hs.2.trans h⟩

@[simp]
theorem restrict_restrict : (K.restrict B).restrict C = K.restrict (B ∩ C) := by
  ext s
  simp [and_assoc]

theorem restrict_eq_self_of_space_subset (h : K.space ⊆ B) : K.restrict B = K := by
  ext s
  exact ⟨fun hs => hs.1, fun hs => ⟨hs, (K.subset_space hs).trans h⟩⟩

theorem space_restrict_subset_space : (K.restrict B).space ⊆ K.space :=
  biUnion_subset_biUnion_left fun _ hs => hs.1

/-- The underlying space of the restriction of `K` to a convex set `B` lies in `|K| ∩ B`. -/
theorem space_restrict_subset (hB : Convex 𝕜 B) : (K.restrict B).space ⊆ K.space ∩ B := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
  exact ⟨space_restrict_subset_space hx, hB.convexHull_subset_iff.2 hs.2 hxs⟩

end OrderedRing

section LinearOrderedField

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {K : SimplicialComplex 𝕜 E} {B : Set E} {s : Finset E} {x : E}

/-- If `B` is an extreme subset of `|K|`, a point of `B` in the convex hull of a face `s` of `K`
lies in the convex hull of a face of `K.restrict B` contained in `s`. -/
theorem exists_subset_mem_restrict_faces (hB : IsExtreme 𝕜 K.space B) (hs : s ∈ K.faces)
    (hxs : x ∈ convexHull 𝕜 (s : Set E)) (hxB : x ∈ B) :
    ∃ t ⊆ s, t ∈ (K.restrict B).faces ∧ x ∈ convexHull 𝕜 (t : Set E) := by
  classical
  have hx : x ∈ convexHull 𝕜 (({y ∈ s | y ∈ B} : Finset E) : Set E) := by
    have hsB : (({y ∈ s | y ∈ B} : Finset E) : Set E) = ↑s ∩ B := by
      ext
      simp
    rw [hsB]
    exact hB.convexHull_inter_subset (convexHull_subset_space hs) ⟨hxs, hxB⟩
  have hne : ({y ∈ s | y ∈ B} : Finset E).Nonempty := by
    rw [← coe_nonempty, ← convexHull_nonempty_iff (𝕜 := 𝕜)]
    exact ⟨x, hx⟩
  refine ⟨_, filter_subset _ _, ⟨K.down_closed hs (filter_subset _ _) hne, ?_⟩, hx⟩
  intro y hy
  exact (mem_filter.1 hy).2

/-- The restriction of `K` to a convex extreme subset `B` of `|K|` triangulates `|K| ∩ B`. For
instance, a triangulation of a convex polytope restricts to a triangulation of each face. -/
theorem space_restrict_of_isExtreme (hB : IsExtreme 𝕜 K.space B) (hBc : Convex 𝕜 B) :
    (K.restrict B).space = K.space ∩ B := by
  refine (space_restrict_subset hBc).antisymm fun x ⟨hx, hxB⟩ => ?_
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
  obtain ⟨t, -, ht, hxt⟩ := exists_subset_mem_restrict_faces hB hs hxs hxB
  exact mem_space_iff.2 ⟨t, ht, hxt⟩

end LinearOrderedField

end Geometry.SimplicialComplex
