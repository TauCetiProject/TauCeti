/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Topology.Compactness.LocallyFinite
import TauCeti.Analysis.Convex.Extreme
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier

/-!
# Restricting a geometric simplicial complex to a set

For a geometric simplicial complex `K` and a set `B`, the faces of `K` all of whose vertices lie
in `B` form a subcomplex `K.restrict B`. When `B` is convex, its underlying space lies in
`|K| ∩ B`. For an arbitrary set `B`, the faces of `K` whose closed simplices lie in `B` form a
subcomplex `K.restrictConvexHull B` whose underlying space always lies in `|K| ∩ B`. It is all of
`|K| ∩ B` as soon as every simplex of `K` whose open simplex meets `B` lies in `B`
(`Geometry.SimplicialComplex.space_restrictConvexHull`), as happens for the simplices of a complex
lying in the underlying space of another one after cutting along its simplices.

When moreover `B` is an extreme subset of `|K|` (for instance a face of a convex polytope which
`K` triangulates), the restriction triangulates exactly `|K| ∩ B`
(`Geometry.SimplicialComplex.space_restrict_of_isExtreme`): the face of `K` carrying a point of
`B` can be shrunk to a face with all its vertices in `B`. So a triangulation of a convex polytope
induces a triangulation of each of its faces. This is what lets triangulations of polytopes
meeting along common faces be compared, and glued, face by face.

The restriction of a locally finite complex to a compact set has finitely many faces
(`Geometry.SimplicialComplex.finite_faces_restrict`).

## Main definitions

* `Geometry.SimplicialComplex.restrict`: the subcomplex of the faces with all vertices in a set.
* `Geometry.SimplicialComplex.restrictConvexHull`: the subcomplex of the faces whose closed
  simplices lie in a set.

## Main results

* `Geometry.SimplicialComplex.exists_subset_mem_restrict_faces`: a point of an extreme subset
  `B` of `|K|` lies in the convex hull of a face of `K.restrict B`, which can be chosen inside any
  given face of `K` whose convex hull contains the point.
* `Geometry.SimplicialComplex.space_restrict_of_isExtreme`: `|K.restrict B| = |K| ∩ B` when `B`
  is a convex extreme subset of `|K|`.
* `Geometry.SimplicialComplex.le_restrictConvexHull_iff`: `K.restrictConvexHull B` is the largest
  subcomplex of `K` whose underlying space lies in `B`.
* `Geometry.SimplicialComplex.space_restrictConvexHull`: `|K.restrictConvexHull B| = |K| ∩ B`
  when every simplex of `K` whose open simplex meets `B` lies in `B`.
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

/-- The subcomplex of `K` consisting of the faces whose closed simplices lie in `B`. Unlike
`K.restrict B`, its underlying space lies in `B` even when `B` is not convex. -/
def restrictConvexHull (K : SimplicialComplex 𝕜 E) (B : Set E) : SimplicialComplex 𝕜 E where
  faces := {s | s ∈ K.faces ∧ convexHull 𝕜 (s : Set E) ⊆ B}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsB⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht =>
      ⟨K.down_closed hs hts ht, (convexHull_mono (coe_subset.2 hts)).trans hsB⟩⟩
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

/-- A subcomplex has a smaller underlying space. -/
@[gcongr]
theorem space_mono {L : SimplicialComplex 𝕜 E} (h : K ≤ L) : K.space ⊆ L.space :=
  biUnion_subset_biUnion_left h

theorem space_restrict_subset_space : (K.restrict B).space ⊆ K.space :=
  space_mono restrict_le

/-- The underlying space of the restriction of `K` to a convex set `B` lies in `|K| ∩ B`. -/
theorem space_restrict_subset (hB : Convex 𝕜 B) : (K.restrict B).space ⊆ K.space ∩ B := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
  exact ⟨space_restrict_subset_space hx, hB.convexHull_subset_iff.2 hs.2 hxs⟩

@[simp, grind =]
theorem mem_restrictConvexHull_faces :
    s ∈ (K.restrictConvexHull B).faces ↔ s ∈ K.faces ∧ convexHull 𝕜 (s : Set E) ⊆ B :=
  Iff.rfl

@[simp, grind =]
theorem vertices_restrictConvexHull : (K.restrictConvexHull B).vertices = K.vertices ∩ B := by
  ext x
  simp [mem_vertices]

theorem restrictConvexHull_le : K.restrictConvexHull B ≤ K := fun _ hs => hs.1

theorem restrictConvexHull_le_restrict : K.restrictConvexHull B ≤ K.restrict B :=
  fun _ hs => ⟨hs.1, (subset_convexHull 𝕜 _).trans hs.2⟩

theorem restrictConvexHull_mono (h : B ⊆ C) : K.restrictConvexHull B ≤ K.restrictConvexHull C :=
  fun _ hs => ⟨hs.1, hs.2.trans h⟩

theorem restrictConvexHull_mono_left {L : SimplicialComplex 𝕜 E} (h : K ≤ L) :
    K.restrictConvexHull B ≤ L.restrictConvexHull B :=
  fun _ hs => ⟨h hs.1, hs.2⟩

@[simp, grind =]
theorem restrictConvexHull_restrictConvexHull :
    (K.restrictConvexHull B).restrictConvexHull C = K.restrictConvexHull (B ∩ C) := by
  ext s
  simp [and_assoc]

/-- The underlying space of `K.restrictConvexHull B` lies in `|K| ∩ B`. -/
theorem space_restrictConvexHull_subset : (K.restrictConvexHull B).space ⊆ K.space ∩ B := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
  exact ⟨convexHull_subset_space hs.1 hxs, hs.2 hxs⟩

/-- `K.restrictConvexHull B` is the largest subcomplex of `K` whose underlying space lies in
`B`. -/
theorem le_restrictConvexHull_iff {A : SimplicialComplex 𝕜 E} :
    A ≤ K.restrictConvexHull B ↔ A ≤ K ∧ A.space ⊆ B :=
  ⟨fun h => ⟨h.trans restrictConvexHull_le,
      (space_mono h).trans (space_restrictConvexHull_subset.trans inter_subset_right)⟩,
    fun h _ hs => ⟨h.1 hs, (convexHull_subset_space hs).trans h.2⟩⟩

@[simp]
theorem restrictConvexHull_eq_self : K.restrictConvexHull B = K ↔ K.space ⊆ B :=
  ⟨fun h => (le_restrictConvexHull_iff.1 h.ge).2,
    fun h => restrictConvexHull_le.antisymm (le_restrictConvexHull_iff.2 ⟨le_rfl, h⟩)⟩

/-- On a convex set, a closed simplex lies in the set exactly when its vertices do, so the two
restrictions agree. -/
theorem restrictConvexHull_eq_restrict (hB : Convex 𝕜 B) :
    K.restrictConvexHull B = K.restrict B := by
  ext s
  simp [hB.convexHull_subset_iff]

end OrderedRing

section Compact

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] {K : SimplicialComplex 𝕜 E} {B : Set E}

/-- Only finitely many simplices of a locally finite complex have all their vertices in a
compact set. -/
theorem finite_faces_restrict (hK : LocallyFinite fun s : K.faces => convexHull 𝕜 (s : Set E))
    (hB : IsCompact B) : (K.restrict B).faces.Finite := by
  refine ((hK.finite_nonempty_inter_compact hB).image Subtype.val).subset ?_
  intro s hs
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs.1
  exact ⟨⟨s, hs.1⟩, ⟨v, subset_convexHull 𝕜 _ hv, hs.2 hv⟩, rfl⟩

/-- Only finitely many simplices of a locally finite complex lie in a compact set. -/
theorem finite_faces_restrictConvexHull
    (hK : LocallyFinite fun s : K.faces => convexHull 𝕜 (s : Set E)) (hB : IsCompact B) :
    (K.restrictConvexHull B).faces.Finite :=
  (finite_faces_restrict hK hB).subset restrictConvexHull_le_restrict

end Compact

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

section Intrinsic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If a convex set `C` meets the simplicial complex `L` exactly in the subcomplex covering its
intrinsic frontier, and its intrinsic interior avoids `|L|`, then the restriction of `L` to `C`
has the intrinsic frontier of `C` as its space. -/
theorem space_restrict_eq_intrinsicFrontier {L : SimplicialComplex ℝ E} {C : Set E}
    (hCv : Convex ℝ C) (hfr : intrinsicFrontier ℝ C ⊆ (L.restrict C).space)
    (hint : Disjoint (intrinsicInterior ℝ C) L.space) :
    (L.restrict C).space = intrinsicFrontier ℝ C := by
  exact ((space_restrict_subset hCv).trans fun _ ⟨hxL, hxC⟩ =>
    TauCeti.inter_subset_intrinsicFrontier_of_disjoint hint ⟨hxC, hxL⟩).antisymm hfr

/-- If every simplex of `K` whose open simplex meets `B` lies in `B`, then the simplices of `K`
lying in `B` triangulate `|K| ∩ B`. -/
theorem space_restrictConvexHull {K : SimplicialComplex ℝ E} {B : Set E}
    (hKB : ∀ s ∈ K.faces, (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∩ B).Nonempty →
      convexHull ℝ (s : Set E) ⊆ B) :
    (K.restrictConvexHull B).space = K.space ∩ B := by
  refine space_restrictConvexHull_subset.antisymm fun x ⟨hxK, hxB⟩ => ?_
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hxK
  obtain ⟨t, ht, -, hxt⟩ := exists_mem_faces_subset_mem_intrinsicInterior hs hxs
  exact mem_space_iff.2 ⟨t, ⟨ht, hKB t ht ⟨x, hxt, hxB⟩⟩, intrinsicInterior_subset hxt⟩

/-- If every simplex of `K` whose open simplex meets a simplex of `L` lies in that simplex, then
the simplices of `K` lying in `|L|` triangulate `|K| ∩ |L|`. -/
theorem space_restrictConvexHull_space {K L : SimplicialComplex ℝ E}
    (hKL : ∀ s ∈ K.faces, ∀ u ∈ L.faces,
      (intrinsicInterior ℝ (convexHull ℝ (s : Set E)) ∩ convexHull ℝ (u : Set E)).Nonempty →
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (u : Set E)) :
    (K.restrictConvexHull L.space).space = K.space ∩ L.space := by
  refine space_restrictConvexHull fun s hs ⟨x, hxs, hxL⟩ => ?_
  obtain ⟨u, hu, hxu⟩ := mem_space_iff.1 hxL
  exact (hKL s hs u hu ⟨x, hxs, hxu⟩).trans (convexHull_subset_space hu)

end Intrinsic

end Geometry.SimplicialComplex
