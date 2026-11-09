/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.OpenSimplex
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier

/-!
# Subdividing a simplicial complex from the centroids of its simplices

The *open simplex* of a simplex `s` of a geometric simplicial complex `K` is the intrinsic
interior of its convex hull. It contains the centroid of `s`
(`AffineIndependent.centroid_mem_intrinsicInterior_convexHull`), and distinct simplices of `K`
have disjoint open simplices (`Geometry.SimplicialComplex.eq_of_mem_intrinsicInterior`).

Coning every simplex of a locally finite complex `K` from its centroid, in order of increasing
dimension, subdivides `K` (`Geometry.SimplicialComplex.exists_subdivision_centroid_mem`), as in the
barycentric subdivision. The resulting complex `L` has the same support, triangulates every
simplex of `K` by finitely many of its simplices and is again locally finite. Every simplex `t` of
`L` is controlled by a simplex `s` of `K`: the centroid of `s` is a vertex of `t`, and the open
simplex of `t` lies in the open simplex of `s`. In particular every vertex of `L` is the centroid of
a simplex of `K`.

Such a subdivision is used in Łojasiewicz's triangulation of semianalytic sets, where a
triangulation of the base is subdivided so that every subdivided open simplex lies in a single open
simplex of the original triangulation and has the centroid of that simplex as a distinguished
vertex.

## Main results

* `Geometry.SimplicialComplex.exists_subdivision_centroid_mem`: a locally finite simplicial complex
  has a locally finite subdivision each of whose simplices has as a vertex the centroid of a simplex
  of the original complex whose open simplex contains its own.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) 18
  (1964), 449–474, §4 (the barycentric subdivision of the triangulated base).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (derived subdivisions).
-/

public section

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Subdivision from the centroids.** A locally finite simplicial complex `K` has a locally
finite subdivision `L`, obtained as in the barycentric subdivision by coning every simplex of `K`
from its centroid. The complex `L` has the same support as `K` and triangulates every simplex of
`K` by finitely many of its simplices. Every simplex `t` of `L` is controlled by a simplex `s` of
`K`: the centroid of `s` is a vertex of `t`, and the open simplex of `t` lies in that of `s`. -/
theorem exists_subdivision_centroid_mem (K : SimplicialComplex ℝ E)
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E)) :
    ∃ L : SimplicialComplex ℝ E, L.space = K.space ∧
      (∀ s ∈ K.faces, (L.restrict (convexHull ℝ (s : Set E))).space = convexHull ℝ (s : Set E) ∧
        (L.restrict (convexHull ℝ (s : Set E))).faces.Finite) ∧
      (∀ t ∈ L.faces, ∃ s ∈ K.faces, s.centroid ℝ id ∈ t ∧
        intrinsicInterior ℝ (convexHull ℝ (t : Set E)) ⊆
          intrinsicInterior ℝ (convexHull ℝ (s : Set E))) ∧
      LocallyFinite fun t : L.faces => convexHull ℝ (t : Set E) := by
  classical
  have hc : ∀ s : K.faces, s.1.centroid ℝ id ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
    intro s
    have : Nonempty s.1 := (K.nonempty_of_mem_faces s.2).coe_sort
    -- the centroid of `s` is that of the affinely independent inclusion `s → E`
    rw [← Finset.centroid_univ, ← Finset.setOfPred_mem, ← Subtype.range_coe_subtype]
    exact (K.indep s.2).centroid_mem_intrinsicInterior_convexHull
  -- a point of the frontier of a simplex lies in the open simplex of a proper face
  have hfr : ∀ s : K.faces, intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ⊆
      ⋃ (t : K.faces) (_ : t ≠ s ∧ convexHull ℝ (t : Set E) ⊆ convexHull ℝ (s : Set E)),
        convexHull ℝ (t : Set E) := by
    intro s x hx
    have hcl : IsClosed (convexHull ℝ (s : Set E)) := s.1.finite_toSet.isClosed_convexHull ℝ
    rw [← hcl.sdiff_intrinsicInterior] at hx
    obtain ⟨t, ht, hts, hxt⟩ := exists_mem_faces_subset_mem_intrinsicInterior s.2 hx.1
    exact mem_iUnion₂.2 ⟨⟨t, ht⟩, ⟨fun h => hx.2 (congrArg Subtype.val h ▸ hxt),
      convexHull_mono (Finset.coe_subset.2 hts)⟩, intrinsicInterior_subset hxt⟩
  have hri : Pairwise fun s t : K.faces =>
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
        (intrinsicInterior ℝ (convexHull ℝ (t : Set E))) := fun s t hst =>
    Set.disjoint_left.2 fun _ hxs hxt =>
      hst (Subtype.ext (eq_of_mem_intrinsicInterior s.2 t.2 hxs hxt))
  obtain ⟨L, hLs, hLP, hLf, hLlf⟩ :=
    exists_subdivision (fun s : K.faces => convexHull ℝ (s : Set E))
    (fun s => s.1.finite_toSet.isCompact_convexHull ℝ) (fun _ => convex_convexHull ℝ _)
    (fun s => s.1.centroid ℝ id) hc hK hri hfr
  refine ⟨L, ?_, fun s hs => hLP ⟨s, hs⟩, fun t ht => ?_, hLlf⟩
  · rw [hLs]
    ext x
    rw [mem_space_iff, mem_iUnion]
    exact ⟨fun ⟨s, hx⟩ => ⟨s.1, s.2, hx⟩, fun ⟨s, hs, hx⟩ => ⟨⟨s, hs⟩, hx⟩⟩
  · obtain ⟨s, hst, hts⟩ := hLf t ht
    exact ⟨s, s.2, hst, TauCeti.intrinsicInterior_mono_of_inter_intrinsicInterior_nonempty
      (convex_convexHull ℝ _) (convexHull_min hts (convex_convexHull ℝ _))
      ⟨_, subset_convexHull ℝ _ hst, hc s⟩⟩

end Geometry.SimplicialComplex
