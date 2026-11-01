/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.Intrinsic

/-!
# Subdividing a simplicial complex from the centroids of its simplices

The *open simplex* of a simplex `s` of a geometric simplicial complex `K` is the intrinsic
interior of its convex hull. Distinct simplices of `K` have disjoint open simplices
(`Geometry.SimplicialComplex.disjoint_intrinsicInterior_convexHull`), so every point of `|K|` lies
in at most one of them.

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

* `Geometry.SimplicialComplex.disjoint_intrinsicInterior_convexHull`: distinct simplices of a
  simplicial complex have disjoint open simplices.
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
  {K : SimplicialComplex ℝ E} {s t : Finset E}

/-- Distinct simplices of a simplicial complex have disjoint open simplices: the intrinsic
interiors of their convex hulls are disjoint. -/
theorem disjoint_intrinsicInterior_convexHull (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hst : s ≠ t) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
      (intrinsicInterior ℝ (convexHull ℝ (t : Set E))) := by
  classical
  refine Set.disjoint_left.2 fun x hxs hxt => ?_
  -- `x` lies in the common face spanned by `s ∩ t`, a proper face of `s` or of `t`
  have hx : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hs ht]
    exact ⟨intrinsicInterior_subset hxs, intrinsicInterior_subset hxt⟩
  by_cases h : s ∩ t = s
  · have hlt : s ∩ t ⊂ t := Finset.ssubset_iff_subset_ne.2
      ⟨Finset.inter_subset_right, fun h' => hst (h.symm.trans h')⟩
    exact Set.disjoint_left.1 ((K.indep ht).disjoint_convexHull_intrinsicInterior_convexHull hlt)
      hx hxt
  · have hlt : s ∩ t ⊂ s := Finset.ssubset_iff_subset_ne.2 ⟨Finset.inter_subset_left, h⟩
    exact Set.disjoint_left.1 ((K.indep hs).disjoint_convexHull_intrinsicInterior_convexHull hlt)
      hx hxs

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
  have hc : ∀ s : K.faces, s.1.centroid ℝ id ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) :=
    fun s => (K.indep s.2).centroid_mem_intrinsicInterior_convexHull (K.nonempty_of_mem_faces s.2)
  -- the frontier of a simplex is covered by its facets, which are simplices of `K`
  have hfr : ∀ s : K.faces, intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ⊆
      ⋃ (t : K.faces) (_ : t ≠ s ∧ convexHull ℝ (t : Set E) ⊆ convexHull ℝ (s : Set E)),
        convexHull ℝ (t : Set E) := by
    intro s x hx
    rw [(K.indep s.2).intrinsicFrontier_convexHull] at hx
    obtain ⟨v, hv, hxv⟩ := mem_iUnion₂.1 hx
    have hne : (s.1.erase v).Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.1 h, Finset.coe_empty, convexHull_empty] at hxv
      exact hxv
    refine mem_iUnion₂.2 ⟨⟨_, K.down_closed s.2 (Finset.erase_subset v s.1) hne⟩,
      ⟨fun h => Finset.notMem_erase v s.1 ?_, convexHull_mono (by simp)⟩, hxv⟩
    rw [show s.1.erase v = s.1 from congrArg Subtype.val h]
    exact hv
  have hri : Pairwise fun s t : K.faces =>
      Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
        (intrinsicInterior ℝ (convexHull ℝ (t : Set E))) := fun s t hst =>
    disjoint_intrinsicInterior_convexHull s.2 t.2 fun h => hst (Subtype.ext h)
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
    exact ⟨s, s.2, hst, (convex_convexHull ℝ _).intrinsicInterior_subset_intrinsicInterior
      (convexHull_min hts (convex_convexHull ℝ _)) (subset_convexHull ℝ _ hst) (hc s)⟩

end Geometry.SimplicialComplex
