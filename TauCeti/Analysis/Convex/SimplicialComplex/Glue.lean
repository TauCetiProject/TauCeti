/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.Analysis.Convex.SimplicialComplex.Restrict
import Mathlib.Analysis.Convex.Combination
import TauCeti.Analysis.Convex.Extreme

/-!
# Gluing geometric simplicial complexes along common faces

A family of geometric simplicial complexes `K i` in a module `E` glues to a single simplicial
complex, `Geometry.SimplicialComplex.glue K h`, whose faces are the faces of all the `K i`, as soon
as the convex hulls of a face of `K i` and a face of `K j` always meet inside the convex hull of
their common vertices. Its underlying space is the union of the spaces `|K i|`, and if each `K i`
is finite and the spaces `|K i|` form a locally finite family, its simplices form a locally finite
family. More generally, a complex is locally finite when its simplices lie in a locally finite
complex or in the cells of a locally finite family of convex sets, finitely many in each cell
(`locallyFinite_convexHull_of_finite_restrict`).

The compatibility condition is checked geometrically when the complexes triangulate sets which
meet along common faces. Suppose every point of `|K i| ∩ |K j|` lies in a set `F` which is an
extreme subset of both `|K i|` and `|K j|`, and such that every face of `K i` with all vertices in
`F` is a face of `K j`; for instance, `K i` and `K j` restrict to the same subcomplex on `F`.
Then a face of `K i` and a face of `K j` meet properly
(`convexHull_inter_convexHull_subset_of_isExtreme`): the point of intersection is carried by
faces with all vertices in `F`, which are then faces of `K j`. Gluing retains the triangulation
of each piece on its convex subsets (`restrict_glue`).

This is the common-face agreement and coverage step in subdividing a locally finite family of
compact convex polytopes, meeting in common faces, into a single simplicial complex compatible
with prescribed triangulations of their faces: each polytope is triangulated separately, by
coning a triangulation of its boundary, and the pieces are glued.

## Main definitions

* `Geometry.SimplicialComplex.glue`: the simplicial complex whose faces are the faces of a
  family of pairwise compatible complexes.

## Main results

* `Geometry.SimplicialComplex.space_glue`: `|glue K h| = ⋃ i, |K i|`.
* `Geometry.SimplicialComplex.glue_le_iff`: the glued complex is the least complex containing
  every `K i`.
* `Geometry.SimplicialComplex.locallyFinite_convexHull_glue`: gluing a locally finite family of
  finite complexes gives a locally finite complex.
* `Geometry.SimplicialComplex.locallyFinite_convexHull_of_finite_restrict`: a complex whose
  simplices lie in a locally finite complex or in the cells of a locally finite family of convex
  sets, finitely many in each cell, is locally finite.
* `Geometry.SimplicialComplex.convexHull_inter_convexHull_subset_of_isExtreme`: complexes
  agreeing on common extreme subsets covering the intersection of their spaces meet properly.
* `Geometry.SimplicialComplex.restrict_glue`: gluing along common faces does not change the
  restriction of each piece to its convex subsets.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial complexes and subdivisions of cell complexes).
-/

public section

open Finset Set

namespace Geometry.SimplicialComplex

section OrderedRing

variable {𝕜 E ι : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  {K : ι → SimplicialComplex 𝕜 E} {L : SimplicialComplex 𝕜 E} {s : Finset E} {x : E}

/-- The simplicial complex whose faces are the faces of all the complexes `K i`, provided the
convex hulls of a face of `K i` and a face of `K j` always meet inside the convex hull of their
common vertices. -/
def glue (K : ι → SimplicialComplex 𝕜 E)
    (h : ∀ i j, ∀ ⦃s t : Finset E⦄, s ∈ (K i).faces → t ∈ (K j).faces →
      convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E)) :
    SimplicialComplex 𝕜 E where
  faces := ⋃ i, (K i).faces
  isRelLowerSet_faces := IsRelLowerSet.iUnion fun i => (K i).isRelLowerSet_faces
  indep hs := by
    obtain ⟨i, hs⟩ := mem_iUnion.1 hs
    exact (K i).indep hs
  inter_subset_convexHull hs ht := by
    obtain ⟨i, hs⟩ := mem_iUnion.1 hs
    obtain ⟨j, ht⟩ := mem_iUnion.1 ht
    exact h i j hs ht

variable (h : ∀ i j, ∀ ⦃s t : Finset E⦄, s ∈ (K i).faces → t ∈ (K j).faces →
  convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E))

@[simp]
theorem mem_glue_faces : s ∈ (glue K h).faces ↔ ∃ i, s ∈ (K i).faces :=
  mem_iUnion

theorem le_glue (i : ι) : K i ≤ glue K h :=
  fun _ hs => (mem_glue_faces h).2 ⟨i, hs⟩

/-- The glued complex is the least simplicial complex containing every `K i`. -/
theorem glue_le_iff : glue K h ≤ L ↔ ∀ i, K i ≤ L :=
  ⟨fun hL i => (le_glue h i).trans hL, fun hL _ hs =>
    let ⟨i, hs⟩ := (mem_glue_faces h).1 hs
    hL i hs⟩

@[simp]
theorem space_glue : (glue K h).space = ⋃ i, (K i).space := by
  ext x
  simp only [mem_space_iff, mem_glue_faces, mem_iUnion]
  exact ⟨fun ⟨s, ⟨i, hs⟩, hx⟩ => ⟨i, s, hs, hx⟩, fun ⟨i, s, hs, hx⟩ => ⟨s, ⟨i, hs⟩, hx⟩⟩

@[simp]
theorem vertices_glue : (glue K h).vertices = ⋃ i, (K i).vertices := by
  ext x
  simp [mem_vertices]

/-- Gluing a locally finite family of finite complexes gives a complex whose simplices form a
locally finite family. -/
theorem locallyFinite_convexHull_glue [TopologicalSpace E] (hfin : ∀ i, (K i).faces.Finite)
    (hlf : LocallyFinite fun i => (K i).space) :
    LocallyFinite fun σ : (glue K h).faces => convexHull 𝕜 (σ.1 : Set E) := by
  intro x
  obtain ⟨U, hU, hfinU⟩ := hlf x
  refine ⟨U, hU, Finite.of_finite_image ((hfinU.biUnion fun i _ => hfin i).subset ?_)
    Subtype.val_injective.injOn⟩
  rintro _ ⟨σ, ⟨y, hyσ, hyU⟩, rfl⟩
  obtain ⟨i, hi⟩ := (mem_glue_faces h).1 σ.2
  exact mem_biUnion (x := i) ⟨y, convexHull_subset_space hi hyσ, hyU⟩ hi

end OrderedRing

section LocallyFinite

variable {𝕜 E ι : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E]

/-- A complex whose simplices are those of a locally finite complex `L` or lie in the cells of a
locally finite family of convex sets, with finitely many simplices in each cell, is locally
finite. -/
theorem locallyFinite_convexHull_of_finite_restrict {K L : SimplicialComplex 𝕜 E}
    {P : ι → Set E} (hPv : ∀ i, Convex 𝕜 (P i)) (hP : LocallyFinite P)
    (hL : LocallyFinite fun σ : L.faces => convexHull 𝕜 (σ : Set E))
    (hfin : ∀ i, (K.restrict (P i)).faces.Finite)
    (hK : ∀ s ∈ K.faces, s ∈ L.faces ∨ ∃ i, (s : Set E) ⊆ P i) :
    LocallyFinite fun σ : K.faces => convexHull 𝕜 (σ : Set E) := by
  intro x
  obtain ⟨U, hU, hUf⟩ := hL x
  obtain ⟨V, hV, hVf⟩ := hP x
  refine ⟨U ∩ V, Filter.inter_mem hU hV, Set.Finite.of_finite_image
    (((hUf.image Subtype.val).union (hVf.biUnion fun i _ => hfin i)).subset ?_)
    Subtype.val_injective.injOn⟩
  rintro _ ⟨σ, ⟨y, hyσ, hyU, hyV⟩, rfl⟩
  rcases hK σ.1 σ.2 with hσ | ⟨i, hσi⟩
  · exact .inl ⟨⟨σ.1, hσ⟩, ⟨y, hyσ, hyU⟩, rfl⟩
  · exact .inr (Set.mem_biUnion (x := i) ⟨y, (hPv i).convexHull_subset_iff.2 hσi hyσ, hyV⟩
      (mem_restrict_faces.2 ⟨σ.2, hσi⟩))

end LocallyFinite

section LinearOrderedField

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {K : ι → SimplicialComplex 𝕜 E} {s t : Finset E}

/-- Two simplicial complexes `K` and `L` meet properly if every point of `|K| ∩ |L|` lies in a
set `F` which is an extreme subset of both `|K|` and `|L|` and such that every face of `K` with
all vertices in `F` is a face of `L`: the convex hulls of a face of `K` and a face of `L` then
meet inside the convex hull of their common vertices. -/
theorem convexHull_inter_convexHull_subset_of_isExtreme {K L : SimplicialComplex 𝕜 E}
    (hKL : ∀ x ∈ K.space ∩ L.space, ∃ F, x ∈ F ∧ IsExtreme 𝕜 K.space F ∧
      IsExtreme 𝕜 L.space F ∧ K.restrict F ≤ L.restrict F)
    (hs : s ∈ K.faces) (ht : t ∈ L.faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E) := by
  rintro x ⟨hxs, hxt⟩
  obtain ⟨F, hxF, hKF, hLF, hKLF⟩ :=
    hKL x ⟨convexHull_subset_space hs hxs, convexHull_subset_space ht hxt⟩
  obtain ⟨s', hss', hs', hxs'⟩ := exists_subset_mem_restrict_faces hKF hs hxs hxF
  obtain ⟨t', htt', ht', hxt'⟩ := exists_subset_mem_restrict_faces hLF ht hxt hxF
  exact convexHull_mono (inter_subset_inter (coe_subset.2 hss') (coe_subset.2 htt'))
    ((L.restrict F).inter_subset_convexHull (hKLF hs') ht' ⟨hxs', hxt'⟩)

/-- Suppose that for any two distinct complexes `K i` and `K j` of a family, every point of
`|K i| ∩ |K j|` lies in a common extreme subset `F` of `|K i|` and `|K j|` such that the faces of
`K i` with all vertices in `F` are faces of `K j`. Then the faces of the family pairwise meet
properly, so the family can be glued. -/
theorem inter_subset_convexHull_of_isExtreme
    (hK : Pairwise fun i j => ∀ x ∈ (K i).space ∩ (K j).space, ∃ F, x ∈ F ∧
      IsExtreme 𝕜 (K i).space F ∧ IsExtreme 𝕜 (K j).space F ∧
        (K i).restrict F ≤ (K j).restrict F)
    (i j : ι) ⦃s t : Finset E⦄ (hs : s ∈ (K i).faces) (ht : t ∈ (K j).faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E) := by
  rcases eq_or_ne i j with rfl | hij
  · exact (K i).inter_subset_convexHull hs ht
  · exact convexHull_inter_convexHull_subset_of_isExtreme (hK hij) hs ht

/-- Gluing a family of complexes along common extreme subsets of their spaces does not change
the restriction of any piece `K i` to a convex subset of `|K i|`. In particular, prescribed
triangulations of the faces of the pieces survive in the glued complex. -/
theorem restrict_glue
    (hK : Pairwise fun i j => ∀ x ∈ (K i).space ∩ (K j).space, ∃ F, x ∈ F ∧
      IsExtreme 𝕜 (K i).space F ∧ IsExtreme 𝕜 (K j).space F ∧
        (K i).restrict F ≤ (K j).restrict F)
    {i : ι} {F : Set E} (hF : Convex 𝕜 F) (hFi : F ⊆ (K i).space) :
    (glue K (inter_subset_convexHull_of_isExtreme hK)).restrict F = (K i).restrict F := by
  classical
  ext s
  simp only [mem_restrict_faces, mem_glue_faces]
  refine ⟨fun ⟨⟨j, hs⟩, hsF⟩ => ⟨?_, hsF⟩, fun ⟨hs, hsF⟩ => ⟨⟨i, hs⟩, hsF⟩⟩
  rcases eq_or_ne j i with rfl | hji
  · exact hs
  -- The barycentre of `s` lies in `|K i| ∩ |K j|`; the extreme subset of `|K j|` containing it
  -- then contains all of `s`, so `s` is a face of the common restriction.
  have hxs : s.centerMass (fun _ => (1 : 𝕜)) id ∈ convexHull 𝕜 (s : Set E) :=
    s.centerMass_id_mem_convexHull (fun _ _ => zero_le_one)
      (by simpa using (K j).nonempty_of_mem_faces hs)
  obtain ⟨G, hxG, hjG, -, hG⟩ := hK hji _
    ⟨convexHull_subset_space hs hxs, hFi (hF.convexHull_subset_iff.2 hsF hxs)⟩
  have hsG : s ∈ ((K j).restrict G).faces := mem_restrict_faces.2 ⟨hs, fun y hy =>
    hjG.mem_of_centerMass_mem (fun _ _ => one_pos)
      (by simpa using convexHull_subset_space hs) hxG (mem_coe.1 hy)⟩
  exact restrict_le (hG hsG)

end LinearOrderedField

end Geometry.SimplicialComplex
