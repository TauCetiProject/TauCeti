/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyFinite
public import TauCeti.AlgebraicTopology.SimplicialComplex.Basic
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
of each piece on its convex subsets (`restrict_glue`). Two complexes `K` and `L` also meet
properly as soon as `|K| ∩ |L|` is the underlying space of their common subcomplex `K ⊓ L`
(`inter_convexHull_subset_convexHull_of_space_inter_subset`), since a point of a subcomplex lying
in a simplex of the complex lies in a face of that simplex belonging to the subcomplex
(`exists_subset_mem_faces_of_le`).

This is the common-face agreement and coverage step in subdividing a locally finite family of
compact convex polytopes, meeting in common faces, into a single simplicial complex compatible
with prescribed triangulations of their faces: each polytope is triangulated separately, by
coning a triangulation of its boundary, and the pieces are glued.

## Main definitions

* `Geometry.SimplicialComplex.glue`: the simplicial complex whose faces are the faces of a
  family of pairwise compatible complexes.
* `Geometry.SimplicialComplex.ofSimplices`: the simplicial complex whose faces are the faces of
  a family of affinely independent simplices meeting pairwise in common faces, generated as
  `TauCeti.PreAbstractSimplicialComplex.ofGenerators`.

## Main results

* `Geometry.SimplicialComplex.space_glue`: `|glue K h| = ⋃ i, |K i|`.
* `Geometry.SimplicialComplex.space_ofSimplices`, `Geometry.SimplicialComplex.vertices_ofSimplices`:
  the underlying space and the vertices of `ofSimplices σ indep inter` are the unions of the convex
  hulls and of the vertex sets of the simplices `σ k`.
* `Geometry.SimplicialComplex.glue_le_iff`: the glued complex is the least complex containing
  every `K i`.
* `Geometry.SimplicialComplex.locallyFinite_convexHull_glue`: gluing a locally finite family of
  finite complexes gives a locally finite complex.
* `Geometry.SimplicialComplex.locallyFinite_convexHull_of_finite_restrict`: a complex whose
  simplices lie in a locally finite complex or in the cells of a locally finite family of convex
  sets, finitely many in each cell, is locally finite.
* `Geometry.SimplicialComplex.exists_subset_mem_faces_of_le`: a point of a subcomplex lying in a
  simplex of the complex lies in a face of that simplex belonging to the subcomplex.
* `Geometry.SimplicialComplex.inter_convexHull_subset_convexHull_of_space_inter_subset`: two
  complexes meeting in the underlying space of their common subcomplex have compatible faces.
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
    LocallyFinite fun σ : (glue K h).faces => convexHull 𝕜 (σ.val : Set E) := by
  intro x
  obtain ⟨U, hU, hfinU⟩ := hlf x
  refine ⟨U, hU, Finite.of_finite_image ((hfinU.biUnion fun i _ => hfin i).subset ?_)
    Subtype.val_injective.injOn⟩
  rintro _ ⟨σ, ⟨y, hyσ, hyU⟩, rfl⟩
  obtain ⟨i, hi⟩ := (mem_glue_faces h).1 σ.property
  exact mem_biUnion (x := i) ⟨y, convexHull_subset_space hi hyσ, hyU⟩ hi

/-- The faces of the pieces `L` and `T j` of a glued family meet compatibly, provided distinct
pieces `T j`, `T k` meet inside `|L|` and a point of `|L|` carried by a face of a piece is carried
by a subface which is a face of `L`. -/
theorem inter_convexHull_subset_convexHull_option {J : Type*} (L : SimplicialComplex 𝕜 E)
    (T : J → SimplicialComplex 𝕜 E) (C : J → Set E) (hT : ∀ j, (T j).space = C j)
    (hCC : Pairwise fun j k => C j ∩ C k ⊆ L.space)
    (hdesc : ∀ j ⦃s : Finset E⦄ ⦃x : E⦄, s ∈ (T j).faces → x ∈ convexHull 𝕜 (s : Set E) →
      x ∈ L.space → ∃ t ⊆ s, t ∈ L.faces ∧ x ∈ convexHull 𝕜 (t : Set E))
    (a b : Option J) ⦃s t : Finset E⦄ (hs : s ∈ ((a.elim L T : SimplicialComplex 𝕜 E)).faces)
    (ht : t ∈ ((b.elim L T : SimplicialComplex 𝕜 E)).faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E) := by
  have hdesc' : ∀ a : Option J, ∀ ⦃s : Finset E⦄ ⦃x : E⦄,
      s ∈ (a.elim L T : SimplicialComplex 𝕜 E).faces →
      x ∈ convexHull 𝕜 (s : Set E) → x ∈ L.space →
      ∃ t ⊆ s, t ∈ L.faces ∧ x ∈ convexHull 𝕜 (t : Set E) := by
    rintro (_ | j) s x hs hx hxL
    · exact ⟨s, Finset.Subset.rfl, hs, hx⟩
    · exact hdesc j hs hx hxL
  rintro x ⟨hxs, hxt⟩
  rcases eq_or_ne a b with rfl | hab
  · exact (a.elim L T : SimplicialComplex 𝕜 E).inter_subset_convexHull hs ht ⟨hxs, hxt⟩
  -- two distinct pieces meet inside `|L|`
  have hxL : x ∈ L.space := by
    rcases a with _ | j
    · exact convexHull_subset_space hs hxs
    rcases b with _ | k
    · exact convexHull_subset_space ht hxt
    exact hCC (fun hjk => hab (congrArg some hjk))
      ⟨hT j ▸ convexHull_subset_space hs hxs, hT k ▸ convexHull_subset_space ht hxt⟩
  obtain ⟨s', hss', hs', hxs'⟩ := hdesc' a hs hxs hxL
  obtain ⟨t', htt', ht', hxt'⟩ := hdesc' b ht hxt hxL
  exact convexHull_mono (Set.inter_subset_inter (coe_subset.2 hss') (coe_subset.2 htt'))
    (L.inter_subset_convexHull hs' ht' ⟨hxs', hxt'⟩)

/-- A point of a subcomplex `A` of `K` lying in a simplex `s` of `K` lies in the simplex of a
face of `A` contained in `s`. -/
theorem exists_subset_mem_faces_of_le {K A : SimplicialComplex 𝕜 E} {s : Finset E} (hAK : A ≤ K)
    (hs : s ∈ K.faces) (hxs : x ∈ convexHull 𝕜 (s : Set E)) (hxA : x ∈ A.space) :
    ∃ t ⊆ s, t ∈ A.faces ∧ x ∈ convexHull 𝕜 (t : Set E) := by
  classical
  obtain ⟨u, hu, hxu⟩ := mem_space_iff.1 hxA
  have hx : x ∈ convexHull 𝕜 ((s ∩ u : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hs (hAK hu) ⟨hxs, hxu⟩
  refine ⟨s ∩ u, Finset.inter_subset_left, A.down_closed hu Finset.inter_subset_right ?_, hx⟩
  rw [← Finset.coe_nonempty, ← convexHull_nonempty_iff (𝕜 := 𝕜)]
  exact ⟨x, hx⟩

/-- If two complexes meet in the underlying space of their common subcomplex, then a simplex of
one meets a simplex of the other in the convex hull of their common vertices, so their faces
together form a simplicial complex. -/
theorem inter_convexHull_subset_convexHull_of_space_inter_subset {K L : SimplicialComplex 𝕜 E}
    {s t : Finset E} (hKL : K.space ∩ L.space ⊆ (K ⊓ L).space) (hs : s ∈ K.faces)
    (ht : t ∈ L.faces) :
    convexHull 𝕜 ↑s ∩ convexHull 𝕜 ↑t ⊆ convexHull 𝕜 (s ∩ t : Set E) := by
  rintro x ⟨hxs, hxt⟩
  have hx := hKL ⟨convexHull_subset_space hs hxs, convexHull_subset_space ht hxt⟩
  obtain ⟨s', hss', hs', hxs'⟩ := exists_subset_mem_faces_of_le inf_le_left hs hxs hx
  obtain ⟨t', htt', ht', hxt'⟩ := exists_subset_mem_faces_of_le inf_le_right ht hxt hx
  exact convexHull_mono (Set.inter_subset_inter (Finset.coe_subset.2 hss')
    (Finset.coe_subset.2 htt')) ((K ⊓ L).inter_subset_convexHull hs' ht' ⟨hxs', hxt'⟩)

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
  rcases hK σ.val σ.property with hσ | ⟨i, hσi⟩
  · exact .inl ⟨⟨σ.val, hσ⟩, ⟨y, hyσ, hyU⟩, rfl⟩
  · exact .inr (Set.mem_biUnion (x := i) ⟨y, (hPv i).convexHull_subset_iff.2 hσi hyσ, hyV⟩
      (mem_restrict_faces.2 ⟨σ.property, hσi⟩))

/-- The restriction of `K` to a cell `P k` has finitely many faces, if `P k` is compact, the cells
are locally finite, the restriction of `L` to `P k` has finitely many faces, the restriction of
`K` to every cell `P m` with `d m < n` has finitely many faces, and every face of `K` is a face of
`L` or lies in such a cell. -/
theorem finite_faces_restrict_of_forall_lt {L K : SimplicialComplex 𝕜 E} {P : ι → Set E}
    (d : ι → ℕ) {n : ℕ} (k : ι) (hPc : IsCompact (P k)) (hPlf : LocallyFinite P)
    (hLfin : (L.restrict (P k)).faces.Finite)
    (hKP : ∀ k, d k < n → (K.restrict (P k)).faces.Finite)
    (hKf : ∀ s ∈ K.faces, s ∈ L.faces ∨
      ∃ k, d k < n ∧ (s : Set E) ⊆ P k) :
    (K.restrict (P k)).faces.Finite := by
  refine (hLfin.union (((hPlf.finite_nonempty_inter_compact
    hPc).inter_of_left {m | d m < n}).biUnion
      fun m hm => hKP m hm.2)).subset ?_
  -- a face of `K` in `P k` is a face of `L` or lies in a smaller cell meeting `P k`
  intro s hs
  obtain ⟨hs, hsP⟩ := mem_restrict_faces.1 hs
  rcases hKf s hs with hsL | ⟨m, hm, hsm⟩
  · exact .inl (mem_restrict_faces.2 ⟨hsL, hsP⟩)
  · obtain ⟨y, hy⟩ := K.nonempty_of_mem_faces hs
    exact .inr (Set.mem_biUnion (x := m) ⟨⟨y, hsm hy, hsP hy⟩, hm⟩
      (mem_restrict_faces.2 ⟨hs, hsm⟩))

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

/-- The simplicial complex whose faces are the nonempty subsets of the simplices `σ k`, provided
each `σ k` is affinely independent and the convex hulls of any two of them meet inside the convex
hull of their common vertices. -/
def ofSimplices (σ : ι → Finset E) (indep : ∀ k, AffineIndependent 𝕜 ((↑) : σ k → E))
    (inter : ∀ k l, convexHull 𝕜 ↑(σ k) ∩ convexHull 𝕜 ↑(σ l) ⊆
      convexHull 𝕜 ((σ k : Set E) ∩ σ l)) :
    SimplicialComplex 𝕜 E where
  toPreAbstractSimplicialComplex := TauCeti.PreAbstractSimplicialComplex.ofGenerators (range σ)
  indep := by
    intro t ht
    obtain ⟨-, _, ⟨k, rfl⟩, htk⟩ := TauCeti.PreAbstractSimplicialComplex.mem_ofGenerators.1 ht
    exact (indep k).mono (coe_subset.2 htk)
  inter_subset_convexHull := by
    classical
    intro s t hs ht x ⟨hxs, hxt⟩
    obtain ⟨-, _, ⟨k, rfl⟩, hsk⟩ := TauCeti.PreAbstractSimplicialComplex.mem_ofGenerators.1 hs
    obtain ⟨-, _, ⟨l, rfl⟩, htl⟩ := TauCeti.PreAbstractSimplicialComplex.mem_ofGenerators.1 ht
    set U := σ k ∩ σ l
    have hU : x ∈ convexHull 𝕜 (U : Set E) := by
      rw [coe_inter]
      exact inter k l ⟨convexHull_mono (coe_subset.2 hsk) hxs,
        convexHull_mono (coe_subset.2 htl) hxt⟩
    -- inside each of the two affinely independent simplices, `x` is carried by common vertices
    have hs : x ∈ convexHull 𝕜 (s ∩ U : Set E) :=
      ((indep k).convexHull_inter hsk inter_subset_left).ge ⟨hxs, hU⟩
    have ht : x ∈ convexHull 𝕜 (t ∩ U : Set E) :=
      ((indep l).convexHull_inter htl inter_subset_right).ge ⟨hxt, hU⟩
    rw [← coe_inter] at hs ht
    refine convexHull_mono (fun y hy => ?_) (((indep k).convexHull_inter
      (inter_subset_left.trans hsk) (inter_subset_right.trans inter_subset_left)).ge ⟨hs, ht⟩)
    simp only [coe_inter, Set.mem_inter_iff] at hy
    exact ⟨hy.1.1, hy.2.1⟩

/-- The faces of `ofSimplices σ indep inter` are the nonempty subsets of the simplices `σ k`. -/
@[simp]
theorem mem_ofSimplices_faces {σ : ι → Finset E} {indep} {inter} :
    s ∈ (ofSimplices (𝕜 := 𝕜) σ indep inter).faces ↔ s.Nonempty ∧ ∃ k, s ⊆ σ k :=
  TauCeti.PreAbstractSimplicialComplex.mem_ofGenerators.trans (by simp)

/-- The underlying space of `ofSimplices σ indep inter` is the union of the convex hulls of the
simplices `σ k`. -/
theorem space_ofSimplices {σ : ι → Finset E} {indep} {inter} :
    (ofSimplices (𝕜 := 𝕜) σ indep inter).space = ⋃ k, convexHull 𝕜 (σ k : Set E) := by
  ext x
  simp only [mem_space_iff, mem_ofSimplices_faces, Set.mem_iUnion]
  constructor
  · rintro ⟨s, ⟨-, k, hsk⟩, hx⟩
    exact ⟨k, convexHull_mono (coe_subset.2 hsk) hx⟩
  · rintro ⟨k, hx⟩
    exact ⟨σ k, ⟨by simpa using Set.nonempty_of_mem hx, k, subset_rfl⟩, hx⟩

/-- The vertices of `ofSimplices σ indep inter` are the vertices of the simplices `σ k`. -/
theorem vertices_ofSimplices {σ : ι → Finset E} {indep} {inter} :
    (ofSimplices (𝕜 := 𝕜) σ indep inter).vertices = ⋃ k, (σ k : Set E) := by
  ext x
  simp [mem_vertices]

end LinearOrderedField

end Geometry.SimplicialComplex
