/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.Join
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Between
import TauCeti.Analysis.Convex.Combination
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Convex.Join

/-!
# Cones of geometric simplicial complexes

Let `K` be a geometric simplicial complex in a module `E` over an ordered field and let `p` be a
point. The *cone* `pK` has as faces the faces of `K`, the faces of `K` with `p` adjoined, and the
vertex `{p}`. It is a simplicial complex when `p` "sees" `|K|` injectively: `p ∉ |K|`, and
every segment from `p` to a point of `|K|` meets `|K|` only at that endpoint
(`Geometry.SimplicialComplex.IsConeApex`). Under this condition the apex lies outside the affine
span of every face of `K` (`IsConeApex.notMem_affineSpan`), the cone glues along common faces, it
contains `K` as a subcomplex, and its underlying space is the convex join of `p` with `|K|`
together with `p` itself (the apex matters only when `K` is empty).

The main application is coning a triangulated boundary of a convex body to an interior point. If
`C` is convex and `K` triangulates its intrinsic frontier, every point of the intrinsic interior
of `C` is a cone apex for `K` (`IsConeApex.of_space_eq_intrinsicFrontier`). If moreover `C` is
compact, the cone triangulates all of `C` (`space_cone_of_space_eq_intrinsicFrontier`) and
retains `K` as its boundary triangulation. This is the coning step in the inductive construction
of simplicial subdivisions of convex polytopes compatible with prescribed boundary
triangulations.

## Main definitions

* `Geometry.SimplicialComplex.IsConeApex`: `p` is outside `|K|` and each segment from `p` meets
  `|K|` at most in its far endpoint.
* `Geometry.SimplicialComplex.cone`: the cone on `K` with apex `p`.

## Main results

* `Geometry.SimplicialComplex.IsConeApex.notMem_affineSpan`: a cone apex lies outside the affine
  span of every face.
* `Geometry.SimplicialComplex.vertices_cone`: the vertices of the cone are the apex and the
  vertices of `K`.
* `Geometry.SimplicialComplex.space_cone`: `|pK| = {p} ∪ convexJoin {p} |K|`.
* `Geometry.SimplicialComplex.le_cone` and `mem_cone_faces_iff_of_notMem`: the faces of the cone
  not containing the apex are exactly the faces of `K`.
* `Geometry.SimplicialComplex.space_cone_of_space_eq_intrinsicFrontier`: coning a triangulation
  of the intrinsic frontier of a compact convex set to an intrinsic interior point triangulates
  the whole set.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 1 (joins and cones) and Chapter 2 (simplicial complexes).
-/

public section

open Finset Set TauCeti

namespace Geometry.SimplicialComplex

section OrderedField

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E] {K : SimplicialComplex 𝕜 E} {p x : E} {s t : Finset E}

/-- A point `p` is a *cone apex* for a geometric simplicial complex `K` if `p ∉ |K|` and every
segment from `p` to a point `y ∈ |K|` meets `|K|` only at `y`. These are the conditions under
which joining `p` to the faces of `K` gives a simplicial complex, the cone `K.cone p h`. -/
structure IsConeApex (K : SimplicialComplex 𝕜 E) (p : E) : Prop where
  /-- The apex is not in the underlying space. -/
  notMem_space : p ∉ K.space
  /-- A segment from the apex to a point `y` of the underlying space meets it only at `y`. -/
  eq_of_mem_segment ⦃x y : E⦄ : x ∈ K.space → y ∈ K.space → x ∈ segment 𝕜 p y → x = y

namespace IsConeApex

variable (h : K.IsConeApex p)
include h

omit [IsStrictOrderedRing 𝕜] in
/-- A cone apex is not a vertex of any face. -/
theorem notMem_of_mem_faces (hs : s ∈ K.faces) : p ∉ s :=
  fun hp => h.notMem_space (K.subset_space hs hp)

/-- A cone apex lies outside the affine span of every face, so adjoining it to a face keeps the
vertices affinely independent. -/
theorem notMem_affineSpan (hs : s ∈ K.faces) : p ∉ affineSpan 𝕜 (s : Set E) := by
  intro hp
  have hne := K.nonempty_of_mem_faces hs
  set c := s.centroid 𝕜 id
  obtain ⟨ε, hε, hq⟩ := s.exists_lineMap_centroid_mem_convexHull hne hp
  have hc : c ∈ K.space := convexHull_subset_space hs (s.centroid_mem_convexHull hne)
  have hcp : p ≠ c := fun hpc => h.notMem_space (hpc ▸ hc)
  -- the centroid lies on the segment from `p` to a point of the face beyond it
  have hcq : c ∈ segment 𝕜 p (AffineMap.lineMap p c (1 + ε)) := by
    rw [segment_eq_image_lineMap]
    refine ⟨(1 + ε)⁻¹, ⟨(inv_pos.2 (by linarith)).le, inv_le_one_of_one_le₀ (by linarith)⟩, ?_⟩
    rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (by linarith),
      AffineMap.lineMap_apply_one]
  have hcq' := h.eq_of_mem_segment hc (convexHull_subset_space hs hq) hcq
  rw [← AffineMap.lineMap_apply_one (k := 𝕜) p c] at hcq'
  have := AffineMap.lineMap_injective 𝕜 hcp hcq'
  linarith

/-- A point of `|K|` in the convex hull of a face of `K` with the apex adjoined already lies in the
convex hull of that face. -/
private theorem mem_convexHull_of_mem_convexHull_insert (ht : t = ∅ ∨ t ∈ K.faces)
    (hx : x ∈ convexHull 𝕜 (insert p (t : Set E))) (hxK : x ∈ K.space) :
    x ∈ convexHull 𝕜 (t : Set E) := by
  rcases mem_convexHull_insert.1 hx with rfl | ⟨y, hy, hxy⟩
  · exact (h.notMem_space hxK).elim
  rcases ht with rfl | ht
  · simp at hy
  rwa [h.eq_of_mem_segment hxK (convexHull_subset_space ht hy) hxy]

/-- Two faces of the cone through the apex meet along the cone on the common face. -/
private theorem convexHull_insert_inter_subset (hs : s = ∅ ∨ s ∈ K.faces)
    (ht : t = ∅ ∨ t ∈ K.faces) :
    convexHull 𝕜 (insert p (s : Set E)) ∩ convexHull 𝕜 (insert p (t : Set E)) ⊆
      convexHull 𝕜 (insert p (s ∩ t : Set E)) := by
  have hp : p ∈ convexHull 𝕜 (insert p (s ∩ t : Set E)) :=
    subset_convexHull 𝕜 _ (mem_insert _ _)
  rintro x ⟨hxs, hxt⟩
  rcases eq_or_ne x p with rfl | hxp
  · exact hp
  obtain ⟨y, hy, hxy⟩ := (mem_convexHull_insert.1 hxs).resolve_left hxp
  obtain ⟨z, hz, hxz⟩ := (mem_convexHull_insert.1 hxt).resolve_left hxp
  rcases hs with rfl | hs
  · simp at hy
  rcases ht with rfl | ht
  · simp at hz
  have hyK := convexHull_subset_space hs hy
  have hzK := convexHull_subset_space ht hz
  -- `y` and `z` lie on the same ray from `p`, so one of them lies on the segment to the other
  rw [mem_segment_iff_wbtw] at hxy hxz
  have hray : SameRay 𝕜 (y -ᵥ p) (z -ᵥ p) :=
    hxy.sameRay_vsub_left.symm.trans hxz.sameRay_vsub_left fun h0 =>
      (hxp (vsub_eq_zero_iff_eq.1 h0)).elim
  have hyz : y = z := by
    rcases wbtw_total_of_sameRay_vsub_left hray with hw | hw
    · exact h.eq_of_mem_segment hyK hzK (mem_segment_iff_wbtw.2 hw)
    · exact (h.eq_of_mem_segment hzK hyK (mem_segment_iff_wbtw.2 hw)).symm
  subst hyz
  have hy' : y ∈ convexHull 𝕜 (insert p (s ∩ t : Set E)) :=
    convexHull_mono (subset_insert _ _) (K.inter_subset_convexHull hs ht ⟨hy, hz⟩)
  exact (convex_convexHull 𝕜 _).segment_subset hp hy' (mem_segment_iff_wbtw.2 hxy)

end IsConeApex

section IntrinsicFrontier

variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousConstSMul 𝕜 E] {C : Set E}

/-- If `K` triangulates the intrinsic frontier of a convex set `C`, every point of the intrinsic
interior of `C` is a cone apex for `K`. -/
theorem IsConeApex.of_space_eq_intrinsicFrontier (hC : Convex 𝕜 C)
    (hK : K.space = intrinsicFrontier 𝕜 C) (hp : p ∈ intrinsicInterior 𝕜 C) :
    K.IsConeApex p where
  notMem_space hpK := by
    rw [hK, ← intrinsicClosure_sdiff_intrinsicInterior] at hpK
    exact hpK.2 hp
  eq_of_mem_segment x y hx hy hxy := by
    by_contra hxy'
    rw [hK, ← intrinsicClosure_sdiff_intrinsicInterior] at hx hy
    have hpx : p ≠ x := fun hpx => hx.2 (hpx ▸ hp)
    exact hx.2 (hC.openSegment_intrinsicInterior_intrinsicClosure_subset_intrinsicInterior hp hy.1
      (mem_openSegment_of_ne_left_right hpx (Ne.symm hxy') hxy))

end IntrinsicFrontier

variable [DecidableEq E]

/-- A face of the cone through the apex and a face of `K` meet along a common face. -/
private theorem IsConeApex.convexHull_inter_subset_of_mem (h : K.IsConeApex p)
    (hs : s.erase p = ∅ ∨ s.erase p ∈ K.faces) (ht : t ∈ K.faces) :
    convexHull 𝕜 (s : Set E) ∩ convexHull 𝕜 (t : Set E) ⊆ convexHull 𝕜 (s ∩ t : Set E) := by
  rintro x ⟨hxs, hxt⟩
  have hxs' : x ∈ convexHull 𝕜 (insert p (s.erase p : Set E)) := by
    refine convexHull_mono ?_ hxs
    rw [← coe_insert]
    exact_mod_cast insert_erase_subset p s
  have hx := h.mem_convexHull_of_mem_convexHull_insert hs hxs' (convexHull_subset_space ht hxt)
  rcases hs with hs | hs
  · simp [hs] at hx
  refine convexHull_mono ?_ (K.inter_subset_convexHull hs ht ⟨hx, hxt⟩)
  exact_mod_cast inter_subset_inter_right (erase_subset p s)

omit [IsStrictOrderedRing 𝕜] in
/-- A nonempty finite set avoiding `p` whose vertices other than `p` are empty or a face of `K`
is a face of `K`. -/
private theorem mem_faces_of_notMem (hne : s.Nonempty)
    (hs : s.erase p = ∅ ∨ s.erase p ∈ K.faces) (hp : p ∉ s) : s ∈ K.faces := by
  rw [erase_eq_of_notMem hp] at hs
  exact hs.resolve_left hne.ne_empty

/-- The cone `pK` on a simplicial complex `K` with apex `p`. Its faces are the nonempty finite sets
whose vertices other than `p` form a face of `K` or are empty: the faces of `K`, the faces of `K`
with `p` adjoined, and the vertex `{p}`. -/
def cone (K : SimplicialComplex 𝕜 E) (p : E) (h : K.IsConeApex p) : SimplicialComplex 𝕜 E where
  faces := {s | s.Nonempty ∧ (s.erase p = ∅ ∨ s.erase p ∈ K.faces)}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsK⟩
    refine ⟨hs, fun t hts ht => ⟨ht, ?_⟩⟩
    have hsub : t.erase p ⊆ s.erase p := erase_subset_erase p hts
    rcases (t.erase p).eq_empty_or_nonempty with he | he
    · exact .inl he
    rcases hsK with hsK | hsK
    · exact (he.ne_empty (subset_empty.1 (hsK ▸ hsub))).elim
    · exact .inr (K.down_closed hsK hsub he)
  indep := by
    rintro s ⟨-, hsK⟩
    have hind : AffineIndepOn 𝕜 id (insert p (s.erase p : Set E)) := by
      rcases hsK with hsK | hsK
      · rw [hsK, coe_empty, insert_empty_eq]
        exact affineIndependent_of_subsingleton 𝕜 _
      · exact AffineIndepOn.id_insert (K.indep hsK) (h.notMem_affineSpan hsK)
    exact AffineIndependent.mono hind (by exact_mod_cast insert_erase_subset p s)
  inter_subset_convexHull := by
    rintro s t ⟨hsne, hs⟩ ⟨htne, ht⟩
    by_cases hpt : p ∈ t
    · by_cases hps : p ∈ s
      · rw [← insert_erase hps, ← insert_erase hpt, coe_insert, coe_insert,
          ← Set.insert_inter_distrib]
        exact h.convexHull_insert_inter_subset hs ht
      · rw [Set.inter_comm, Set.inter_comm (s : Set E)]
        exact h.convexHull_inter_subset_of_mem ht (mem_faces_of_notMem hsne hs hps)
    · exact h.convexHull_inter_subset_of_mem hs (mem_faces_of_notMem htne ht hpt)


variable (h : K.IsConeApex p)

@[simp]
theorem mem_cone_faces :
    s ∈ (K.cone p h).faces ↔ s.Nonempty ∧ (s.erase p = ∅ ∨ s.erase p ∈ K.faces) :=
  Iff.rfl

/-- The faces of the cone not containing the apex are exactly the faces of `K`. -/
theorem mem_cone_faces_iff_of_notMem (hs : p ∉ s) : s ∈ (K.cone p h).faces ↔ s ∈ K.faces := by
  rw [mem_cone_faces, erase_eq_of_notMem hs]
  exact ⟨fun ⟨hne, hs⟩ => hs.resolve_left hne.ne_empty,
    fun hs => ⟨K.nonempty_of_mem_faces hs, .inr hs⟩⟩

/-- The cone contains `K` as a subcomplex. -/
theorem le_cone : K ≤ K.cone p h := fun _ hs =>
  (mem_cone_faces_iff_of_notMem h (h.notMem_of_mem_faces hs)).2 hs

/-- Adjoining the apex to a face of `K` gives a face of the cone. -/
theorem insert_mem_cone_faces (hs : s ∈ K.faces) : insert p s ∈ (K.cone p h).faces := by
  rw [mem_cone_faces, erase_insert (h.notMem_of_mem_faces hs)]
  exact ⟨insert_nonempty _ _, .inr hs⟩

/-- The vertices of the cone are the apex together with the vertices of `K`. -/
@[simp]
theorem vertices_cone : (K.cone p h).vertices = insert p K.vertices := by
  ext x
  rw [mem_vertices, Set.mem_insert_iff, mem_vertices]
  rcases eq_or_ne x p with rfl | hxp
  · simp
  rw [mem_cone_faces_iff_of_notMem h (Finset.notMem_singleton.2 hxp.symm)]
  simp [hxp]

/-- The apex is a vertex of the cone. -/
theorem mem_vertices_cone : p ∈ (K.cone p h).vertices := by
  simp

/-- The cone has finitely many faces exactly when `K` does. -/
theorem finite_faces_cone_iff : (K.cone p h).faces.Finite ↔ K.faces.Finite := by
  refine ⟨fun hK => hK.subset (le_cone h), fun hK => ?_⟩
  refine (((hK.image (insert p)).union hK).insert {p}).subset fun s ⟨hne, hs⟩ => ?_
  by_cases hps : p ∈ s
  · rcases hs with hs | hs
    · left
      rw [← insert_erase hps, hs, insert_empty]
    · exact .inr (.inl ⟨_, hs, insert_erase hps⟩)
  · rw [erase_eq_of_notMem hps] at hs
    exact .inr (.inr (hs.resolve_left hne.ne_empty))

/-- The underlying space of the cone is the convex join of the apex with `|K|`, together with the
apex itself (which matters only when `K` is empty). -/
theorem space_cone : (K.cone p h).space = insert p (convexJoin 𝕜 {p} K.space) := by
  refine Subset.antisymm (fun x hx => ?_) fun x hx => ?_
  · obtain ⟨s, ⟨-, hs⟩, hxs⟩ := mem_space_iff.1 hx
    have hxs' : x ∈ convexHull 𝕜 (insert p (s.erase p : Set E)) :=
      convexHull_mono (by exact_mod_cast insert_erase_subset p s) hxs
    rcases mem_convexHull_insert.1 hxs' with hxp | ⟨y, hy, hxy⟩
    · exact .inl hxp
    rcases hs with hs | hs
    · simp [hs] at hy
    exact .inr (mem_convexJoin.2 ⟨p, rfl, y, convexHull_subset_space hs hy, hxy⟩)
  rcases hx with hx | hx
  · rw [hx]
    exact (K.cone p h).vertices_subset_space (mem_vertices_cone h)
  obtain ⟨a, ha, y, hy, hxy⟩ := mem_convexJoin.1 hx
  rw [mem_singleton_iff] at ha
  rw [ha] at hxy
  obtain ⟨s, hs, hys⟩ := mem_space_iff.1 hy
  refine mem_space_iff.2 ⟨insert p s, insert_mem_cone_faces h hs, ?_⟩
  rw [coe_insert]
  exact (convex_convexHull 𝕜 _).segment_subset (subset_convexHull 𝕜 _ (mem_insert _ _))
    (convexHull_mono (Set.subset_insert _ _) hys) hxy

end OrderedField

section Real

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [ContinuousSMul ℝ E] [T2Space E] [DecidableEq E] {K : SimplicialComplex ℝ E} {C : Set E} {p : E}

/-- Coning a triangulation of the intrinsic frontier of a compact convex set `C` to a point of the
intrinsic interior of `C` triangulates `C`: every point of `C` is either the apex or lies on a
segment from the apex to a point of the intrinsic frontier. -/
theorem space_cone_of_space_eq_intrinsicFrontier (hCc : IsCompact C) (hC : Convex ℝ C)
    (hK : K.space = intrinsicFrontier ℝ C) (hp : p ∈ intrinsicInterior ℝ C) :
    (K.cone p (.of_space_eq_intrinsicFrontier hC hK hp)).space = C := by
  have hpC : p ∈ C := intrinsicInterior_subset hp
  have hFC : intrinsicFrontier ℝ C ⊆ C := intrinsicFrontier_subset hCc.isClosed
  rw [space_cone, hK]
  refine Subset.antisymm (insert_subset hpC ?_) fun x hx => ?_
  · rw [convexJoin_singleton_left]
    exact iUnion₂_subset fun y hy => hC.segment_subset hpC (hFC hy)
  by_cases hxp : x = p
  · rw [hxp]
    exact mem_insert _ _
  refine .inr (mem_convexJoin.2 ⟨p, rfl, ?_⟩)
  obtain ⟨T, hT1, hfT⟩ := hCc.exists_lineMap_mem_intrinsicFrontier hpC hx hxp
  refine ⟨_, hfT, ?_⟩
  rw [segment_eq_image_lineMap]
  refine ⟨T⁻¹, ⟨inv_nonneg.2 (by linarith), inv_le_one_of_one_le₀ hT1⟩, ?_⟩
  rw [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (by linarith : T ≠ 0),
    AffineMap.lineMap_apply_one]

end Real

end Geometry.SimplicialComplex
