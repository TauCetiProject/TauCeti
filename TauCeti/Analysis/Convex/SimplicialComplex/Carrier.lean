/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Convex.OpenSimplex

/-!
# The open simplex carrying a point of a geometric simplicial complex

The open simplices of a geometric simplicial complex `K`, the intrinsic interiors of the convex
hulls of its faces, partition its underlying space `|K|`: every point of `|K|` lies in the open
simplex of exactly one face of `K`, classically called its *carrier*
(`Geometry.SimplicialComplex.existsUnique_mem_intrinsicInterior`). More precisely, a point of a
simplex lies in the open simplex of one of the faces of that simplex
(`Geometry.SimplicialComplex.exists_mem_faces_subset_mem_intrinsicInterior`), and two faces whose
open simplices meet are equal (`Geometry.SimplicialComplex.eq_of_mem_intrinsicInterior`).

This is the cell structure through which two complexes with a common underlying space are compared
in `TauCeti.Analysis.Convex.SimplicialComplex.CommonSubdivision`.

## Main results

* `Geometry.SimplicialComplex.exists_mem_faces_subset_mem_intrinsicInterior`: a point of a simplex
  lies in the open simplex of one of its faces.
* `Geometry.SimplicialComplex.eq_of_mem_intrinsicInterior`: distinct faces have disjoint open
  simplices.
* `Geometry.SimplicialComplex.existsUnique_mem_intrinsicInterior`: every point of `|K|` lies in
  the open simplex of exactly one face.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (simplicial complexes and their open simplices).
-/

public section

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {s t : Finset E} {x : E}

/-- Every point of a simplex of a geometric simplicial complex lies in the open simplex of one of
its faces. -/
theorem exists_mem_faces_subset_mem_intrinsicInterior (hs : s ∈ K.faces)
    (hx : x ∈ convexHull ℝ (s : Set E)) :
    ∃ t ∈ K.faces, t ⊆ s ∧ x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨w, hw₀, hw₁, rfl⟩ := Finset.mem_convexHull'.1 hx
  -- The face spanned by the vertices of positive weight.
  set t := s.filter fun y => w y ≠ 0
  have ht₁ : ∑ y ∈ t, w y = 1 := by rw [Finset.sum_filter_ne_zero, hw₁]
  have hts : t ⊆ s := Finset.filter_subset _ _
  have htne : t.Nonempty := Finset.nonempty_of_sum_ne_zero (ht₁ ▸ one_ne_zero)
  have ht : t ∈ K.faces := K.down_closed hs hts htne
  refine ⟨t, ht, hts, ?_⟩
  -- The convex hull of `t` is that of the affinely independent inclusion `t → E`.
  rw [← Finset.setOfPred_mem, ← Subtype.range_coe_subtype,
    (K.indep ht).mem_intrinsicInterior_convexHull_iff]
  have ht₁' : ∑ y : t, w y = 1 := by rw [Finset.sum_coe_sort t w, ht₁]
  refine ⟨fun y => w y, fun y => (hw₀ _ (Finset.mem_filter.1 y.2).1).lt_of_ne'
    (Finset.mem_filter.1 y.2).2, ht₁', ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ ht₁',
    Finset.sum_coe_sort t fun y => w y • y]
  exact Finset.sum_filter_of_ne fun y _ hy => left_ne_zero_of_smul hy

/-- **The open simplices of a complex are disjoint.** A point lies in the intrinsic interior of
at most one simplex of a geometric simplicial complex. -/
theorem eq_of_mem_intrinsicInterior (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hxs : x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hxt : x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E))) : s = t := by
  -- A point of the open simplex of `s` lying in the simplex of `t` forces `s ⊆ t`.
  have key : ∀ {s t : Finset E}, s ∈ K.faces → t ∈ K.faces →
      x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) →
      x ∈ intrinsicInterior ℝ (convexHull ℝ (t : Set E)) → s ⊆ t := by
    intro s t hs ht hxs hxt
    have hst := K.inter_subset_convexHull hs ht
      ⟨intrinsicInterior_subset hxs, intrinsicInterior_subset hxt⟩
    rw [← Finset.setOfPred_mem, ← Subtype.range_coe_subtype] at hxs
    have h := (K.indep hs).eq_univ_of_mem_intrinsicInterior_convexHull hxs
      (s := {y | (y : E) ∈ t}) (by convert hst using 2; ext; simp [and_comm])
    intro y hy
    have hy' : (⟨y, hy⟩ : s) ∈ {y : s | (y : E) ∈ t} := h ▸ mem_univ _
    simpa using hy'
  exact (key hs ht hxs hxt).antisymm (key ht hs hxt hxs)

/-- Distinct faces of a geometric simplicial complex have disjoint open simplices. -/
theorem pairwise_disjoint_intrinsicInterior (K : SimplicialComplex ℝ E) :
    Pairwise fun s t : K.faces => Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
      (intrinsicInterior ℝ (convexHull ℝ (t : Set E))) := by
  intro s t hst
  exact Set.disjoint_left.mpr fun x hxs hxt =>
    hst (Subtype.ext (eq_of_mem_intrinsicInterior s.2 t.2 hxs hxt))

/-- The open simplex of a face outside a subcomplex misses the subcomplex's underlying space. -/
theorem disjoint_intrinsicInterior_space_of_not_mem {A : SimplicialComplex ℝ E}
    (hAK : A ≤ K) (hs : s ∈ K.faces) (hsA : s ∉ A.faces) :
    Disjoint (intrinsicInterior ℝ (convexHull ℝ (s : Set E))) A.space := by
  refine Set.disjoint_left.mpr fun x hxs hxA => ?_
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxA
  obtain ⟨u, hu, -, hxu⟩ := exists_mem_faces_subset_mem_intrinsicInterior ht hxt
  exact hsA (eq_of_mem_intrinsicInterior hs (hAK hu) hxs hxu ▸ hu)

/-- **The carrier of a point.** Every point of the underlying space of a geometric simplicial
complex lies in the open simplex of exactly one of its faces. -/
theorem existsUnique_mem_intrinsicInterior (hx : x ∈ K.space) :
    ∃! s, s ∈ K.faces ∧ x ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)) := by
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.1 hx
  obtain ⟨t, ht, -, hxt⟩ := exists_mem_faces_subset_mem_intrinsicInterior hs hxs
  exact ⟨t, ⟨ht, hxt⟩, fun u ⟨hu, hxu⟩ => eq_of_mem_intrinsicInterior hu ht hxu hxt⟩

end Geometry.SimplicialComplex
