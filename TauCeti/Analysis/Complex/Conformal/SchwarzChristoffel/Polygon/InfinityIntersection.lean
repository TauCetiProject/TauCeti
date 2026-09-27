/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingSide

/-!
# Intersection of the two Schwarz--Christoffel closing sides

When the exponent sum is `-2`, the final finite vertex, the common value at infinity,
and the first finite vertex occur in strict order on a horizontal line. Consequently the
two closing sides meet exactly at their shared endpoint. Their finite boundary
parametrizations omit that endpoint, so the two unbounded real rays have disjoint images.
This is the separation at infinity needed to check that a nonconvex
Schwarz--Christoffel boundary is simple.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped ComplexOrder

namespace TauCeti

variable {n : ℕ}

/-- The two closing sides of a Schwarz--Christoffel polygon meet only at their
shared endpoint, the boundary value at infinity. No upper bound on the individual
exponents is needed. -/
theorem schwarzChristoffelPolygon_closingSides_inter
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2) :
    (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last n).castSucc ∩
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1)) =
        {schwarzChristoffelVertexAtInfinity a e z₀} := by
  obtain ⟨hr, hl⟩ :=
    schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha he hsum
  rw [schwarzChristoffelPolygon_edgeSet_last_prevertex,
    schwarzChristoffelPolygon_edgeSet_last]
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    have hzright := segment_subset_Icc hr.le hz.1
    have hzleft := segment_subset_Icc hl.le hz.2
    exact Set.mem_singleton_iff.mpr (hzright.2.antisymm hzleft.1)
  · rintro z (rfl : z = schwarzChristoffelVertexAtInfinity a e z₀)
    exact ⟨right_mem_segment ℝ _ _, left_mem_segment ℝ _ _⟩

/-- The finite parts of the two unbounded Schwarz--Christoffel boundary rays
are disjoint. Their segment closures touch at the value at infinity, which
neither finite ray attains. -/
@[simp] theorem disjoint_schwarzChristoffelBoundary_unbounded_images
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2) :
    Disjoint
      (schwarzChristoffelBoundary a e z₀ '' Iic (a 0))
      (schwarzChristoffelBoundary a e z₀ '' Ici (a (Fin.last n))) := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hleft := schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0
    (hfinite 0) (fun k _ ↦ ha.monotone k.zero_le) hS
  have hright := schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last n)
    (hfinite _) (fun k _ ↦ ha.monotone k.le_last) hS
  rw [hleft, hright, Set.disjoint_left]
  intro z hzleft hzright
  have hz : z ∈
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last n).castSucc ∩
        (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1)) := by
    rw [schwarzChristoffelPolygon_edgeSet_last_prevertex,
      schwarzChristoffelPolygon_edgeSet_last]
    exact ⟨hzright.1, by simpa only [segment_symm] using hzleft.1⟩
  rw [schwarzChristoffelPolygon_closingSides_inter a e z₀ ha he hsum] at hz
  exact hzleft.2 (Set.mem_singleton_iff.mp hz)

end TauCeti
