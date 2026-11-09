/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Compactification
public import TauCeti.Analysis.Convex.PolygonalRange
public import TauCeti.Data.Fin.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Basic
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.UnboundedEdge

/-!
# The Schwarz--Christoffel compactified boundary is polygonal

For a nondecreasing finite family of prevertices, the real projective line splits into the
two unbounded intervals and the intervals between consecutive prevertices.  The
Schwarz--Christoffel boundary map carries each finite interval onto its bounded side.  The real
points in the two unbounded intervals trace the two sides incident to the common vertex at infinity
with that vertex omitted; compactification supplies the omitted vertex.

Consequently the range of the compactified boundary map is exactly the boundary of the packaged
polygon.  This identification does not require the polygon to be simple; proving that distinct
nonadjacent sides do not meet is the separate global injectivity problem.

## Main results

* `TauCeti.range_schwarzChristoffelCompactifiedBoundary` -- the compactified boundary map traces
  exactly the boundary of `schwarzChristoffelPolygon`.
* `TauCeti.exists_mem_edgeSet_schwarzChristoffelBoundary_of_mem_Icc`,
  `TauCeti.schwarzChristoffelBoundary_mem_edgeSet_last_of_le` and
  `TauCeti.schwarzChristoffelBoundary_mem_edgeSet_last_prevertex_of_ge` -- each finite parameter is
  sent to the bounded side over its prevertex interval or to the closing side adjacent to the
  nearest end prevertex.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped OnePoint

namespace TauCeti

variable {n : ℕ}

/-- **The compactified Schwarz--Christoffel boundary traces the polygon boundary.**  For ordered
prevertices, integrability at every finite prevertex and decay at infinity make each
closed finite interval map onto its corresponding bounded side.  Each unbounded interval traces
its side with the common vertex at infinity omitted, and the compactified point supplies that
vertex.  Their union is the complete boundary of `schwarzChristoffelPolygon`.

No simplicity hypothesis is needed: this is an equality of ranges even when nonadjacent polygon
sides intersect. -/
theorem range_schwarzChristoffelCompactifiedBoundary (a e : Fin (n + 1) → ℝ)
    (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ j, -1 < ∑ i with a i = a j, e i) (hinfty : ∑ i, e i < -1) :
    Set.range (schwarzChristoffelCompactifiedBoundary a e z₀) =
      (schwarzChristoffelPolygon a e z₀).boundary ℝ := by
  have hfinite' (i : Fin n) : ∀ j, e j ≠ 0 → a j ∉ Ioo (a i.castSucc) (a i.succ) :=
    fun j _ ↦ not_mem_Ioo_castSucc_succ a ha i j
  have hb := fun i : Fin n ↦ schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
    (ha i.castSucc_le_succ) (hfinite' i) (hfinite i.castSucc) (hfinite i.succ)
  have hr := schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last n)
    (hfinite (Fin.last n)) (fun i _ ↦ ha i.le_last) hinfty
  have hl := schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0
    (hfinite 0) (fun i _ ↦ ha i.zero_le) hinfty
  rw [schwarzChristoffelPolygon_boundary]
  exact (range_subset_union_segments a _ _ _ _
    (schwarzChristoffelCompactifiedBoundary_infty a e z₀)
    (schwarzChristoffelCompactifiedBoundary_coe a e z₀) (fun i ↦ (hb i).subset)
    (hr.subset.trans sdiff_subset) (hl.subset.trans sdiff_subset)).antisymm
    (union_segments_subset_range a _ _ _ _
      (schwarzChristoffelCompactifiedBoundary_infty a e z₀)
      (schwarzChristoffelCompactifiedBoundary_coe a e z₀) (fun i ↦ (hb i).superset)
      hr.superset hl.superset)

/-- Every point of the boundary arc over the bounded parameter interval lies on one of the
finite sides. -/
theorem exists_mem_edgeSet_schwarzChristoffelBoundary_of_mem_Icc
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hfinite : ∀ k, -1 < ∑ l with a l = a k, e l) {x : ℝ}
    (hx : x ∈ Icc (a 0) (a (Fin.last (n + 1)))) :
    ∃ i : Fin (n + 1), schwarzChristoffelBoundary a e z₀ x ∈
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc := by
  obtain ⟨i, hi⟩ := exists_mem_Icc_castSucc_succ a (Nat.succ_ne_zero n) hx
  refine ⟨i, ?_⟩
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
    ← schwarzChristoffelBoundary_image_Icc_prevertex a e z₀
      (ha i.castSucc_le_succ) (fun k _ ↦ not_mem_Ioo_castSucc_succ a ha i k)
      (hfinite _) (hfinite _)]
  exact ⟨x, hi, rfl⟩

/-- Parameters left of the first prevertex are sent to the closing side at infinity. -/
theorem schwarzChristoffelBoundary_mem_edgeSet_last_of_le
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (h0 : -1 < ∑ l with a l = a 0, e l) (hS : ∑ k, e k < -1) {x : ℝ}
    (hx : x ≤ a 0) :
    schwarzChristoffelBoundary a e z₀ x ∈
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)) := by
  rw [schwarzChristoffelPolygon_edgeSet_last]
  have hm : schwarzChristoffelBoundary a e z₀ x ∈
      schwarzChristoffelBoundary a e z₀ '' Iic (a 0) := ⟨x, hx, rfl⟩
  rw [schwarzChristoffelBoundary_image_Iic_prevertex a e z₀ 0 h0
    (fun k _ ↦ ha k.zero_le) hS] at hm
  rw [segment_symm]
  exact hm.1

/-- Parameters right of the last prevertex are sent to the closing side at the last vertex. -/
theorem schwarzChristoffelBoundary_mem_edgeSet_last_prevertex_of_ge
    (a e : Fin (n + 2) → ℝ) (z₀ : UpperHalfPlane) (ha : Monotone a)
    (hlast : -1 < ∑ l with a l = a (Fin.last (n + 1)), e l) (hS : ∑ k, e k < -1) {x : ℝ}
    (hx : a (Fin.last (n + 1)) ≤ x) :
    schwarzChristoffelBoundary a e z₀ x ∈
      (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 1)).castSucc := by
  rw [schwarzChristoffelPolygon_edgeSet_last_prevertex]
  have hm : schwarzChristoffelBoundary a e z₀ x ∈
      schwarzChristoffelBoundary a e z₀ '' Ici (a (Fin.last (n + 1))) := ⟨x, hx, rfl⟩
  rw [schwarzChristoffelBoundary_image_Ici_prevertex a e z₀ (Fin.last (n + 1)) hlast
    (fun k _ ↦ ha k.le_last) hS] at hm
  exact hm.1

end TauCeti
