/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.LongTurn
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingSide
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.Boundary
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.BoundedArcInjective

import Mathlib.Order.SuccPred.Fin

/-!
# Simplicity of the convex Schwarz--Christoffel boundary

Strictly ordered prevertices and exponents in `(-1, 0)` summing to `-2` give an injective
compactified Schwarz--Christoffel boundary. Nonadjacent bounded sides are disjoint, adjacent
bounded sides meet only at their common corner, and the bounded boundary arc lies strictly above
the horizontal closing side except at its endpoints. The two unbounded arcs occupy opposite sides
of the vertex at infinity. Thus the complete polygon boundary is a Jordan curve.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane
open scoped ComplexOrder

namespace TauCeti

variable {n : ℕ} {a e : Fin (n + 1) → ℝ} {z₀ : UpperHalfPlane}

/-- Under the exponent bounds, every prevertex carries a finite total exponent above `-1`. -/
private lemma neg_one_lt_sum_filter_eq (a e : Fin (n + 1) → ℝ) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
  simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he k).1

/-- The Schwarz--Christoffel boundary is injective between its first and last finite prevertices
under the classical convex-polygon hypotheses. -/
theorem schwarzChristoffelBoundary_injOn_prevertex_interval
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    InjOn (schwarzChristoffelBoundary a e z₀) (Icc (a 0) (a (Fin.last n))) := by
  have hfinite := neg_one_lt_sum_filter_eq a e ha he
  apply schwarzChristoffelBoundary_injOn_prevertex_interval_of_edge_intersections
    a e z₀ ha.monotone hfinite
  intro i j hij z hzi hzj
  by_cases hadj : i.val + 1 = j.val
  · refine ⟨hadj.symm, ?_⟩
    have hcorner : ∑ l with a l = a i.succ, e l ∈ Ioo (-1 : ℝ) 0 := by
      simpa [ha.injective.eq_iff, Finset.filter_eq'] using he i.succ
    exact schwarzChristoffelPolygon_bounded_edgeSet_inter_subset_vertex_of_adjacent
      a e z₀ ha.monotone i j hadj (ha i.castSucc_lt_succ)
      (ha j.castSucc_lt_succ) (hfinite _)
      ⟨hcorner.1, hcorner.2.trans (by norm_num)⟩
      (by simpa [ha.injective.eq_iff, Finset.filter_eq'] using (he i.succ).2.ne)
      (hfinite _) ⟨hzi, hzj⟩
  · have hd := disjoint_schwarzChristoffelPolygon_bounded_edgeSet a e z₀ ha he hsum i j
      (by simp only [Fin.lt_def] at hij; omega)
    exact False.elim (Set.disjoint_left.mp hd hzi hzj)

/-- The unbounded arc to the left of the first prevertex lies strictly below the vertex at
infinity. -/
private lemma vertexAtInfinity_lt_boundary_of_le_first
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) {x : ℝ} (hx : x ≤ a 0) :
    schwarzChristoffelVertexAtInfinity a e z₀ < schwarzChristoffelBoundary a e z₀ x := by
  have hfinite := neg_one_lt_sum_filter_eq a e ha he
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ ↦ ha.monotone k.zero_le
  have hVfirst := schwarzChristoffelVertexAtInfinity_lt_boundary a e z₀ (hfinite _) hfirst hsum
  have hm : schwarzChristoffelBoundary a e z₀ x ∈ schwarzChristoffelBoundary a e z₀ '' Iic (a 0) :=
    ⟨x, hx, rfl⟩
  rw [schwarzChristoffelBoundary_image_Iic a e z₀ (hfinite _) hfirst hS] at hm
  have hseg : schwarzChristoffelBoundary a e z₀ x ∈
      segment ℝ (schwarzChristoffelVertexAtInfinity a e z₀)
        (schwarzChristoffelBoundary a e z₀ (a 0)) := by
    rw [segment_symm]
    exact hm.1
  exact lt_of_le_of_ne (segment_subset_Icc hVfirst.le hseg).1 (Ne.symm hm.2)

/-- The unbounded arc to the right of the last prevertex lies strictly above the vertex at
infinity. -/
private lemma boundary_lt_vertexAtInfinity_of_last_le
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) {x : ℝ} (hx : a (Fin.last n) ≤ x) :
    schwarzChristoffelBoundary a e z₀ x < schwarzChristoffelVertexAtInfinity a e z₀ := by
  have hfinite := neg_one_lt_sum_filter_eq a e ha he
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last n) := fun k _ ↦ ha.monotone k.le_last
  have hVlast := schwarzChristoffelBoundary_lt_vertexAtInfinity a e z₀ (hfinite _) hlast hS
  have hm : schwarzChristoffelBoundary a e z₀ x ∈
      schwarzChristoffelBoundary a e z₀ '' Ici (a (Fin.last n)) := ⟨x, hx, rfl⟩
  rw [schwarzChristoffelBoundary_image_Ici a e z₀ (hfinite _) hlast hS] at hm
  exact lt_of_le_of_ne (segment_subset_Icc hVlast.le hm.1).2 hm.2

/-- The bounded open arc lies strictly above the line through the vertex at infinity. -/
private lemma im_vertexAtInfinity_lt_im_boundary
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) {x : ℝ}
    (hx : x ∈ Ioo (a 0) (a (Fin.last n))) :
    (schwarzChristoffelVertexAtInfinity a e z₀).im < (schwarzChristoffelBoundary a e z₀ x).im := by
  have hfinite := neg_one_lt_sum_filter_eq a e ha he
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ ↦ ha.monotone k.zero_le
  have hVfirst := schwarzChristoffelVertexAtInfinity_lt_boundary a e z₀ (hfinite _) hfirst hsum
  rw [(Complex.lt_def.mp hVfirst).2]
  exact im_schwarzChristoffelBoundary_first_lt a e z₀ ha he hsum hx

/-- The boundary never meets the vertex at infinity at a finite parameter. -/
private lemma boundary_ne_vertexAtInfinity
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) (x : ℝ) :
    schwarzChristoffelBoundary a e z₀ x ≠ schwarzChristoffelVertexAtInfinity a e z₀ := by
  by_cases hx₀ : x ≤ a 0
  · exact (vertexAtInfinity_lt_boundary_of_le_first a e z₀ ha he hsum hx₀).ne'
  by_cases hxn : a (Fin.last n) ≤ x
  · exact (boundary_lt_vertexAtInfinity_of_last_le a e z₀ ha he hsum hxn).ne
  · intro h
    have hi := im_vertexAtInfinity_lt_im_boundary a e z₀ ha he hsum
      ⟨lt_of_not_ge hx₀, lt_of_not_ge hxn⟩
    rw [h] at hi
    exact hi.false

/-- Strictly ordered prevertices with exponents in `(-1, 0)` summing to `-2` give an injective
Schwarz--Christoffel boundary on the one-point compactification of the real line. -/
theorem schwarzChristoffelCompactifiedBoundary_injective
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  have hfinite := neg_one_lt_sum_filter_eq a e ha he
  have hfirst : ∀ k, e k ≠ 0 → a 0 ≤ a k := fun k _ ↦ ha.monotone k.zero_le
  have hlast : ∀ k, e k ≠ 0 → a k ≤ a (Fin.last n) := fun k _ ↦ ha.monotone k.le_last
  have hleft {x : ℝ} (hx : x ≤ a 0) := vertexAtInfinity_lt_boundary_of_le_first a e z₀ ha he hsum hx
  have hright {x : ℝ} (hx : a (Fin.last n) ≤ x) :=
    boundary_lt_vertexAtInfinity_of_last_le a e z₀ ha he hsum hx
  have hmiddle {x : ℝ} (hx : x ∈ Ioo (a 0) (a (Fin.last n))) :=
    im_vertexAtInfinity_lt_im_boundary a e z₀ ha he hsum hx
  rw [schwarzChristoffelCompactifiedBoundary_injective_iff]
  refine ⟨?_, boundary_ne_vertexAtInfinity a e z₀ ha he hsum⟩
  -- Equality on each of the three arcs is already controlled; separate their images.
  have hbounded := schwarzChristoffelBoundary_injOn_prevertex_interval a e z₀ ha he hsum
  have hleftInj := schwarzChristoffelBoundary_injOn_Iic a e z₀ (hfinite _) hfirst
  have hrightInj := schwarzChristoffelBoundary_injOn_Ici a e z₀ (hfinite _) hlast
  suffices h : ∀ x y, x < y →
      schwarzChristoffelBoundary a e z₀ x ≠ schwarzChristoffelBoundary a e z₀ y by
    intro x y hxy
    rcases lt_trichotomy x y with hlt | heq | hgt
    · exact False.elim (h x y hlt hxy)
    · exact heq
    · exact False.elim (h y x hgt hxy.symm)
  intro x y hxy heq
  by_cases hy₀ : y ≤ a 0
  · exact hxy.ne (hleftInj (hxy.le.trans hy₀) hy₀ heq)
  by_cases hxn : a (Fin.last n) ≤ x
  · exact hxy.ne (hrightInj hxn (hxn.trans hxy.le) heq)
  by_cases hx₀ : x ≤ a 0
  · by_cases hyn : a (Fin.last n) ≤ y
    · exact (hleft hx₀).not_ge (heq ▸ (hright hyn).le)
    · have hi := hmiddle ⟨lt_of_not_ge hy₀, lt_of_not_ge hyn⟩
      rw [← heq, ← (Complex.lt_def.mp (hleft hx₀)).2] at hi
      exact hi.false
  · by_cases hyn : a (Fin.last n) ≤ y
    · have hi := hmiddle ⟨lt_of_not_ge hx₀, lt_of_not_ge hxn⟩
      rw [heq, (Complex.lt_def.mp (hright hyn)).2] at hi
      exact hi.false
    · exact hxy.ne (hbounded ⟨(lt_of_not_ge hx₀).le, (lt_of_not_ge hxn).le⟩
        ⟨(lt_of_not_ge hy₀).le, (lt_of_not_ge hyn).le⟩ heq)

/-- The polygon traced by a convex Schwarz--Christoffel boundary is a Jordan curve. The vertex
at infinity may subdivide a straight side; it need not be a genuine corner. -/
theorem isJordanCurve_schwarzChristoffelPolygon_boundary
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, e k ∈ Ioo (-1 : ℝ) 0) (hsum : ∑ k, e k = -2) :
    IsJordanCurve ((schwarzChristoffelPolygon a e z₀).boundary ℝ) := by
  have hfinite := neg_one_lt_sum_filter_eq a e ha he
  have hS : ∑ k, e k < -1 := by rw [hsum]; norm_num
  rw [← range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hS]
  exact isJordanCurve_range_schwarzChristoffelCompactifiedBoundary a e z₀ hfinite hS
    (schwarzChristoffelCompactifiedBoundary_injective a e z₀ ha he hsum)

end TauCeti
