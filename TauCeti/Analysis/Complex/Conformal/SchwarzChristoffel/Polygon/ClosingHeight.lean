/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.EdgeIntersection.Criterion
import TauCeti.Analysis.Complex.PlaneSeparation.Segment

/-!
# Closing-side separation from vertex heights

For a Schwarz--Christoffel polygon with possibly reentrant corners, strict height of every
intermediate vertex above the horizontal closing line keeps the bounded sides away from
both closing sides except at their prescribed endpoints. Together with a bounded-side
intersection check, this proves simplicity of the compactified boundary. The height
condition is finite and geometric, so it can be checked independently of the analytic
construction of the vertices.

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

/-- If every intermediate vertex is strictly above the line through the first and last
vertices, a bounded side can meet that line only at one of those two endpoints. -/
theorem schwarzChristoffelPolygon_bounded_edgeSet_eq_endpoint_of_im_le
    (a e : Fin (n + 3) → ℝ) (z₀ : UpperHalfPlane)
    (hends : (schwarzChristoffelVertex a e z₀ (Fin.last (n + 2))).im =
      (schwarzChristoffelVertex a e z₀ 0).im)
    (hheight : ∀ k : Fin (n + 3), k ≠ 0 → k ≠ Fin.last (n + 2) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im)
    (i : Fin (n + 2)) {z : ℂ}
    (hz : z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
    (hzim : z.im ≤ (schwarzChristoffelVertex a e z₀ 0).im) :
    z = schwarzChristoffelVertex a e z₀ 0 ∨
      z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 2)) := by
  let V := schwarzChristoffelVertex a e z₀
  have hge (k : Fin (n + 3)) : (V 0).im ≤ (V k).im := by
    rcases eq_or_ne k 0 with rfl | hk
    · exact le_rfl
    rcases eq_or_ne k (Fin.last (n + 2)) with rfl | hlast
    · exact hends.symm.le
    · exact (hheight k hk hlast).le
  rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc] at hz
  by_cases hi : i.succ = Fin.last (n + 2)
  · have hcast0 : i.castSucc ≠ (0 : Fin (n + 3)) := by
      intro h
      have hi' := congrArg Fin.val hi
      have h' := congrArg Fin.val h
      simp only [Fin.val_succ, Fin.val_last] at hi'
      simp only [Fin.val_castSucc, Fin.val_zero] at h'
      omega
    have hcastlast : i.castSucc ≠ Fin.last (n + 2) :=
      (Fin.castSucc_lt_last i).ne
    have hzlast := eq_left_of_mem_segment_of_im_le_of_lt
      (u := V (Fin.last (n + 2))) (v := V i.castSucc)
      (by rw [hends]) (hheight i.castSucc hcast0 hcastlast)
      (by simpa only [← hi, segment_symm] using hz) hzim
    exact Or.inr hzlast
  · have hzfirst := eq_left_of_mem_segment_of_im_le_of_lt
      (u := V i.castSucc) (v := V i.succ)
      (hge i.castSucc) (hheight i.succ (Fin.succ_ne_zero i) hi) hz hzim
    rcases eq_or_ne i.castSucc 0 with h0 | h0
    · exact Or.inl (hzfirst.trans (congrArg V h0))
    · have hcastlast : i.castSucc ≠ Fin.last (n + 2) :=
        (Fin.castSucc_lt_last i).ne
      have hlt := hheight i.castSucc h0 hcastlast
      dsimp only [V] at hzfirst
      rw [← hzfirst] at hlt
      exact False.elim (not_lt_of_ge hzim hlt)

/-- Strict intermediate vertex heights discharge both closing-side intersection
hypotheses of the polygonal simplicity criterion. The exponents may be positive. -/
theorem schwarzChristoffelPolygon_closing_intersections_of_vertex_heights
    (a e : Fin (n + 3) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2)
    (hheight : ∀ k : Fin (n + 3), k ≠ 0 → k ≠ Fin.last (n + 2) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im) :
    (∀ (i : Fin (n + 2)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 3)) →
        z = schwarzChristoffelVertex a e z₀ 0) ∧
    (∀ (i : Fin (n + 2)) (z : ℂ),
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc →
      z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ (Fin.last (n + 2)).castSucc →
        z = schwarzChristoffelVertex a e z₀ (Fin.last (n + 2))) := by
  obtain ⟨hr, hl⟩ :=
    schwarzChristoffelVertex_last_lt_vertexAtInfinity_lt_vertex_zero a e z₀ ha he hsum
  have hends : (schwarzChristoffelVertex a e z₀ (Fin.last (n + 2))).im =
      (schwarzChristoffelVertex a e z₀ 0).im :=
    (Complex.lt_def.mp hr).2.trans (Complex.lt_def.mp hl).2
  constructor
  · intro i z hz hzleft
    rw [schwarzChristoffelPolygon_edgeSet_last] at hzleft
    have hzbound := segment_subset_Icc hl.le hzleft
    have hzim : z.im ≤ (schwarzChristoffelVertex a e z₀ 0).im := by
      rw [← (Complex.lt_def.mp hl).2]
      exact (Complex.le_def.mp hzbound.1).2.ge
    rcases schwarzChristoffelPolygon_bounded_edgeSet_eq_endpoint_of_im_le
      a e z₀ hends hheight i hz hzim with hfirst | hlast
    · exact hfirst
    · have hle := hzbound.1
      rw [hlast] at hle
      exact False.elim (hr.not_ge hle)
  · intro i z hz hzright
    rw [schwarzChristoffelPolygon_edgeSet_last_prevertex] at hzright
    have hzbound := segment_subset_Icc hr.le hzright
    have hzim : z.im ≤ (schwarzChristoffelVertex a e z₀ 0).im := by
      rw [← hends]
      exact (Complex.le_def.mp hzbound.1).2.ge
    rcases schwarzChristoffelPolygon_bounded_edgeSet_eq_endpoint_of_im_le
      a e z₀ hends hheight i hz hzim with hfirst | hlast
    · have hle := hzbound.2
      rw [hfirst] at hle
      exact False.elim (hl.not_ge hle)
    · exact hlast

/-- A bounded-side intersection check and strict interior vertex heights make the
compactified Schwarz--Christoffel boundary simple, including for reentrant corners. -/
theorem schwarzChristoffelCompactifiedBoundary_injective_of_bounded_intersections_of_vertex_heights
    (a e : Fin (n + 3) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2)
    (hheight : ∀ k : Fin (n + 3), k ≠ 0 → k ≠ Fin.last (n + 2) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im)
    (hbounded : ∀ (i j : Fin (n + 2)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  have hfinite (k : Fin (n + 3)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  obtain ⟨hleft, hright⟩ :=
    schwarzChristoffelPolygon_closing_intersections_of_vertex_heights
      a e z₀ ha he hsum hheight
  exact schwarzChristoffelCompactifiedBoundary_injective_of_edge_intersections
    a e z₀ ha hfinite hsum hbounded hleft hright

end TauCeti
