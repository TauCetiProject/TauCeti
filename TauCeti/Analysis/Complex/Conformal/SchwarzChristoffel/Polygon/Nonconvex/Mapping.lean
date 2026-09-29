/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.VertexSeparation
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.ClosingHeight
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.FilledInterior
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.EdgeIntersection.Converse

/-!
# A Schwarz--Christoffel map onto a nonconvex polygon

Finite signed-height checks on the Schwarz--Christoffel vertices certify that the bounded sides
do not cross and that the bounded arc stays above the closing side. With interior turning
exponents in `(-1, 1) \ {0}`, endpoint exponents greater than `-1`, and total exponent `-2`,
these checks make the compactified boundary a Jordan curve.
The primitive then maps the upper half-plane bijectively onto the filled interior of that polygon.
Positive exponents, and hence reentrant corners, are allowed.

## References

* L. Ahlfors, *Complex Analysis*, Chapter 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Chapter 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- Signed vertex separation for nonadjacent bounded sides, together with strict heights above
the closing line, makes the entire compactified Schwarz--Christoffel boundary injective. -/
theorem schwarzChristoffelCompactifiedBoundary_injective_of_vertex_separation_of_vertex_heights
    (a e : Fin (n + 3) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2)
    (hcorner : ∀ k : Fin (n + 2), k.val + 1 < n + 2 → e k.succ < 1)
    (hne : ∀ k : Fin (n + 2), k.val + 1 < n + 2 → e k.succ ≠ 0)
    (hsep : ∀ (i j : Fin (n + 2)), i.val + 1 < j.val →
      let c := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
      let u := schwarzChristoffelVertex a e z₀ i.castSucc
      let v := schwarzChristoffelVertex a e z₀ j.castSucc
      let w := schwarzChristoffelVertex a e z₀ j.succ
      (0 < (c * (v - u)).im ∧ 0 < (c * (w - u)).im) ∨
        ((c * (v - u)).im < 0 ∧ (c * (w - u)).im < 0))
    (hheight : ∀ k : Fin (n + 3), k ≠ 0 → k ≠ Fin.last (n + 2) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im) :
    Function.Injective (schwarzChristoffelCompactifiedBoundary a e z₀) := by
  have hfinite (k : Fin (n + 3)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  have harc := schwarzChristoffelBoundary_injOn_prevertex_interval_of_vertex_separation
    a e z₀ ha he hcorner hne hsep
  have hbounded : ∀ (i j : Fin (n + 2)), i < j →
      ∀ z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc,
        z ∈ (schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc →
          j.val = i.val + 1 ∧ z = schwarzChristoffelVertex a e z₀ i.succ := by
    intro i j hij z hzi hzj
    exact schwarzChristoffelPolygon_bounded_edges_adjacent_and_eq_vertex_of_injOn
      a e z₀ ha hfinite harc i j hij z hzi hzj
  exact schwarzChristoffelCompactifiedBoundary_injective_of_bounded_intersections_of_vertex_heights
    a e z₀ ha he hsum hheight hbounded

/-- Under finite vertex-separation and closing-height checks, the Schwarz--Christoffel primitive
maps the upper half-plane bijectively onto the filled polygon interior. The exponents may be
positive at reentrant corners. -/
theorem bijOn_schwarzChristoffelPrimitive_filledHull_sdiff_of_vertex_separation_of_vertex_heights
    (a e : Fin (n + 3) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k) (hsum : ∑ k, e k = -2)
    (hcorner : ∀ k : Fin (n + 2), k.val + 1 < n + 2 → e k.succ < 1)
    (hne : ∀ k : Fin (n + 2), k.val + 1 < n + 2 → e k.succ ≠ 0)
    (hsep : ∀ (i j : Fin (n + 2)), i.val + 1 < j.val →
      let c := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
      let u := schwarzChristoffelVertex a e z₀ i.castSucc
      let v := schwarzChristoffelVertex a e z₀ j.castSucc
      let w := schwarzChristoffelVertex a e z₀ j.succ
      (0 < (c * (v - u)).im ∧ 0 < (c * (w - u)).im) ∨
        ((c * (v - u)).im < 0 ∧ (c * (w - u)).im < 0))
    (hheight : ∀ k : Fin (n + 3), k ≠ 0 → k ≠ Fin.last (n + 2) →
      (schwarzChristoffelVertex a e z₀ 0).im < (schwarzChristoffelVertex a e z₀ k).im) :
    BijOn (schwarzChristoffelPrimitive a e z₀) upperHalfPlaneSet
      (filledHull ((schwarzChristoffelPolygon a e z₀).boundary ℝ) \
        (schwarzChristoffelPolygon a e z₀).boundary ℝ) := by
  have hfinite (k : Fin (n + 3)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  have hinfty : ∑ k, e k < -1 := by rw [hsum]; norm_num
  have hinj :=
    schwarzChristoffelCompactifiedBoundary_injective_of_vertex_separation_of_vertex_heights
      a e z₀ ha he hsum hcorner hne hsep hheight
  rw [← range_schwarzChristoffelCompactifiedBoundary a e z₀ ha.monotone hfinite hinfty]
  exact bijOn_schwarzChristoffelPrimitive_filledHull_sdiff a e z₀ hfinite hinfty hinj

end TauCeti
