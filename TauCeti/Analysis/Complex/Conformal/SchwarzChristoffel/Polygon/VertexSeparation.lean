/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.BoundedArcInjective
public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.NonconvexSeparation

/-!
# A vertex separation criterion for a Schwarz--Christoffel boundary arc

For a polygon with reentrant corners, ordered prevertices and integrable exponents alone do not
make its boundary simple. The criterion here checks the bounded arc using only the finite
Schwarz--Christoffel vertices. At each nonadjacent pair of sides, the two endpoints of the later
side must lie strictly on the same side of the earlier side's supporting line. With strictly
ordered prevertices, turning exponents in `(-1, 1) \ {0}` at the interior vertices make each
adjacent pair meet only at its common vertex.

The criterion is sufficient for injectivity between the first and last prevertices. To obtain a
simple compactified boundary, the two sides incident to infinity must also be checked.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- Strict signed heights at the endpoints of every nonadjacent later side, together with
strictly ordered prevertices and turning exponents in `(-1, 1) \ {0}` at the interior vertices,
make the bounded Schwarz--Christoffel boundary arc injective. Heights are measured after rotating
each earlier side to the real axis. The condition allows both positive and negative turning
exponents. -/
theorem schwarzChristoffelBoundary_injOn_prevertex_interval_of_vertex_separation
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (he : ∀ k, -1 < e k)
    (hcorner : ∀ k : Fin n, k.val + 1 < n → e k.succ < 1)
    (hne : ∀ k : Fin n, k.val + 1 < n → e k.succ ≠ 0)
    (hsep : ∀ (i j : Fin n), i.val + 1 < j.val →
      let c := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
      let u := schwarzChristoffelVertex a e z₀ i.castSucc
      let v := schwarzChristoffelVertex a e z₀ j.castSucc
      let w := schwarzChristoffelVertex a e z₀ j.succ
      (0 < (c * (v - u)).im ∧ 0 < (c * (w - u)).im) ∨
        ((c * (v - u)).im < 0 ∧ (c * (w - u)).im < 0)) :
    InjOn (schwarzChristoffelBoundary a e z₀)
      (Icc (a 0) (a (Fin.last n))) := by
  have hfinite (k : Fin (n + 1)) : -1 < ∑ l with a l = a k, e l := by
    simpa [ha.injective.eq_iff, Finset.filter_eq'] using he k
  apply schwarzChristoffelBoundary_injOn_prevertex_interval_of_edge_intersections
    a e z₀ ha.monotone hfinite
  intro i j hij z hzi hzj
  by_cases hadj : i.val + 1 = j.val
  · have hcornerI : e i.succ ∈ Ioo (-1 : ℝ) 1 :=
      ⟨he i.succ, hcorner i (by omega)⟩
    have hz : z = schwarzChristoffelVertex a e z₀ i.succ :=
      schwarzChristoffelPolygon_bounded_edgeSet_inter_subset_vertex_of_adjacent
        a e z₀ ha.monotone i j hadj (ha i.castSucc_lt_succ)
        (ha j.castSucc_lt_succ) (hfinite _)
        (by simpa [ha.injective.eq_iff, Finset.filter_eq'] using hcornerI)
        (by simpa [ha.injective.eq_iff, Finset.filter_eq'] using hne i (by omega))
        (hfinite _) ⟨hzi, hzj⟩
    exact ⟨hadj.symm, hz⟩
  have hgap : i.val + 1 < j.val := by
    have := Fin.lt_def.mp hij
    omega
  let c := Complex.exp (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I)
  let u := schwarzChristoffelVertex a e z₀ i.castSucc
  let v := schwarzChristoffelVertex a e z₀ j.castSucc
  let w := schwarzChristoffelVertex a e z₀ j.succ
  have hline : (c * (schwarzChristoffelVertex a e z₀ i.succ - u)).im = 0 := by
    simpa only [c, u, sub_self, Real.sin_zero, mul_zero] using
      im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
        a e z₀ ha (schwarzChristoffelEdgeAngle a e (a i.castSucc)) i
        (hfinite _) (hfinite _)
  have hdisj : Disjoint
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc) := by
    rw [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc,
      schwarzChristoffelPolygon_edgeSet_castSucc_castSucc]
    rcases hsep i j hgap with hpos | hneg
    · exact disjoint_segment_of_im_mul_sub_pos c u
        (schwarzChristoffelVertex a e z₀ i.succ) v w hline hpos.1 hpos.2
    · exact disjoint_segment_of_im_mul_sub_neg c u
        (schwarzChristoffelVertex a e z₀ i.succ) v w hline hneg.1 hneg.2
  exact False.elim (Set.disjoint_left.mp hdisj hzi hzj)

end TauCeti
