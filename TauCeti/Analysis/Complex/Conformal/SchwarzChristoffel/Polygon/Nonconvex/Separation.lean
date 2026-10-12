/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Polygon.LongTurn
public import TauCeti.Analysis.Complex.PlaneSeparation.Segment

/-!
# A nonconvex separation test for Schwarz--Christoffel sides

A bounded Schwarz--Christoffel side has a known direction and positive length.
For two sides, rotate the first side to the real axis. If the chord from its
endpoint to the start of the second side has a strict signed height, and the
second side has a weak height of the same sign, then the two sides are disjoint.
The test permits changes in the sign of turning exponents and is therefore
applicable to nonconvex polygonal data. It isolates the geometric separation
needed to check global simplicity from finite vertex and angle information.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

noncomputable section

open Complex Set UpperHalfPlane

namespace TauCeti

variable {n : ℕ}

/-- Two bounded Schwarz--Christoffel sides are disjoint if the chord from the
end of the first side to the beginning of the second has a strict signed height,
and the second side's sine contribution has the same weak sign. The heights are
measured after rotating the first side to the real axis. -/
theorem disjoint_schwarzChristoffelPolygon_bounded_edgeSet_of_chord_sine
    (a e : Fin (n + 1) → ℝ) (z₀ : UpperHalfPlane) (ha : StrictMono a)
    (i j : Fin n)
    (hi₀ : -1 < ∑ l with a l = a i.castSucc, e l)
    (hi₁ : -1 < ∑ l with a l = a i.succ, e l)
    (hj₀ : -1 < ∑ l with a l = a j.castSucc, e l)
    (hj₁ : -1 < ∑ l with a l = a j.succ, e l)
    (hsep :
      (0 < (Complex.exp
          (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
        (schwarzChristoffelVertex a e z₀ j.castSucc -
          schwarzChristoffelVertex a e z₀ i.succ)).im ∧
        0 ≤ Real.sin (schwarzChristoffelEdgeAngle a e (a j.castSucc) -
          schwarzChristoffelEdgeAngle a e (a i.castSucc))) ∨
      ((Complex.exp
          (-schwarzChristoffelEdgeAngle a e (a i.castSucc) * Complex.I) *
        (schwarzChristoffelVertex a e z₀ j.castSucc -
          schwarzChristoffelVertex a e z₀ i.succ)).im < 0 ∧
        Real.sin (schwarzChristoffelEdgeAngle a e (a j.castSucc) -
          schwarzChristoffelEdgeAngle a e (a i.castSucc)) ≤ 0)) :
    Disjoint ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ i.castSucc.castSucc)
      ((schwarzChristoffelPolygon a e z₀).edgeSet ℝ j.castSucc.castSucc) := by
  let V := schwarzChristoffelVertex a e z₀
  let θi := schwarzChristoffelEdgeAngle a e (a i.castSucc)
  let θj := schwarzChristoffelEdgeAngle a e (a j.castSucc)
  let c := Complex.exp (-θi * Complex.I)
  have hline : (c * (V i.succ - V i.castSucc)).im = 0 := by
    simpa only [θi, c, sub_self, Real.sin_zero, mul_zero] using
      im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
        a e z₀ ha θi i hi₀ hi₁
  have hstep : (c * (V j.succ - V j.castSucc)).im =
      ‖V j.succ - V j.castSucc‖ * Real.sin (θj - θi) :=
    im_exp_neg_mul_schwarzChristoffelVertex_succ_sub_eq
      a e z₀ ha θi j hj₀ hj₁
  have hfirst : (c * (V j.castSucc - V i.castSucc)).im =
      (c * (V j.castSucc - V i.succ)).im := by
    have h : V j.castSucc - V i.castSucc =
        (V j.castSucc - V i.succ) + (V i.succ - V i.castSucc) := by ring
    rw [h, mul_add, Complex.add_im, hline, add_zero]
  have hlast : (c * (V j.succ - V i.castSucc)).im =
      (c * (V j.castSucc - V i.castSucc)).im +
        (c * (V j.succ - V j.castSucc)).im := by
    have h : V j.succ - V i.castSucc =
        (V j.castSucc - V i.castSucc) + (V j.succ - V j.castSucc) := by ring
    rw [h, mul_add, Complex.add_im]
  simp only [schwarzChristoffelPolygon_edgeSet_castSucc_castSucc]
  rcases hsep with ⟨hchord, hsin⟩ | ⟨hchord, hsin⟩
  · apply disjoint_segment_of_im_mul_sub_pos c (V i.castSucc) (V i.succ)
      (V j.castSucc) (V j.succ) hline
    · rw [hfirst]
      exact hchord
    · rw [hlast, hfirst, hstep]
      exact add_pos_of_pos_of_nonneg hchord (mul_nonneg (norm_nonneg _) hsin)
  · apply disjoint_segment_of_im_mul_sub_neg c (V i.castSucc) (V i.succ)
      (V j.castSucc) (V j.succ) hline
    · rw [hfirst]
      exact hchord
    · rw [hlast, hfirst, hstep]
      exact add_neg_of_neg_of_nonpos hchord (mul_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hsin)

end TauCeti
