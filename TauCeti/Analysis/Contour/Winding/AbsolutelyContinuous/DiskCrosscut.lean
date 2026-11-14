/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Curve.DiskCrosscut
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Concat
import TauCeti.Analysis.Contour.Winding.Number.Circle.Basic
import TauCeti.Analysis.Contour.Winding.Number.Reparam
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Circle

/-!
# Winding numbers and orientations of closed-up disk crosscuts

Let `c` be an injective absolutely continuous arc on `[a, b]` whose interior lies in the open disk
of center `z₀` and radius `r`, and whose endpoints `c b = circleMap z₀ r α` and
`c a = circleMap z₀ r β` lie on the boundary circle. The loop `TauCeti.Contour.arcLoop` follows `c`
and then returns from `c b` to `c a` along the arc of the circle from the angle `α` to the angle
`β`. When `α < β < α + 2π`, there are two such loops: the one closed by the counterclockwise arc
from `α` to `β`, and the one closed by the clockwise arc from `α` to `β - 2π`.

Both loops are simple closed absolutely continuous curves. If `c` is piecewise `C¹`, so are the
loops. At every point of the open disk off the arc, their winding numbers differ by that of the
full circle, which is one. Together with the Jordan
index theorem this shows that the loop closed by the counterclockwise arc is positively oriented,
the loop closed by the clockwise arc is negatively oriented, and every point of the open disk off
the arc lies in exactly one of the two filled hulls.

The construction and its regularity, integral and topological API are in
`TauCeti/Analysis/Contour/Curve/DiskCrosscut.lean`.

## Main results

* `TauCeti.Contour.windingNumber_arcLoop`: decomposition into the original and circle arcs.
* `TauCeti.Contour.windingNumber_arcLoop_eq_add_one`: the winding numbers of the two loops differ
  by one on the open disk off the arc.
* `TauCeti.Contour.jordanSign_arcLoop_eq_one`: the loop closed by the counterclockwise arc is
  positively oriented.
* `TauCeti.Contour.jordanSign_arcLoop_eq_neg_one`: the loop closed by the clockwise arc
  is negatively oriented.
* `TauCeti.Contour.mem_filledHull_arcLoop_iff_notMem`: each point of the open disk off the arc lies
  in exactly one of the two filled hulls.

## References

* C. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Section 2.1.
-/

public section

noncomputable section

open Set Metric Complex Real Filter MeasureTheory
open scoped Topology Interval

namespace TauCeti.Contour

variable {c : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {r α β : ℝ}

/-- Off the trace, the winding number of the closed-up arc is the sum of the winding numbers
of the original arc and the closing circle arc. -/
theorem windingNumber_arcLoop (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hb : c b = circleMap z₀ r α) {z : ℂ}
    (hz : z ∉ arcLoop c b z₀ r α β '' uIcc a (b + 1)) :
    windingNumber (arcLoop c b z₀ r α β) a (b + 1) z =
      windingNumber c a b z + windingNumber (circleMap z₀ r) α β z := by
  have hL := hc.arcLoop (β := β) hab hb
  have h1 : uIcc a b ⊆ uIcc a (b + 1) := by
    rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have h2 : uIcc b (b + 1) ⊆ uIcc a (b + 1) := by
    rw [uIcc_of_le (by linarith : b ≤ b + 1), uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hab le_rfl
  have hleft : windingNumber (arcLoop c b z₀ r α β) a b z = windingNumber c a b z :=
    windingNumber_congr_curve fun s hs => arcLoop_of_le
      ((uIcc_of_le hab ▸ uIoo_subset_uIcc_self hs).2)
  have hright : windingNumber (arcLoop c b z₀ r α β) b (b + 1) z =
      windingNumber (circleCap z₀ r b (b + 1) α β) b (b + 1) z :=
    windingNumber_congr_curve fun s hs => eqOn_arcLoop_Ici hb
      ((uIcc_of_le (lt_add_one b).le ▸ uIoo_subset_uIcc_self hs).1)
  have hcircle : ∀ θ ∈ uIcc α β, circleMap z₀ r θ ≠ z := by
    intro θ hθ heq
    apply hz
    rw [image_arcLoop hab hb]
    exact Or.inr ⟨θ, hθ, heq⟩
  rw [(hL.mono h1).windingNumber_concat (hL.mono h2)
    (fun h => hz (image_mono h1 h)) (fun h => hz (image_mono h2 h)), hleft, hright]
  congr 1
  rw [windingNumber_congr_curve (γ₂ := circleMap z₀ r ∘
    fun s => (β - α) * s + (α - (β - α) * b)) (fun s _ => by
      simp only [circleCap_apply, add_sub_cancel_left, div_one, Function.comp_apply]
      congr 1
      ring)]
  have hstart : (β - α) * b + (α - (β - α) * b) = α := by ring
  have hend : (β - α) * (b + 1) + (α - (β - α) * b) = β := by ring
  rw [windingNumber_comp_mul_add (fun θ _ => differentiable_circleMap z₀ r θ)
    (continuous_deriv_circleMap z₀ r).continuousOn (fun θ hθ => hcircle θ (by
      rwa [hstart, hend] at hθ)), hstart, hend]

/-- The winding numbers of the loops closed by the circle arcs from `α` to `β` and from `α` to
`β - 2π` differ by one at every point of the open disk off the arc `c`. -/
theorem windingNumber_arcLoop_eq_add_one (hab : a ≤ b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hb : c b = circleMap z₀ r α) {z : ℂ} (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    windingNumber (arcLoop c b z₀ r α β) a (b + 1) z =
      windingNumber (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1) z + 1 := by
  have hoff : ∀ l u, z ∉ circleMap z₀ r '' uIcc l u := by
    rintro l u ⟨θ, -, rfl⟩
    exact circleMap_notMem_ball z₀ r θ hz
  have hturn : windingNumber (circleMap z₀ r) (β - 2 * π) β z = 1 := by
    rw [(absolutelyContinuousOnInterval_circleMap z₀ r _ _).windingNumber_eq_integral (hoff _ _)]
    have h := integral_circleMap_index_add_two_pi (mem_ball.mp hz) (β - 2 * π)
    rw [sub_add_cancel] at h
    rw [h, inv_mul_cancel₀ Complex.two_pi_I_ne_zero]
  rw [windingNumber_arcLoop hab hc hb (notMem_image_arcLoop hab hb hz hzc),
    windingNumber_arcLoop hab hc hb (notMem_image_arcLoop hab hb hz hzc),
    (absolutelyContinuousOnInterval_circleMap z₀ r α (β - 2 * π)).windingNumber_concat
      (absolutelyContinuousOnInterval_circleMap z₀ r (β - 2 * π) β) (hoff _ _) (hoff _ _), hturn]
  exact (add_assoc _ _ _).symm

section Orientation

variable {δ : ℝ}

open scoped Classical in
private theorem windingNumber_arcLoop_eq_ite (hab : a < b)
    (hc : AbsolutelyContinuousOnInterval c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r δ) (hb : c b = circleMap z₀ r α)
    (hδα : |δ - α| < 2 * π) {z : ℂ} (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    windingNumber (arcLoop c b z₀ r α δ) a (b + 1) z =
      if z ∈ filledHull (arcLoop c b z₀ r α δ '' uIcc a (b + 1)) then
        (jordanSign (arcLoop c b z₀ r α δ) a (b + 1) : ℂ) else 0 := by
  have hL := hc.arcLoop (β := δ) hab.le hb
  have hcl := arcLoop_eq_arcLoop_add_one (α := α) hab.le ha
  split_ifs with hzH
  · exact hL.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff (by linarith) hcl
      (injOn_arcLoop hab hinj hin ha hb hδα) ⟨hzH, notMem_image_arcLoop hab.le hb hz hzc⟩
  · exact hL.windingNumber_eq_zero_of_notMem_filledHull hcl hzH

private theorem jordanSign_arcLoop_eq_one_or_neg_one (hab : a < b)
    (hc : AbsolutelyContinuousOnInterval c a b) (hinj : InjOn c (Icc a b))
    (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (ha : c a = circleMap z₀ r δ)
    (hb : c b = circleMap z₀ r α) (hδα : |δ - α| < 2 * π) :
    jordanSign (arcLoop c b z₀ r α δ) a (b + 1) = 1 ∨
      jordanSign (arcLoop c b z₀ r α δ) a (b + 1) = -1 :=
  (hc.arcLoop (β := δ) hab.le hb)
    |>.jordanSign_eq_one_or_neg_one (by linarith) (arcLoop_eq_arcLoop_add_one hab.le ha)
      (injOn_arcLoop hab hinj hin ha hb hδα)

private theorem exists_mem_ball_arcLoop (hab : a < b) (hc : ContinuousOn c (Icc a b))
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r δ) (hb : c b = circleMap z₀ r α)
    (hδα : |δ - α| < 2 * π) :
    ∃ z ∈ ball z₀ r, z ∉ c '' Icc a b ∧
      z ∈ filledHull (arcLoop c b z₀ r α δ '' uIcc a (b + 1)) := by
  obtain ⟨z, hz⟩ :=
    (isJordanCurve_image_arcLoop hab hc hinj hin ha hb hδα).nonempty_filledHull_sdiff
  have h := (mem_filledHull_sdiff_image_arcLoop_iff hab hc hinj hin ha hb hδα).mp hz
  exact ⟨z, h.1.1, h.1.2, h.2⟩

private theorem jordanSign_arcLoop_and_mem_filledHull_iff (hab : a < b)
    (hc : AbsolutelyContinuousOnInterval c a b) (hinj : InjOn c (Icc a b))
    (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (ha : c a = circleMap z₀ r β)
    (hb : c b = circleMap z₀ r α) (hαβ : α < β) (hβα : β < α + 2 * π) :
    jordanSign (arcLoop c b z₀ r α β) a (b + 1) = 1 ∧
      jordanSign (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1) = -1 ∧
      ∀ z ∈ ball z₀ r, z ∉ c '' Icc a b →
        (z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) ↔
          z ∉ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1))) := by
  have ha' : c a = circleMap z₀ r (β - 2 * π) := by
    rw [ha, ← periodic_circleMap z₀ r (β - 2 * π), sub_add_cancel]
  have h1' : |β - α| < 2 * π := by rw [abs_of_pos (by linarith)]; linarith
  have h2' : |β - 2 * π - α| < 2 * π := by
    rw [abs_of_neg (by linarith)]; linarith
  have hw1 := fun {z} hz hzc => windingNumber_arcLoop_eq_ite (z := z) hab hc hinj hin ha hb h1'
    hz hzc
  have hw2 := fun {z} hz hzc =>
    windingNumber_arcLoop_eq_ite (z := z) hab hc hinj hin ha' hb h2' hz hzc
  have hdiff := fun {z} hz hzc => windingNumber_arcLoop_eq_add_one (β := β) (z := z) hab.le hc hb
    hz hzc
  classical
  set s₁ := jordanSign (arcLoop c b z₀ r α β) a (b + 1)
  set s₂ := jordanSign (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1)
  have hs₁ := jordanSign_arcLoop_eq_one_or_neg_one hab hc hinj hin ha hb h1'
  have hs₂ := jordanSign_arcLoop_eq_one_or_neg_one hab hc hinj hin ha' hb h2'
  -- The winding-number difference forces the two possible Jordan signs and memberships.
  have key : ∀ z ∈ ball z₀ r, z ∉ c '' Icc a b →
      ((if z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) then s₁ else 0) : ℤ) =
        (if z ∈ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1)) then s₂ else 0)
          + 1 := by
    intro z hz hzc
    have h := hdiff hz hzc
    rw [hw1 hz hzc, hw2 hz hzc] at h
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hc' : ContinuousOn c (Icc a b) := uIcc_of_le hab.le ▸ hc.continuousOn
  obtain ⟨z₁, hz₁, hz₁c, hz₁H⟩ := exists_mem_ball_arcLoop hab hc' hinj hin ha hb h1'
  obtain ⟨z₂, hz₂, hz₂c, hz₂H⟩ := exists_mem_ball_arcLoop hab hc' hinj hin ha' hb h2'
  have k1 := key z₁ hz₁ hz₁c
  have k2 := key z₂ hz₂ hz₂c
  simp only [hz₁H, ↓reduceIte] at k1
  simp only [hz₂H, ↓reduceIte] at k2
  have hs₁1 : s₁ = 1 := by
    rcases hs₁ with h | h <;> rcases hs₂ with h' | h' <;> split_ifs at k1 <;> omega
  have hs₂1 : s₂ = -1 := by
    rcases hs₂ with h' | h' <;> split_ifs at k2 <;> omega
  refine ⟨hs₁1, hs₂1, fun z hz hzc => ?_⟩
  have k := key z hz hzc
  rw [hs₁1, hs₂1] at k
  by_cases hA : z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) <;>
    by_cases hB : z ∈ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1)) <;>
    simp only [hA, hB, ↓reduceIte] at k
  · omega
  · exact iff_of_true hA hB
  · exact iff_of_false hA (not_not_intro hB)
  · omega

/-- The loop closed by the counterclockwise circle arc from `α` to `β` is positively oriented. -/
theorem jordanSign_arcLoop_eq_one (hab : a < b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α < β)
    (hβα : β < α + 2 * π) :
    jordanSign (arcLoop c b z₀ r α β) a (b + 1) = 1 :=
  (jordanSign_arcLoop_and_mem_filledHull_iff hab hc hinj hin ha hb hαβ hβα).1

/-- The loop closed by a clockwise circle arc shorter than a full circle is negatively
oriented. -/
theorem jordanSign_arcLoop_eq_neg_one (hab : a < b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hβα : β < α)
    (hαβ : α < β + 2 * π) :
    jordanSign (arcLoop c b z₀ r α β) a (b + 1) = -1 := by
  have ha' : c a = circleMap z₀ r (β + 2 * π) := by
    rw [periodic_circleMap, ha]
  simpa only [add_sub_cancel_right] using
    (jordanSign_arcLoop_and_mem_filledHull_iff hab hc hinj hin ha' hb hαβ (by linarith)).2.1

/-- Every point of the open disk off the arc `c` lies in exactly one of the filled hulls of the
loops closed by the counterclockwise and the clockwise circle arcs. -/
theorem mem_filledHull_arcLoop_iff_notMem (hab : a < b) (hc : AbsolutelyContinuousOnInterval c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α < β)
    (hβα : β < α + 2 * π) {z : ℂ} (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) ↔
      z ∉ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1)) :=
  (jordanSign_arcLoop_and_mem_filledHull_iff hab hc hinj hin ha hb hαβ hβα).2.2 z hz hzc

end Orientation

end TauCeti.Contour
