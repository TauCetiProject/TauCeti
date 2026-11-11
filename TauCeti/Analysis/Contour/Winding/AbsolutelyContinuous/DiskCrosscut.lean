/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
public import TauCeti.Topology.JordanCurve.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Contour.Winding.Number.Circle
import TauCeti.Topology.JordanCurve.Interval

/-!
# Crosscuts of a disk closed up by circle arcs

Let `c` be an injective piecewise `C¹` arc on `[a, b]` whose interior lies in the open disk of
center `z₀` and radius `r`, and whose endpoints `c b = circleMap z₀ r α` and
`c a = circleMap z₀ r β` lie on the boundary circle. The loop `TauCeti.Contour.arcLoop` follows `c`
and then returns from `c b` to `c a` along the arc of the circle from the angle `α` to the angle
`β`. When `α < β < α + 2π`, there are two such loops: the one closed by the counterclockwise arc
from `α` to `β`, and the one closed by the clockwise arc from `α` to `β - 2π`.

Both loops are simple closed piecewise `C¹` curves. At every point of the open disk off the arc,
their winding numbers differ by that of the full circle, which is one. Together with the Jordan
index theorem this shows that the loop closed by the counterclockwise arc is positively oriented,
the loop closed by the clockwise arc is negatively oriented, and every point of the open disk off
the arc lies in exactly one of the two filled hulls.

## Main results

* `TauCeti.Contour.arcLoop`: the arc `c` followed by a circle arc.
* `TauCeti.Contour.isJordanCurve_image_arcLoop`: the trace of the loop is a Jordan curve.
* `TauCeti.Contour.windingNumber_arcLoop_eq_add_one`: the winding numbers of the two loops differ
  by one on the open disk off the arc.
* `TauCeti.Contour.jordanSign_arcLoop_eq_one`: the loop closed by the counterclockwise arc is
  positively oriented.
* `TauCeti.Contour.jordanSign_arcLoop_sub_two_pi_eq_neg_one`: the loop closed by the clockwise arc
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

/-- The loop which follows `c` up to the parameter `b` and then, on `[b, b + 1]`, the arc of the
circle of center `z₀` and radius `r` from the angle `α` to the angle `β`. -/
def arcLoop (c : ℝ → ℂ) (b : ℝ) (z₀ : ℂ) (r α β : ℝ) (s : ℝ) : ℂ :=
  if s ≤ b then c s else circleMap z₀ r (α + (s - b) * (β - α))

variable {c : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {r α β : ℝ}

/-- Up to the parameter `b`, the loop is the arc `c`. -/
@[simp]
theorem arcLoop_of_le {s : ℝ} (hs : s ≤ b) : arcLoop c b z₀ r α β s = c s := ite_eq_left hs

/-- After the parameter `b`, the loop is the affinely reparametrized circle. -/
@[simp]
theorem arcLoop_of_lt {s : ℝ} (hs : b < s) :
    arcLoop c b z₀ r α β s = circleMap z₀ r (α + (s - b) * (β - α)) := ite_eq_right hs.not_ge

/-- At the parameter `b + 1`, the loop reaches the point of angle `β` of the circle. -/
theorem arcLoop_add_one : arcLoop c b z₀ r α β (b + 1) = circleMap z₀ r β := by
  rw [arcLoop_of_lt (lt_add_one b)]
  congr 1
  ring

/-- The loop agrees with the arc `c` near every parameter before `b`. -/
theorem arcLoop_eventuallyEq_of_lt {s : ℝ} (hs : s < b) : arcLoop c b z₀ r α β =ᶠ[𝓝 s] c :=
  (eventually_lt_nhds hs).mono fun _ h => arcLoop_of_le h.le

/-- The loop agrees with the affinely reparametrized circle near every parameter after `b`. -/
theorem arcLoop_eventuallyEq_of_gt {s : ℝ} (hs : b < s) :
    arcLoop c b z₀ r α β =ᶠ[𝓝 s] fun s => circleMap z₀ r (α + (s - b) * (β - α)) :=
  (eventually_gt_nhds hs).mono fun _ h => arcLoop_of_lt h

/-- The loop closed by a circle arc ending at the point where `c` starts is closed. -/
theorem arcLoop_eq_arcLoop_add_one (hab : a ≤ b) (ha : c a = circleMap z₀ r β) :
    arcLoop c b z₀ r α β a = arcLoop c b z₀ r α β (b + 1) := by
  rw [arcLoop_of_le hab, arcLoop_add_one, ha]

/-- Closing a piecewise `C¹` arc by a circle arc gives a piecewise `C¹` loop. -/
theorem isPiecewiseC1On_arcLoop (hc : IsPiecewiseC1On c a b) (hab : a ≤ b)
    (hb : c b = circleMap z₀ r α) : IsPiecewiseC1On (arcLoop c b z₀ r α β) a (b + 1) := by
  have harc : IsPiecewiseC1On (fun s => circleMap z₀ r (α + (s - b) * (β - α))) b (b + 1) :=
    IsPiecewiseC1On.of_contDiffOn ((contDiff_circleMap z₀ r).comp (by fun_prop)).contDiffOn
  exact hc.if_le harc hab (by linarith) (by simpa using hb)

/-- From the parameter `b` on, the loop is the affinely reparametrized circle, provided the arc `c`
ends at the point of angle `α`. -/
theorem eqOn_arcLoop_Ici (hb : c b = circleMap z₀ r α) :
    EqOn (arcLoop c b z₀ r α β) (fun s => circleMap z₀ r (α + (s - b) * (β - α))) (Ici b) := by
  intro s hs
  rcases (mem_Ici.mp hs).eq_or_lt with rfl | hsb
  · simp [hb]
  · exact arcLoop_of_lt hsb

/-- Closing a continuous arc by a circle arc gives a continuous loop. -/
theorem continuousOn_arcLoop (hc : ContinuousOn c (Icc a b)) (hab : a ≤ b)
    (hb : c b = circleMap z₀ r α) : ContinuousOn (arcLoop c b z₀ r α β) (Icc a (b + 1)) := by
  rw [← Icc_union_Icc_eq_Icc hab (le_add_of_nonneg_right zero_le_one)]
  refine ContinuousOn.union_of_isClosed (hc.congr fun s hs => arcLoop_of_le hs.2) ?_
    isClosed_Icc isClosed_Icc
  exact ((continuous_circleMap z₀ r).comp (by fun_prop)).continuousOn.congr
    ((eqOn_arcLoop_Ici hb).mono Icc_subset_Ici_self)

/-- The trace of the loop is the trace of the arc together with the circle arc. -/
theorem image_arcLoop (hab : a ≤ b) (hb : c b = circleMap z₀ r α) :
    arcLoop c b z₀ r α β '' uIcc a (b + 1) = c '' Icc a b ∪ circleMap z₀ r '' uIcc α β := by
  have hb1 : b ≤ b + 1 := le_add_of_nonneg_right zero_le_one
  let f : ℝ →ᵃ[ℝ] ℝ := (AffineMap.lineMap α β).comp ((AffineMap.id ℝ ℝ) - AffineMap.const ℝ ℝ b)
  have hf : ∀ s, f s = α + (s - b) * (β - α) := fun s => by
    simp only [f, AffineMap.coe_comp, Function.comp_apply, AffineMap.coe_sub, AffineMap.coe_id,
      AffineMap.coe_const, Pi.sub_apply, id_eq, Function.const_apply, AffineMap.lineMap_apply_ring']
    ring
  have hcircle : (fun s => circleMap z₀ r (α + (s - b) * (β - α))) = circleMap z₀ r ∘ f := by
    ext s
    simp [hf]
  rw [uIcc_of_le (hab.trans hb1), ← Icc_union_Icc_eq_Icc hab hb1, image_union,
    image_congr fun s (hs : s ∈ Icc a b) => arcLoop_of_le hs.2,
    image_congr fun s (hs : s ∈ Icc b (b + 1)) => eqOn_arcLoop_Ici hb (Icc_subset_Ici_self hs),
    hcircle, image_comp,
    ← uIcc_of_le hb1, AffineMap.image_uIcc, hf, hf]
  simp

/-- A point of the open disk off the arc `c` is off the trace of the loop. -/
theorem notMem_image_arcLoop (hab : a ≤ b) (hb : c b = circleMap z₀ r α) {z : ℂ}
    (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    z ∉ arcLoop c b z₀ r α β '' uIcc a (b + 1) := by
  rw [image_arcLoop hab hb]
  rintro (h | ⟨θ, -, rfl⟩)
  · exact hzc h
  · exact circleMap_notMem_ball z₀ r θ hz

/-- If the interior of the arc `c` lies in the open disk and its endpoints lie on the circle, then
the trace of the loop lies in the closed disk. -/
theorem image_arcLoop_subset_closedBall (hab : a ≤ b) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (hr : 0 ≤ r) (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) :
    arcLoop c b z₀ r α β '' uIcc a (b + 1) ⊆ closedBall z₀ r := by
  rw [image_arcLoop hab hb]
  rintro _ (⟨s, hs, rfl⟩ | ⟨θ, -, rfl⟩)
  · rcases hs.1.eq_or_lt with rfl | has
    · rw [ha]
      exact circleMap_mem_closedBall z₀ hr β
    rcases hs.2.eq_or_lt with rfl | hsb
    · rw [hb]
      exact circleMap_mem_closedBall z₀ hr α
    exact ball_subset_closedBall (hin s ⟨has, hsb⟩)
  · exact circleMap_mem_closedBall z₀ hr θ

/-- If the interior of the arc `c` lies in the open disk and its endpoints lie on the circle, then
the filled hull of the trace of the loop lies in the closed disk. -/
theorem filledHull_image_arcLoop_subset_closedBall (hab : a ≤ b)
    (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (hr : 0 ≤ r) (ha : c a = circleMap z₀ r β)
    (hb : c b = circleMap z₀ r α) :
    filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) ⊆ closedBall z₀ r :=
  (filledHull_subset_closedConvexHull ⟨_, mem_image_of_mem _ left_mem_uIcc⟩).trans
    (closedConvexHull_min (image_arcLoop_subset_closedBall hab hin hr ha hb)
      (convex_closedBall z₀ r) isClosed_closedBall)

/-- The loop is injective on `[a, b + 1)`: the arc meets the circle only at its endpoints, and the
circle arc is shorter than the full circle. -/
theorem injOn_arcLoop (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (hr : 0 < r) (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α ≠ β)
    (hβα : |β - α| < 2 * π) : InjOn (arcLoop c b z₀ r α β) (Ico a (b + 1)) := by
  have hsph : ∀ θ, circleMap z₀ r θ ∉ ball z₀ r := circleMap_notMem_ball z₀ r
  have hend : ∀ s ∈ Icc a b, c s ∉ ball z₀ r → s = a ∨ s = b := fun s hs h => by
    by_contra hne
    push Not at hne
    exact h (hin s ⟨lt_of_le_of_ne hs.1 hne.1.symm, lt_of_le_of_ne hs.2 hne.2⟩)
  have hθα : ∀ s, b < s → s < b + 1 →
      circleMap z₀ r (α + (s - b) * (β - α)) ≠ circleMap z₀ r α := fun s h1 h2 h => by
    have hd : |α + (s - b) * (β - α) - α| < 2 * π := by
      rw [add_sub_cancel_left, abs_mul, abs_of_pos (by linarith : 0 < s - b)]
      nlinarith [abs_nonneg (β - α)]
    have : (s - b) * (β - α) ≠ 0 := mul_ne_zero (by linarith) (sub_ne_zero.mpr hαβ.symm)
    exact this (by linarith [eq_of_circleMap_eq hr.ne' hd h])
  have hθβ : ∀ s, b < s → s < b + 1 →
      circleMap z₀ r (α + (s - b) * (β - α)) ≠ circleMap z₀ r β := fun s h1 h2 h => by
    have hsub : α + (s - b) * (β - α) - β = -((b + 1 - s) * (β - α)) := by ring
    have hd : |α + (s - b) * (β - α) - β| < 2 * π := by
      rw [hsub, abs_neg, abs_mul, abs_of_pos (by linarith : 0 < b + 1 - s)]
      nlinarith [abs_nonneg (β - α)]
    have : (b + 1 - s) * (β - α) ≠ 0 := mul_ne_zero (by linarith) (sub_ne_zero.mpr hαβ.symm)
    exact this (by linarith [eq_of_circleMap_eq hr.ne' hd h])
  have hcross : ∀ s ∈ Ico a (b + 1), ∀ s' ∈ Ico a (b + 1), s ≤ b → b < s' →
      arcLoop c b z₀ r α β s ≠ arcLoop c b z₀ r α β s' := fun s hs s' hs' hsb hs'b h => by
    rw [arcLoop_of_le hsb, arcLoop_of_lt hs'b] at h
    rcases hend s ⟨hs.1, hsb⟩ (h ▸ hsph _) with rfl | rfl
    · exact hθβ s' hs'b hs'.2 (h.symm.trans ha)
    · exact hθα s' hs'b hs'.2 (h.symm.trans hb)
  intro s hs s' hs' h
  rcases le_or_gt s b with hsb | hsb <;> rcases le_or_gt s' b with hs'b | hs'b
  · rw [arcLoop_of_le hsb, arcLoop_of_le hs'b] at h
    exact hinj ⟨hs.1, hsb⟩ ⟨hs'.1, hs'b⟩ h
  · exact absurd h (hcross s hs s' hs' hsb hs'b)
  · exact absurd h.symm (hcross s' hs' s hs hs'b hsb)
  · rw [arcLoop_of_lt hsb, arcLoop_of_lt hs'b] at h
    have hsub : α + (s - b) * (β - α) - (α + (s' - b) * (β - α)) = (s - s') * (β - α) := by ring
    have h' := eq_of_circleMap_eq hr.ne' (by
      rw [hsub, abs_mul]
      have : |s - s'| < 1 := abs_sub_lt_iff.mpr ⟨by linarith [hs.2], by linarith [hs'.2]⟩
      nlinarith [abs_nonneg (s - s'), abs_nonneg (β - α)]) h
    have : (s - s') * (β - α) = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · linarith
    · exact absurd (sub_eq_zero.mp h0).symm hαβ

/-- If the interior of the injective arc `c` lies in the open disk, its endpoints lie on the
circle, and the closing circle arc is nontrivial and shorter than the full circle, then the trace
of the loop is a Jordan curve. -/
theorem isJordanCurve_image_arcLoop (hab : a < b) (hc : ContinuousOn c (Icc a b))
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (hr : 0 < r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α ≠ β)
    (hβα : |β - α| < 2 * π) :
    IsJordanCurve (arcLoop c b z₀ r α β '' uIcc a (b + 1)) := by
  rw [uIcc_of_le (by linarith)]
  exact isJordanCurve_image_Icc (by linarith) (continuousOn_arcLoop hc hab.le hb)
    (arcLoop_eq_arcLoop_add_one hab.le ha) (injOn_arcLoop hinj hin hr ha hb hαβ hβα)

private theorem integral_arcLoop_arc {z : ℂ} :
    ∫ s in b..b + 1, (arcLoop c b z₀ r α β s - z)⁻¹ * deriv (arcLoop c b z₀ r α β) s =
      ∫ θ in α..β, (circleMap z₀ r θ - z)⁻¹ * (circleMap 0 r θ * I) := by
  set g : ℝ → ℂ := fun θ => (circleMap z₀ r θ - z)⁻¹ * (circleMap 0 r θ * I)
  have hcongr : EqOn (fun s => (arcLoop c b z₀ r α β s - z)⁻¹ * deriv (arcLoop c b z₀ r α β) s)
      (fun s => ((β - α : ℝ) : ℂ) * g ((β - α) * s + (α - b * (β - α)))) (uIoo b (b + 1)) := by
    intro s hs
    rw [uIoo_of_le (by linarith)] at hs
    have hθ : (β - α) * s + (α - b * (β - α)) = α + (s - b) * (β - α) := by ring
    have hderiv : HasDerivAt (fun s => circleMap z₀ r (α + (s - b) * (β - α)))
        ((β - α : ℝ) • (circleMap 0 r (α + (s - b) * (β - α)) * I)) s := by
      have hin : HasDerivAt (fun s : ℝ => α + (s - b) * (β - α)) (β - α) s := by
        simpa using ((hasDerivAt_id s).sub_const b).mul_const (β - α) |>.const_add α
      exact (hasDerivAt_circleMap z₀ r _).scomp s hin
    simp only [g, hθ]
    rw [(arcLoop_eventuallyEq_of_gt hs.1).deriv_eq, hderiv.deriv, arcLoop_of_lt hs.1,
      Complex.real_smul]
    ring
  rw [intervalIntegral.integral_congr_uIoo hcongr, intervalIntegral.integral_const_mul]
  rcases eq_or_ne β α with rfl | hd
  · simp
  rw [intervalIntegral.integral_comp_mul_add (f := g) (sub_ne_zero.mpr hd)]
  have h1 : (β - α) * b + (α - b * (β - α)) = α := by ring
  have h2 : (β - α) * (b + 1) + (α - b * (β - α)) = β := by ring
  rw [h1, h2, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hd)), one_mul]

/-- The winding numbers of the loops closed by the circle arcs from `α` to `β` and from `α` to
`β - 2π` differ by one at every point of the open disk off the arc `c`. -/
theorem windingNumber_arcLoop_eq_add_one (hab : a ≤ b) (hc : IsPiecewiseC1On c a b)
    (hb : c b = circleMap z₀ r α) {z : ℂ} (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    windingNumber (arcLoop c b z₀ r α β) a (b + 1) z =
      windingNumber (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1) z + 1 := by
  have key : ∀ δ, windingNumber (arcLoop c b z₀ r α δ) a (b + 1) z =
      (2 * (π : ℂ) * I)⁻¹ * ((∫ s in a..b, (arcLoop c b z₀ r α δ s - z)⁻¹ *
        deriv (arcLoop c b z₀ r α δ) s) +
        ∫ θ in α..δ, (circleMap z₀ r θ - z)⁻¹ * (circleMap 0 r θ * I)) := by
    intro δ
    have hL := isPiecewiseC1On_arcLoop (β := δ) hc hab hb
    have havoid : ∀ t ∈ uIcc a (b + 1), arcLoop c b z₀ r α δ t ≠ z := fun t ht h =>
      notMem_image_arcLoop hab hb hz hzc ⟨t, ht, h⟩
    have hint := intervalIntegrable_inv_sub_mul_deriv hL.continuousOn havoid
      hL.intervalIntegrable_deriv
    have h1 : uIcc a b ⊆ uIcc a (b + 1) := by
      rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
      exact Icc_subset_Icc le_rfl (by linarith)
    have h2 : uIcc b (b + 1) ⊆ uIcc a (b + 1) := by
      rw [uIcc_of_le (by linarith : b ≤ b + 1), uIcc_of_le (by linarith)]
      exact Icc_subset_Icc hab le_rfl
    rw [windingNumber_eq_integral_of_avoidance hL.continuousOn havoid hint,
      ← intervalIntegral.integral_add_adjacent_intervals (hint.mono_set h1) (hint.mono_set h2),
      integral_arcLoop_arc]
  have hfirst : (∫ s in a..b, (arcLoop c b z₀ r α β s - z)⁻¹ *
      deriv (arcLoop c b z₀ r α β) s) = ∫ s in a..b, (arcLoop c b z₀ r α (β - 2 * π) s - z)⁻¹ *
        deriv (arcLoop c b z₀ r α (β - 2 * π)) s := by
    refine intervalIntegral.integral_congr_uIoo fun s hs => ?_
    rw [uIoo_of_le hab] at hs
    simp only [(arcLoop_eventuallyEq_of_lt (z₀ := z₀) (r := r) (α := α) (β := β) hs.2).deriv_eq,
      (arcLoop_eventuallyEq_of_lt (z₀ := z₀) (r := r) (α := α) (β := β - 2 * π) hs.2).deriv_eq,
      arcLoop_of_le hs.2.le]
  have hg : Continuous fun θ => (circleMap z₀ r θ - z)⁻¹ * (circleMap 0 r θ * I) :=
    (((continuous_circleMap z₀ r).sub continuous_const).inv₀
      fun θ => sub_ne_zero.mpr (circleMap_ne_mem_ball hz θ)).mul
      ((continuous_circleMap 0 r).mul continuous_const)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) α (β - 2 * π))
    (hg.intervalIntegrable (μ := volume) (β - 2 * π) β)
  have hturn := integral_circleMap_index_add_two_pi (mem_ball.mp hz) (β - 2 * π)
  simp only [sub_add_cancel, deriv_circleMap] at hturn
  rw [hturn] at hsplit
  rw [key β, key (β - 2 * π), hfirst, ← hsplit]
  have hpi : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  field_simp
  ring

section Orientation

variable {δ : ℝ}

open scoped Classical in
private theorem windingNumber_arcLoop_eq_ite (hab : a < b) (hc : IsPiecewiseC1On c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r δ) (hb : c b = circleMap z₀ r α) (hαδ : α ≠ δ)
    (hδα : |δ - α| < 2 * π) {z : ℂ} (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    windingNumber (arcLoop c b z₀ r α δ) a (b + 1) z =
      if z ∈ filledHull (arcLoop c b z₀ r α δ '' uIcc a (b + 1)) then
        (jordanSign (arcLoop c b z₀ r α δ) a (b + 1) : ℂ) else 0 := by
  have hr : 0 < r := pos_of_mem_ball hz
  have hL := (isPiecewiseC1On_arcLoop (β := δ) hc hab.le hb).absolutelyContinuousOnInterval
  have hcl := arcLoop_eq_arcLoop_add_one (α := α) hab.le ha
  split_ifs with hzH
  · exact hL.windingNumber_eq_jordanSign_of_mem_filledHull_sdiff (by linarith) hcl
      (injOn_arcLoop hinj hin hr ha hb hαδ hδα) ⟨hzH, notMem_image_arcLoop hab.le hb hz hzc⟩
  · exact hL.windingNumber_eq_zero_of_notMem_filledHull hcl hzH

private theorem jordanSign_arcLoop_eq_one_or_neg_one (hab : a < b)
    (hc : IsPiecewiseC1On c a b) (hinj : InjOn c (Icc a b))
    (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (hr : 0 < r) (ha : c a = circleMap z₀ r δ)
    (hb : c b = circleMap z₀ r α) (hαδ : α ≠ δ) (hδα : |δ - α| < 2 * π) :
    jordanSign (arcLoop c b z₀ r α δ) a (b + 1) = 1 ∨
      jordanSign (arcLoop c b z₀ r α δ) a (b + 1) = -1 :=
  (isPiecewiseC1On_arcLoop (β := δ) hc hab.le hb).absolutelyContinuousOnInterval
    |>.jordanSign_eq_one_or_neg_one (by linarith) (arcLoop_eq_arcLoop_add_one hab.le ha)
      (injOn_arcLoop hinj hin hr ha hb hαδ hδα)

private theorem exists_mem_ball_arcLoop (hab : a < b) (hc : ContinuousOn c (Icc a b))
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (hr : 0 < r)
    (ha : c a = circleMap z₀ r δ) (hb : c b = circleMap z₀ r α) (hαδ : α ≠ δ)
    (hδα : |δ - α| < 2 * π) :
    ∃ z ∈ ball z₀ r, z ∉ c '' Icc a b ∧
      z ∈ filledHull (arcLoop c b z₀ r α δ '' uIcc a (b + 1)) := by
  have hJ := isJordanCurve_image_arcLoop hab hc hinj hin hr ha hb hαδ hδα
  obtain ⟨z, hz⟩ := hJ.nonempty_filledHull_sdiff
  have hzball : z ∈ ball z₀ r := by
    rw [← hJ.interior_filledHull] at hz
    rw [← interior_closedBall z₀ hr.ne']
    exact interior_mono (filledHull_image_arcLoop_subset_closedBall hab.le hin hr.le ha hb) hz
  refine ⟨z, hzball, fun h => hz.2 ?_, hz.1⟩
  rw [image_arcLoop hab.le hb]
  exact Or.inl h

private theorem jordanSign_arcLoop_and_mem_filledHull_iff (hab : a < b)
    (hc : IsPiecewiseC1On c a b) (hinj : InjOn c (Icc a b))
    (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r) (ha : c a = circleMap z₀ r β)
    (hb : c b = circleMap z₀ r α) (hαβ : α < β) (hβα : β < α + 2 * π) :
    jordanSign (arcLoop c b z₀ r α β) a (b + 1) = 1 ∧
      jordanSign (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1) = -1 ∧
      ∀ z ∈ ball z₀ r, z ∉ c '' Icc a b →
        (z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) ↔
          z ∉ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1))) := by
  have hr : 0 < r := pos_of_mem_ball (hin ((a + b) / 2) ⟨by linarith, by linarith⟩)
  have ha' : c a = circleMap z₀ r (β - 2 * π) := by
    rw [ha, ← periodic_circleMap z₀ r (β - 2 * π), sub_add_cancel]
  have h1 : α ≠ β := hαβ.ne
  have h1' : |β - α| < 2 * π := by rw [abs_of_pos (by linarith)]; linarith
  have h2 : α ≠ β - 2 * π := by linarith
  have h2' : |β - 2 * π - α| < 2 * π := by
    rw [abs_of_neg (by linarith)]; linarith
  have hw1 := fun {z} hz hzc => windingNumber_arcLoop_eq_ite (z := z) hab hc hinj hin ha hb h1 h1'
    hz hzc
  have hw2 := fun {z} hz hzc => windingNumber_arcLoop_eq_ite (z := z) hab hc hinj hin ha' hb h2
    h2' hz hzc
  have hdiff := fun {z} hz hzc => windingNumber_arcLoop_eq_add_one (β := β) (z := z) hab.le hc hb
    hz hzc
  classical
  set s₁ := jordanSign (arcLoop c b z₀ r α β) a (b + 1)
  set s₂ := jordanSign (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1)
  have hs₁ := jordanSign_arcLoop_eq_one_or_neg_one hab hc hinj hin hr ha hb h1 h1'
  have hs₂ := jordanSign_arcLoop_eq_one_or_neg_one hab hc hinj hin hr ha' hb h2 h2'
  have key : ∀ z ∈ ball z₀ r, z ∉ c '' Icc a b →
      ((if z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) then s₁ else 0) : ℤ) =
        (if z ∈ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1)) then s₂ else 0)
          + 1 := by
    intro z hz hzc
    have h := hdiff hz hzc
    rw [hw1 hz hzc, hw2 hz hzc] at h
    split_ifs at h ⊢ <;> exact_mod_cast h
  have hc' : ContinuousOn c (Icc a b) := uIcc_of_le hab.le ▸ hc.continuousOn
  obtain ⟨z₁, hz₁, hz₁c, hz₁H⟩ := exists_mem_ball_arcLoop hab hc' hinj hin hr ha hb h1 h1'
  obtain ⟨z₂, hz₂, hz₂c, hz₂H⟩ := exists_mem_ball_arcLoop hab hc' hinj hin hr ha' hb h2 h2'
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
theorem jordanSign_arcLoop_eq_one (hab : a < b) (hc : IsPiecewiseC1On c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α < β)
    (hβα : β < α + 2 * π) :
    jordanSign (arcLoop c b z₀ r α β) a (b + 1) = 1 :=
  (jordanSign_arcLoop_and_mem_filledHull_iff hab hc hinj hin ha hb hαβ hβα).1

/-- The loop closed by the clockwise circle arc from `α` to `β - 2π` is negatively oriented. -/
theorem jordanSign_arcLoop_sub_two_pi_eq_neg_one (hab : a < b) (hc : IsPiecewiseC1On c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α < β)
    (hβα : β < α + 2 * π) :
    jordanSign (arcLoop c b z₀ r α (β - 2 * π)) a (b + 1) = -1 :=
  (jordanSign_arcLoop_and_mem_filledHull_iff hab hc hinj hin ha hb hαβ hβα).2.1

/-- Every point of the open disk off the arc `c` lies in exactly one of the filled hulls of the
loops closed by the counterclockwise and the clockwise circle arcs. -/
theorem mem_filledHull_arcLoop_iff_notMem (hab : a < b) (hc : IsPiecewiseC1On c a b)
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α) (hαβ : α < β)
    (hβα : β < α + 2 * π) {z : ℂ} (hz : z ∈ ball z₀ r) (hzc : z ∉ c '' Icc a b) :
    z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) ↔
      z ∉ filledHull (arcLoop c b z₀ r α (β - 2 * π) '' uIcc a (b + 1)) :=
  (jordanSign_arcLoop_and_mem_filledHull_iff hab hc hinj hin ha hb hαβ hβα).2.2 z hz hzc

end Orientation

end TauCeti.Contour
