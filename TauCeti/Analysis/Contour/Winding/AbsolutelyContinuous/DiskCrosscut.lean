/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On
public import TauCeti.Analysis.Contour.Crossing.Excision
public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Jordan
public import TauCeti.Topology.JordanCurve.Basic
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Concat
import TauCeti.Analysis.Contour.Winding.Number.Circle
import TauCeti.Analysis.Contour.Winding.Number.Reparam
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Circle
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import TauCeti.Topology.JordanCurve.Interval

/-!
# Crosscuts of a disk closed up by circle arcs

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

## Main results

* `TauCeti.Contour.arcLoop`: the arc `c` followed by a circle arc.
* `AbsolutelyContinuousOnInterval.arcLoop`: closing the arc preserves absolute continuity.
* `TauCeti.Contour.isJordanCurve_image_arcLoop`: the trace of the loop is a Jordan curve.
* `TauCeti.Contour.windingNumber_arcLoop`: decomposition into the original and circle arcs.
* `TauCeti.Contour.mem_filledHull_sdiff_image_arcLoop_iff`: the inside lies in the disk off `c`.
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

/-- The loop which follows `c` up to the parameter `b` and then, on `[b, b + 1]`, the arc of the
circle of center `z₀` and radius `r` from the angle `α` to the angle `β`. -/
def arcLoop (c : ℝ → ℂ) (b : ℝ) (z₀ : ℂ) (r α β : ℝ) (s : ℝ) : ℂ :=
  if s ≤ b then c s else circleCap z₀ r b (b + 1) α β s

variable {c : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {r α β : ℝ}

/-- Up to the parameter `b`, the loop is the arc `c`. -/
@[simp]
theorem arcLoop_of_le {s : ℝ} (hs : s ≤ b) : arcLoop c b z₀ r α β s = c s := ite_eq_left hs

/-- After the parameter `b`, the loop is the affinely reparametrized circle. -/
@[simp]
theorem arcLoop_of_lt {s : ℝ} (hs : b < s) :
    arcLoop c b z₀ r α β s = circleMap z₀ r (α + (s - b) * (β - α)) := by
  simp [arcLoop, hs.not_ge, circleCap_apply, mul_comm]

/-- At the parameter `b + 1`, the loop reaches the point of angle `β` of the circle. -/
theorem arcLoop_add_one : arcLoop c b z₀ r α β (b + 1) = circleMap z₀ r β := by
  rw [arcLoop, ite_eq_right (lt_add_one b).not_ge,
    circleCap_right z₀ r (lt_add_one b).ne α β]

/-- The loop agrees with the arc `c` near every parameter before `b`. -/
theorem arcLoop_eventuallyEq_of_lt {s : ℝ} (hs : s < b) : arcLoop c b z₀ r α β =ᶠ[𝓝 s] c :=
  (eventually_lt_nhds hs).mono fun _ h => arcLoop_of_le h.le

/-- The loop agrees with the affinely reparametrized circle near every parameter after `b`. -/
theorem arcLoop_eventuallyEq_of_gt {s : ℝ} (hs : b < s) :
    arcLoop c b z₀ r α β =ᶠ[𝓝 s] fun s => circleMap z₀ r (α + (s - b) * (β - α)) :=
  (eventually_gt_nhds hs).mono fun _ h => arcLoop_of_lt h

/-- Before the joining parameter, the derivative of the loop is that of the original arc. -/
@[simp]
theorem deriv_arcLoop_of_lt {s : ℝ} (hs : s < b) :
    deriv (arcLoop c b z₀ r α β) s = deriv c s :=
  (arcLoop_eventuallyEq_of_lt hs).deriv_eq

/-- After the joining parameter, the loop has the derivative of the affine circle arc. -/
theorem hasDerivAt_arcLoop_of_gt {s : ℝ} (hs : b < s) :
    HasDerivAt (arcLoop c b z₀ r α β)
      ((β - α) • (circleMap 0 r (α + (s - b) * (β - α)) * I)) s := by
  have hin : HasDerivAt (fun s : ℝ => α + (s - b) * (β - α)) (β - α) s := by
    simpa using ((hasDerivAt_id s).sub_const b).mul_const (β - α) |>.const_add α
  exact ((hasDerivAt_circleMap z₀ r _).scomp s hin).congr_of_eventuallyEq
    (arcLoop_eventuallyEq_of_gt hs)

/-- After the joining parameter, the derivative of the loop is the circle velocity times the
angular speed. -/
@[simp]
theorem deriv_arcLoop_of_gt {s : ℝ} (hs : b < s) :
    deriv (arcLoop c b z₀ r α β) s =
      (β - α) • (circleMap 0 r (α + (s - b) * (β - α)) * I) :=
  (hasDerivAt_arcLoop_of_gt hs).deriv

/-- Integrating along the original piece of the loop gives the integral along `c`. -/
theorem integral_arcLoop_left (f : ℂ → ℂ) (hab : a ≤ b) :
    ∫ s in a..b, f (arcLoop c b z₀ r α β s) * deriv (arcLoop c b z₀ r α β) s =
      ∫ s in a..b, f (c s) * deriv c s := by
  refine intervalIntegral.integral_congr_uIoo fun s hs => ?_
  rw [uIoo_of_le hab] at hs
  rw [arcLoop_of_le hs.2.le, deriv_arcLoop_of_lt hs.2]

/-- Integrating along the closing piece gives the integral along the circle from `α` to `β`,
for an arbitrary complex integrand. -/
theorem integral_arcLoop_circle (f : ℂ → ℂ) :
    ∫ s in b..b + 1, f (arcLoop c b z₀ r α β s) * deriv (arcLoop c b z₀ r α β) s =
      ∫ θ in α..β, f (circleMap z₀ r θ) * deriv (circleMap z₀ r) θ := by
  let g : ℝ → ℂ := fun θ => f (circleMap z₀ r θ) * deriv (circleMap z₀ r) θ
  have hcongr : EqOn (fun s => f (arcLoop c b z₀ r α β s) * deriv (arcLoop c b z₀ r α β) s)
      (fun s => ((β - α : ℝ) : ℂ) * g ((β - α) * s + (α - b * (β - α)))) (uIoo b (b + 1)) := by
    intro s hs
    rw [uIoo_of_le (lt_add_one b).le] at hs
    have hθ : (β - α) * s + (α - b * (β - α)) = α + (s - b) * (β - α) := by ring
    simp only [g, hθ, deriv_circleMap]
    rw [deriv_arcLoop_of_gt hs.1, arcLoop_of_lt hs.1, Complex.real_smul]
    ring
  rw [intervalIntegral.integral_congr_uIoo hcongr, intervalIntegral.integral_const_mul]
  rcases eq_or_ne β α with rfl | hd
  · simp
  rw [intervalIntegral.integral_comp_mul_add (f := g) (sub_ne_zero.mpr hd)]
  have h1 : (β - α) * b + (α - b * (β - α)) = α := by ring
  have h2 : (β - α) * (b + 1) + (α - b * (β - α)) = β := by ring
  rw [h1, h2, Complex.real_smul, ← mul_assoc, Complex.ofReal_inv,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (sub_ne_zero.mpr hd)), one_mul]

/-- The loop closed by a circle arc ending at the point where `c` starts is closed. -/
theorem arcLoop_eq_arcLoop_add_one (hab : a ≤ b) (ha : c a = circleMap z₀ r β) :
    arcLoop c b z₀ r α β a = arcLoop c b z₀ r α β (b + 1) := by
  rw [arcLoop_of_le hab, arcLoop_add_one, ha]

/-- Closing a piecewise `C¹` arc by a circle arc gives a piecewise `C¹` loop. -/
theorem isPiecewiseC1On_arcLoop (hc : IsPiecewiseC1On c a b) (hab : a ≤ b)
    (hb : c b = circleMap z₀ r α) : IsPiecewiseC1On (arcLoop c b z₀ r α β) a (b + 1) := by
  have harc : IsPiecewiseC1On (circleCap z₀ r b (b + 1) α β) b (b + 1) :=
    IsPiecewiseC1On.of_contDiffOn (contDiff_circleCap z₀ r b (b + 1) α β).contDiffOn
  exact hc.if_le harc hab (by linarith) (by simpa using hb)

/-- From the parameter `b` on, the loop is the affinely reparametrized circle, provided the arc `c`
ends at the point of angle `α`. -/
theorem eqOn_arcLoop_Ici (hb : c b = circleMap z₀ r α) :
    EqOn (arcLoop c b z₀ r α β) (circleCap z₀ r b (b + 1) α β) (Ici b) := by
  intro s hs
  rcases (mem_Ici.mp hs).eq_or_lt with rfl | hsb
  · simp [arcLoop, hb]
  · exact ite_eq_right hsb.not_ge

/-- Closing an absolutely continuous arc by a circle arc gives an absolutely continuous loop. -/
theorem _root_.AbsolutelyContinuousOnInterval.arcLoop (hc : AbsolutelyContinuousOnInterval c a b)
    (hab : a ≤ b) (hb : c b = circleMap z₀ r α) :
    AbsolutelyContinuousOnInterval (TauCeti.Contour.arcLoop c b z₀ r α β) a (b + 1) := by
  have hleft : AbsolutelyContinuousOnInterval (TauCeti.Contour.arcLoop c b z₀ r α β) a b :=
    hc.congr fun s hs => by
      rw [uIcc_of_le hab] at hs
      exact (arcLoop_of_le hs.2).symm
  have harc := (contDiff_circleCap z₀ r b (b + 1) α β).contDiffOn.absolutelyContinuousOnInterval
    (a := b) (b := b + 1)
  exact hleft.trans (harc.congr fun s hs => by
    rw [uIcc_of_le (le_add_of_nonneg_right zero_le_one)] at hs
    exact (eqOn_arcLoop_Ici hb hs.1).symm)

/-- Closing a continuous arc by a circle arc gives a continuous loop. -/
theorem continuousOn_arcLoop (hc : ContinuousOn c (Icc a b)) (hab : a ≤ b)
    (hb : c b = circleMap z₀ r α) : ContinuousOn (arcLoop c b z₀ r α β) (Icc a (b + 1)) := by
  rw [← Icc_union_Icc_eq_Icc hab (le_add_of_nonneg_right zero_le_one)]
  refine ContinuousOn.union_of_isClosed (hc.congr fun s hs => arcLoop_of_le hs.2) ?_
    isClosed_Icc isClosed_Icc
  exact (contDiff_circleCap z₀ r b (b + 1) α β).continuous.continuousOn.congr
    ((eqOn_arcLoop_Ici hb).mono Icc_subset_Ici_self)

/-- The trace of the loop is the trace of the arc together with the circle arc. -/
theorem image_arcLoop (hab : a ≤ b) (hb : c b = circleMap z₀ r α) :
    arcLoop c b z₀ r α β '' uIcc a (b + 1) = c '' Icc a b ∪ circleMap z₀ r '' uIcc α β := by
  have hb1 : b ≤ b + 1 := le_add_of_nonneg_right zero_le_one
  let f : ℝ →ᵃ[ℝ] ℝ := (AffineMap.lineMap α β).comp ((AffineMap.id ℝ ℝ) - AffineMap.const ℝ ℝ b)
  have hf : ∀ s, f s = α + (s - b) * (β - α) := fun s => by
    simp only [f, AffineMap.coe_comp, Function.comp_apply, FunLike.coe_sub, AffineMap.coe_id,
      AffineMap.coe_const, Pi.sub_apply, id_eq, Function.const_apply, AffineMap.lineMap_apply_ring']
    ring
  have hcircle : (fun s => circleMap z₀ r (α + (s - b) * (β - α))) = circleMap z₀ r ∘ f := by
    ext s
    simp [hf]
  rw [uIcc_of_le (hab.trans hb1), ← Icc_union_Icc_eq_Icc hab hb1, image_union,
    image_congr fun s (hs : s ∈ Icc a b) => arcLoop_of_le hs.2,
    image_congr (g := fun s => circleMap z₀ r (α + (s - b) * (β - α)))
      fun s (hs : s ∈ Icc b (b + 1)) =>
        (eqOn_arcLoop_Ici hb (Icc_subset_Ici_self hs)).trans
          (by simp [circleCap_apply, mul_comm]),
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

/-- If the interior of the injective arc `c` lies in the open disk, its endpoints lie on the
circle, and the closing circle arc is nontrivial and shorter than the full circle, then the loop
is injective on `[a, b + 1)`. -/
theorem injOn_arcLoop (hab : a < b) (hinj : InjOn c (Icc a b))
    (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α)
    (hβα : |β - α| < 2 * π) : InjOn (arcLoop c b z₀ r α β) (Ico a (b + 1)) := by
  have hr : 0 < r := pos_of_mem_ball (hin ((a + b) / 2) ⟨by linarith, by linarith⟩)
  have hαβ : α ≠ β := fun h => hab.ne (hinj (left_mem_Icc.mpr hab.le)
    (right_mem_Icc.mpr hab.le) (by rw [ha, hb, h]))
  have hsph : ∀ θ, circleMap z₀ r θ ∉ ball z₀ r := circleMap_notMem_ball z₀ r
  have hend : ∀ s ∈ Icc a b, c s ∉ ball z₀ r → s = a ∨ s = b := fun s hs h => by
    by_contra hne
    push Not at hne
    exact h (hin s ⟨lt_of_le_of_ne hs.1 hne.1.symm, lt_of_le_of_ne hs.2 hne.2⟩)
  have hangle : ∀ s ∈ Icc b (b + 1),
      α + (s - b) * (β - α) ∈ Ico (min α β) (min α β + 2 * π) := by
    intro s hs
    rcases le_total α β with h | h
    · rw [min_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)] at *
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr h),
        mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h)]
    · rw [min_eq_right h, abs_of_nonpos (sub_nonpos.mpr h)] at *
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hs.1) (sub_nonneg.mpr h),
        mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr h)]
  -- Prove injectivity of the whole closing cap once, including both endpoints.
  have harc : InjOn (circleCap z₀ r b (b + 1) α β) (Icc b (b + 1)) := by
    intro s hs s' hs' h
    simp only [circleCap_apply, add_sub_cancel_left, div_one] at h
    have heq := injOn_circleMap_of_abs_sub_le' hr.ne' (by linarith :
      min α β + 2 * π - min α β ≤ 2 * π) (hangle s hs) (hangle s' hs') (by
        simpa [mul_comm] using h)
    exact (mul_left_cancel₀ (sub_ne_zero.mpr hαβ.symm)
      (by linarith : (β - α) * s = (β - α) * s'))
  have hθα : ∀ s, b < s → s < b + 1 →
      circleMap z₀ r (α + (s - b) * (β - α)) ≠ circleMap z₀ r α := by
    intro s h1 h2 h
    have heq := harc ⟨h1.le, h2.le⟩ ⟨le_rfl, (lt_add_one b).le⟩ (by
      simpa [circleCap_apply, mul_comm] using h)
    exact h1.ne' heq
  have hθβ : ∀ s, b < s → s < b + 1 →
      circleMap z₀ r (α + (s - b) * (β - α)) ≠ circleMap z₀ r β := by
    intro s h1 h2 h
    have heq := harc ⟨h1.le, h2.le⟩ ⟨(lt_add_one b).le, le_rfl⟩ (by
      simpa [circleCap_apply, mul_comm] using h)
    exact h2.ne heq
  -- The original arc meets the cap only at its endpoints.
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
  · exact harc ⟨hsb.le, hs.2.le⟩ ⟨hs'b.le, hs'.2.le⟩
      (((eqOn_arcLoop_Ici hb hsb.le).symm.trans h).trans (eqOn_arcLoop_Ici hb hs'b.le))

/-- If the interior of the injective arc `c` lies in the open disk, its endpoints lie on the
circle, and the closing circle arc is nontrivial and shorter than the full circle, then the trace
of the loop is a Jordan curve. -/
theorem isJordanCurve_image_arcLoop (hab : a < b) (hc : ContinuousOn c (Icc a b))
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α)
    (hβα : |β - α| < 2 * π) :
    IsJordanCurve (arcLoop c b z₀ r α β '' uIcc a (b + 1)) := by
  rw [uIcc_of_le (by linarith)]
  exact isJordanCurve_image_Icc (by linarith) (continuousOn_arcLoop hc hab.le hb)
    (arcLoop_eq_arcLoop_add_one hab.le ha) (injOn_arcLoop hab hinj hin ha hb hβα)

/-- The inside of the closed-up crosscut is precisely its filled hull in the open disk off
`c`. This characterization needs only continuity of the crosscut. -/
theorem mem_filledHull_sdiff_image_arcLoop_iff (hab : a < b) (hc : ContinuousOn c (Icc a b))
    (hinj : InjOn c (Icc a b)) (hin : ∀ s ∈ Ioo a b, c s ∈ ball z₀ r)
    (ha : c a = circleMap z₀ r β) (hb : c b = circleMap z₀ r α)
    (hβα : |β - α| < 2 * π) {z : ℂ} :
    z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) \
        (arcLoop c b z₀ r α β '' uIcc a (b + 1)) ↔
      z ∈ ball z₀ r \ c '' Icc a b ∧
        z ∈ filledHull (arcLoop c b z₀ r α β '' uIcc a (b + 1)) := by
  have hr : 0 < r := pos_of_mem_ball (hin ((a + b) / 2) ⟨by linarith, by linarith⟩)
  constructor
  · intro hz
    have hJ := isJordanCurve_image_arcLoop hab hc hinj hin ha hb hβα
    have hzball : z ∈ ball z₀ r := by
      rw [← hJ.interior_filledHull] at hz
      rw [← interior_closedBall z₀ hr.ne']
      exact interior_mono (filledHull_image_arcLoop_subset_closedBall hab.le hin hr.le ha hb) hz
    refine ⟨⟨hzball, fun h => hz.2 ?_⟩, hz.1⟩
    rw [image_arcLoop hab.le hb]
    exact Or.inl h
  · rintro ⟨⟨hz, hzc⟩, hzH⟩
    exact ⟨hzH, notMem_image_arcLoop hab.le hb hz hzc⟩

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
