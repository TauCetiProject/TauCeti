/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PlaneSeparation.Isoperimetric
public import TauCeti.Analysis.SpecialFunctions.CantorFunction
import TauCeti.Analysis.Contour.Curve.Circle.Basic
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Circle
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

/-!
# A circle parametrized through the Cantor function

Let `C` be the Cantor function and `φ t = (t + C t) / 2` (`TauCeti.cantorReparam`), an increasing
homeomorphism of `[0, 1]` that is not absolutely continuous. Running once around the unit circle
with angle `2π φ t` gives a curve `TauCeti.cantorCircle` on `[0, 1]` that is continuous, closed,
injective on `[0, 1)` and rectifiable, of length `2π`, but not absolutely continuous.

Such a curve lies outside the absolutely continuous form of the planar isoperimetric theorem, while
the bounded-variation form applies to it: its inside has area `A` and its length `L` satisfies the
equality `4π A = L²` (`TauCeti.four_pi_mul_volume_real_filledHull_sdiff_cantorCircle`).

## Main results

* `TauCeti.image_cantorCircle_Icc`: the trace of `cantorCircle` is the unit circle.
* `TauCeti.injOn_cantorCircle`: `cantorCircle` is injective on `[0, 1)`.
* `TauCeti.eVariationOn_cantorCircle`: `cantorCircle` has length `2π` on `[0, 1]`.
* `TauCeti.not_absolutelyContinuousOnInterval_cantorCircle`: `cantorCircle` is not absolutely
  continuous on `[0, 1]`.
* `TauCeti.four_pi_mul_volume_real_filledHull_sdiff_cantorCircle`: equality in the isoperimetric
  inequality for `cantorCircle`.
-/

public section

open Complex MeasureTheory Metric Set
open scoped Real

namespace TauCeti

/-- The unit circle traversed once on `[0, 1]` with angle `2π φ t`, where
`φ = TauCeti.cantorReparam` is built from the Cantor function. -/
noncomputable def cantorCircle : ℝ → ℂ := circleMap 0 1 ∘ fun t ↦ 2 * π * cantorReparam t

/-- Evaluation of `cantorCircle`. -/
theorem cantorCircle_apply (t : ℝ) : cantorCircle t = circleMap 0 1 (2 * π * cantorReparam t) :=
  (rfl)

/-- `cantorCircle` is continuous. -/
theorem continuous_cantorCircle : Continuous cantorCircle :=
  (continuous_circleMap 0 1).comp (continuous_const.mul cantorReparam.continuous)

/-- `cantorCircle` starts at `1`. -/
@[simp]
theorem cantorCircle_zero : cantorCircle 0 = 1 := by
  simp [cantorCircle_apply, circleMap]

/-- `cantorCircle` ends at `1`, so it is a closed curve on `[0, 1]`. -/
@[simp]
theorem cantorCircle_one : cantorCircle 1 = 1 := by
  simp [cantorCircle_apply, circleMap]

/-- The angle `2π φ t` of `cantorCircle` maps `[0, 1]` onto `[0, 2π]`. -/
private theorem image_two_pi_mul_cantorReparam_Icc :
    (fun t ↦ 2 * π * cantorReparam t) '' Icc 0 1 = Icc 0 (2 * π) := by
  rw [← image_image (2 * π * ·), OrderIso.image_Icc, cantorReparam_zero, cantorReparam_one,
    image_mul_left_Icc Real.two_pi_pos.le zero_le_one, mul_zero, mul_one]

/-- The trace of `cantorCircle` on `[0, 1]` is the unit circle. -/
theorem image_cantorCircle_Icc : cantorCircle '' Icc 0 1 = sphere 0 1 := by
  rw [cantorCircle, image_comp, image_two_pi_mul_cantorReparam_Icc,
    ← uIcc_of_le Real.two_pi_pos.le, image_circleMap_uIcc, abs_one]

/-- `cantorCircle` is injective on `[0, 1)`: it is a simple closed curve. -/
theorem injOn_cantorCircle : InjOn cantorCircle (Ico 0 1) := by
  refine (injOn_circleMap_of_abs_sub_le' one_ne_zero (a := 0) (b := 2 * π) (by simp)).comp
    ((mul_right_injective₀ Real.two_pi_pos.ne').comp cantorReparam.injective).injOn
    fun t ht ↦ ?_
  have h₀ := cantorReparam.monotone ht.1
  have h₁ := cantorReparam.strictMono ht.2
  simp only [cantorReparam_zero, cantorReparam_one] at h₀ h₁
  exact ⟨by positivity, by nlinarith [Real.two_pi_pos]⟩

/-- `cantorCircle` has length `2π` on `[0, 1]`. -/
theorem eVariationOn_cantorCircle :
    eVariationOn cantorCircle (Icc 0 1) = ENNReal.ofReal (2 * π) := by
  simpa using continuous_cantorCircle.continuousOn.eVariationOn_eq_of_image_eq_sphere
    (injOn_cantorCircle.mono Ioo_subset_Ico_self) image_cantorCircle_Icc

/-- `cantorCircle` has bounded variation on `[0, 1]`. -/
theorem boundedVariationOn_cantorCircle : BoundedVariationOn cantorCircle (Icc 0 1) := by
  rw [BoundedVariationOn, eVariationOn_cantorCircle]
  exact ENNReal.ofReal_ne_top

/-- `cantorCircle` is not absolutely continuous on `[0, 1]`. -/
theorem not_absolutelyContinuousOnInterval_cantorCircle :
    ¬ AbsolutelyContinuousOnInterval cantorCircle 0 1 := fun h ↦ by
  -- On each half of the parameter interval the angle stays in an open arc of length `2π`, so
  -- absolute continuity of the curve would pass to the angle, and hence to `cantorReparam`.
  set u := cantorReparam.symm (1 / 2)
  have hu : cantorReparam u = 1 / 2 := cantorReparam.apply_symm_apply _
  have hu₀ : 0 ≤ u := by
    rw [← cantorReparam.le_iff_le, hu, cantorReparam_zero]; norm_num
  have hu₁ : u ≤ 1 := by
    rw [← cantorReparam.le_iff_le, hu, cantorReparam_one]; norm_num
  rw [cantorCircle] at h
  -- On a subinterval where the increasing angle stays in an open arc of length `2π`, absolute
  -- continuity passes from the curve to the angle.
  have hangle {s t θ₀ : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
      (h₀ : θ₀ - π < 2 * π * cantorReparam s) (h₁ : 2 * π * cantorReparam t < θ₀ + π) :
      AbsolutelyContinuousOnInterval (fun x ↦ 2 * π * cantorReparam x) s t := by
    refine (absolutelyContinuousOnInterval_circleMap_comp_iff (θ₀ := θ₀) one_ne_zero
      fun x hx ↦ ?_).1 (h.mono (uIcc_subset_uIcc (by simp [hs, hst.trans ht])
        (by simp [hs.trans hst, ht])))
    rw [uIcc_of_le hst] at hx
    have := cantorReparam.monotone hx.1
    have := cantorReparam.monotone hx.2
    constructor <;> nlinarith [Real.pi_pos]
  -- The angle lies in `[0, π]` on `[0, u]` and in `[π, 2π]` on `[u, 1]`.
  have h₁ := hangle (θ₀ := π / 2) le_rfl hu₀ hu₁ (by simp [Real.pi_pos])
    (by rw [hu]; linarith [Real.pi_pos])
  have h₂ := hangle (θ₀ := 3 * π / 2) hu₀ hu₁ le_rfl (by rw [hu]; linarith [Real.pi_pos])
    (by simp; linarith [Real.pi_pos])
  refine not_absolutelyContinuousOnInterval_cantorReparam
    (((h₁.trans h₂).const_mul (2 * π)⁻¹).congr fun t _ ↦ ?_)
  field_simp

/-- **Equality in the isoperimetric inequality for `cantorCircle`.** The inside of the unit circle
has area `A` with `4π A = L²`, where `L` is the total variation of `cantorCircle` on `[0, 1]`. The
bounded-variation form of the isoperimetric theorem applies although `cantorCircle` is not
absolutely continuous. -/
theorem four_pi_mul_volume_real_filledHull_sdiff_cantorCircle :
    4 * π * volume.real (filledHull (cantorCircle '' Icc 0 1) \ cantorCircle '' Icc 0 1) =
      (eVariationOn cantorCircle (Icc 0 1)).toReal ^ 2 :=
  (boundedVariationOn_cantorCircle.four_pi_mul_volume_real_filledHull_sdiff_eq_iff zero_lt_one
    continuous_cantorCircle.continuousOn (by simp) injOn_cantorCircle).2
      ⟨0, 1, one_pos, image_cantorCircle_Icc⟩

end TauCeti
