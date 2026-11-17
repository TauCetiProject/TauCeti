/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# The fundamental theorem of calculus for nonnegative derivatives

Mathlib's `intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le` evaluates `∫ x in a..b, f x` as
`F b - F a` for an antiderivative `F` that is continuous on `[a, b]`, provided `f` is interval
integrable. When `f` is nonnegative on `(a, b)` the integrability is automatic
(`intervalIntegral.integrableOn_deriv_of_nonneg`), which matters for integrands that are unbounded
at an endpoint, such as `1 / √(x - a)`. This file records the combined statement.

In the converse direction, FTC-1 recovers the derivative of a `T`-periodic function `x` from the
integral equation `x(t) - x(0) = ∫₀ᵗ Y` over a single period `[0, T]`, when `Y` is continuous and
`T`-periodic: periodicity propagates the equation to all of `ℝ`.

It also records that every point of a path lies within half its length of the midpoint of its
endpoints, and that along a loop `f` (with `f a = f b`) the integral of `B (f x) (f' x)` for a
continuous bilinear map `B` is unchanged by subtracting a constant from `f`, because `∫ f' = 0`.
Along a path that is not closed, subtracting the midpoint `m` of the endpoints changes it by
`B m (f b - f a)`, and the remaining integral is at most `‖B‖ / 2` times the squared length of the
path.

## Main declarations

* `TauCeti.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le_of_nonneg`
* `TauCeti.hasDerivAt_of_periodic_of_sub_eq_integral`
* `TauCeti.norm_sub_midpoint_le_integral_norm_div_two`
* `ContinuousLinearMap.intervalIntegral_apply_apply_eq_sub_const`
* `ContinuousLinearMap.norm_intervalIntegral_apply_apply_sub_apply_midpoint_le`
-/

public section

open MeasureTheory Set
open scoped Interval

namespace TauCeti

namespace intervalIntegral

/-- **FTC-2 for a nonnegative derivative.** If `F` is continuous on `[a, b]` and has derivative
`f x ≥ 0` at every `x ∈ (a, b)`, then `∫ x in a..b, f x = F b - F a`; the integrability of `f`
is a consequence rather than a hypothesis. -/
theorem integral_eq_sub_of_hasDerivAt_of_le_of_nonneg {F f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hF : ContinuousOn F (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt F (f x) x)
    (hf : ∀ x ∈ Ioo a b, 0 ≤ f x) : ∫ x in a..b, f x = F b - F a :=
  _root_.intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hF hd
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (_root_.intervalIntegral.integrableOn_deriv_of_nonneg hF hd hf))

end intervalIntegral

/-- **Periodic solutions of an integral equation.** Let `x` and a continuous `Y` be `T`-periodic,
with `T > 0`. If `x t - x 0 = ∫₀ᵗ Y` for every `t ∈ [0, T]`, then `x` has derivative `Y t` at every
`t`. -/
theorem hasDerivAt_of_periodic_of_sub_eq_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {x Y : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hxper : Function.Periodic x T) (hY : Continuous Y) (hYper : Function.Periodic Y T)
    (hint : ∀ t ∈ Icc 0 T, x t - x 0 = ∫ τ in 0..t, Y τ) (t : ℝ) : HasDerivAt x (Y t) t := by
  have hxT : x T = x 0 := by simpa using hxper 0
  have hintT : ∫ τ in 0..T, Y τ = 0 := by
    rw [← hint T ⟨hT.le, le_rfl⟩, hxT, sub_self]
  -- The difference of the two sides of the integral equation is periodic and vanishes on
  -- `[0, T)`, so it vanishes everywhere.
  have hall : ∀ t, x t = x 0 + ∫ τ in 0..t, Y τ := by
    set Φ : ℝ → E := fun t ↦ x 0 + (∫ τ in 0..t, Y τ) - x t
    have hΦper : Function.Periodic Φ T := fun t ↦ by
      have h := hYper.intervalIntegral_add_eq t 0
      rw [zero_add, hintT] at h
      simp only [Φ, hxper t]
      rw [← _root_.intervalIntegral.integral_add_adjacent_intervals (hY.intervalIntegrable 0 t)
        (hY.intervalIntegrable t (t + T)), h, add_zero]
    intro t
    obtain ⟨r, hr, htr⟩ := hΦper.exists_mem_Ico₀ hT t
    have h0 : Φ r = 0 := by
      simp only [Φ]
      rw [← hint r (Ico_subset_Icc_self hr)]
      abel
    exact (sub_eq_zero.1 (htr.trans h0)).symm
  have h := (_root_.intervalIntegral.integral_hasDerivAt_right (hY.intervalIntegrable 0 t)
    (hY.stronglyMeasurableAtFilter _ _) hY.continuousAt).const_add (x 0)
  exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall hall)

/-- Every point of a path `f` on `[a, b]` with integrable derivative `f'` lies within half its
length `∫ ‖f'‖` of the midpoint of its endpoints. -/
theorem norm_sub_midpoint_le_integral_norm_div_two {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {a b : ℝ} {f f' : ℝ → V} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) {x : ℝ} (hx : x ∈ Icc a b) :
    ‖f x - midpoint ℝ (f a) (f b)‖ ≤ (∫ t in a..b, ‖f' t‖) / 2 := by
  have hab : a ≤ b := hx.1.trans hx.2
  -- On a subinterval `[y, z]`, the displacement is at most the integral of the speed.
  have hnorm {y z : ℝ} (hy : a ≤ y) (hyz : y ≤ z) (hz : z ≤ b) :
      ‖f z - f y‖ ≤ ∫ t in y..z, ‖f' t‖ := by
    have hsub : Icc y z ⊆ Icc a b := Icc_subset_Icc hy hz
    refine norm_sub_le_integral_of_norm_deriv_le_of_le hyz
      (fun t ht ↦ (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hf t (hsub (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt)
      (Filter.Eventually.of_forall fun t ht ↦ (hf t (hsub (Ioo_subset_Icc_self ht))).deriv ▸ le_rfl)
      (hf'.norm.mono_set ?_)
    rw [uIcc_of_le hyz, uIcc_of_le hab]
    exact hsub
  have hax : uIcc a x ⊆ uIcc a b := by
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  have hxb : uIcc x b ⊆ uIcc a b := by
    rw [uIcc_of_le hx.2, uIcc_of_le hab]
    exact Icc_subset_Icc hx.1 le_rfl
  have hsplit : (∫ t in a..x, ‖f' t‖) + ∫ t in x..b, ‖f' t‖ = ∫ t in a..b, ‖f' t‖ :=
    _root_.intervalIntegral.integral_add_adjacent_intervals (hf'.norm.mono_set hax)
      (hf'.norm.mono_set hxb)
  have hmid : f x - midpoint ℝ (f a) (f b) =
      (1 / 2 : ℝ) • (f x - f a) - (1 / 2 : ℝ) • (f b - f x) := by
    rw [midpoint_eq_smul_add, invOf_eq_inv]
    module
  calc ‖f x - midpoint ℝ (f a) (f b)‖
      _ ≤ (1 / 2 : ℝ) * ‖f x - f a‖ + (1 / 2 : ℝ) * ‖f b - f x‖ := by
        rw [hmid]
        refine (norm_sub_le _ _).trans ?_
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
          le_refl]
      _ ≤ (1 / 2 : ℝ) * (∫ t in a..x, ‖f' t‖) + (1 / 2 : ℝ) * ∫ t in x..b, ‖f' t‖ := by
        gcongr
        · exact hnorm le_rfl hx.1 hx.2
        · exact hnorm hx.1 hx.2 le_rfl
      _ = (∫ t in a..b, ‖f' t‖) / 2 := by rw [← hsplit]; ring

end TauCeti

namespace ContinuousLinearMap

/-- Along a loop `f` (that is, `f a = f b`) continuous on `[a, b]` with derivative `f'` in the
interior, subtracting a constant from the first argument does not change the integral of
`B (f x) (f' x)`, since `∫ f' = f b - f a = 0`. -/
theorem intervalIntegral_apply_apply_eq_sub_const {V G : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [NormedAddCommGroup G] [NormedSpace ℝ G] (B : V →L[ℝ] V →L[ℝ] G) {a b : ℝ}
    {f f' : ℝ → V}
    (hfc : ContinuousOn f [[a, b]])
    (hf : ∀ x ∈ Ioo (min a b) (max a b), HasDerivAt f (f' x) x) (hfab : f a = f b)
    (hf'ii : IntervalIntegrable f' volume a b) (m : V) :
    ∫ x in a..b, B (f x) (f' x) = ∫ x in a..b, B (f x - m) (f' x) := by
  have hBm : IntervalIntegrable (fun x => B m (f' x)) volume a b :=
    ⟨(B m).integrable_comp hf'ii.1, (B m).integrable_comp hf'ii.2⟩
  -- Without completeness of `G` every integral in `G` vanishes.
  by_cases hG : CompleteSpace G
  swap
  · simp [intervalIntegral, integral_of_not_completeSpace hG]
  have hmean : ∫ x in a..b, B m (f' x) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right ((B m).continuous.comp_continuousOn hfc)
      (fun x hx => ((B m).hasFDerivAt.comp_hasDerivAt x (hf x hx)).hasDerivWithinAt) hBm]
    simp [hfab]
  by_cases hint : IntervalIntegrable (fun x => B (f x - m) (f' x)) volume a b
  · rw [← add_zero (∫ x in a..b, B (f x - m) (f' x)), ← hmean,
      ← intervalIntegral.integral_add hint hBm]
    simp [map_sub]
  · -- if `B (f x - m) (f' x)` is not integrable then neither is `B (f x) (f' x)`, as `B m (f' x)`
    -- is, and both integrals vanish
    have hfint : ¬ IntervalIntegrable (fun x => B (f x) (f' x)) volume a b := fun h =>
      hint (by simpa [map_sub] using h.sub hBm)
    rw [intervalIntegral.integral_undef hint, intervalIntegral.integral_undef hfint]

/-- Along a path `f` on `[a, b]` with integrable derivative `f'`, the integral of
`B (f x) (f' x)` for a continuous bilinear map `B` differs from `B m (f b - f a)`, where `m` is the
midpoint of the endpoints, by at most `‖B‖ / 2` times the square of the length `∫ ‖f'‖`. Every
point of the path lies within half its length of `m`. For a loop the correction term vanishes, and
for a skew form `B m (f b - f a) = B (f a) (f b)`. -/
theorem norm_intervalIntegral_apply_apply_sub_apply_midpoint_le {V G : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup G]
    [NormedSpace ℝ G] [CompleteSpace G] (B : V →L[ℝ] V →L[ℝ] G) {a b : ℝ} (hab : a ≤ b)
    {f f' : ℝ → V} (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hf' : IntervalIntegrable f' volume a b) :
    ‖(∫ x in a..b, B (f x) (f' x)) - B (midpoint ℝ (f a) (f b)) (f b - f a)‖ ≤
      ‖B‖ / 2 * (∫ x in a..b, ‖f' x‖) ^ 2 := by
  set m := midpoint ℝ (f a) (f b)
  set ℓ := ∫ x in a..b, ‖f' x‖
  have hfc : ContinuousOn f (Icc a b) := fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  have hℓ : 0 ≤ ℓ := _root_.intervalIntegral.integral_nonneg hab fun _ _ ↦ norm_nonneg _
  have hbound : IntervalIntegrable (fun x ↦ ‖B‖ * (ℓ / 2) * ‖f' x‖) volume a b :=
    hf'.norm.const_mul _
  have hpt (x : ℝ) (hx : x ∈ Icc a b) : ‖B (f x - m) (f' x)‖ ≤ ‖B‖ * (ℓ / 2) * ‖f' x‖ :=
    (B.le_opNorm₂ _ _).trans
      (by gcongr; exact TauCeti.norm_sub_midpoint_le_integral_norm_div_two hf hf' hx)
  have hint : IntervalIntegrable (fun x ↦ B (f x - m) (f' x)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at hbound hf' ⊢
    refine hbound.mono' (B.aestronglyMeasurable_comp₂
      (((hfc.mono Ioc_subset_Icc_self).sub continuousOn_const).aestronglyMeasurable
        measurableSet_Ioc) hf'.aestronglyMeasurable) ?_
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun x hx ↦ hpt x (Ioc_subset_Icc_self hx))
  have hBm : IntervalIntegrable (fun x ↦ B m (f' x)) volume a b :=
    ⟨(B m).integrable_comp hf'.1, (B m).integrable_comp hf'.2⟩
  -- Splitting off the constant `m` leaves the integral of `B m f' = B m (f b - f a)`.
  have hBmf : ∫ x in a..b, B m (f' x) = B m (f b - f a) := by
    rw [_root_.intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x ↦ B m (f x))
      (fun x hx ↦ (B m).hasFDerivAt.comp_hasDerivAt x (hf x (by rwa [uIcc_of_le hab] at hx))) hBm,
      map_sub]
  have hsplit : (∫ x in a..b, B (f x) (f' x)) - B m (f b - f a) =
      ∫ x in a..b, B (f x - m) (f' x) := by
    rw [← hBmf, ← _root_.intervalIntegral.integral_sub (by simpa [map_sub] using hint.add hBm) hBm]
    simp [map_sub]
  rw [hsplit]
  refine (_root_.intervalIntegral.norm_integral_le_of_norm_le hab
    (Filter.Eventually.of_forall fun x hx ↦ hpt x (Ioc_subset_Icc_self hx)) hbound).trans_eq ?_
  rw [_root_.intervalIntegral.integral_const_mul]
  ring

end ContinuousLinearMap
