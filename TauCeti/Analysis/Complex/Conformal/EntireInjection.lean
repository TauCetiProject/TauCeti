/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Complex.Conformal.LocalDegree

/-!
# Injective entire functions are affine

An entire function `f : ℂ → ℂ` is injective exactly when it is an affine map `z ↦ a z + b` with
`a ≠ 0` (`Differentiable.injective_iff_exists_eq_mul_add`). Thus the biholomorphisms of `ℂ` are
the affine maps.

The argument is the classical one. By the open mapping theorem the image of the unit disc is a
neighbourhood of `f 0`, which an injective `f` does not revisit outside the disc, so
`w ↦ (f (1 / w) - f 0)⁻¹` is bounded on the punctured unit disc. Its removable singularity at `0`
is a zero, since otherwise `f` would tend to a finite limit at infinity and be constant by
Liouville's theorem. That function is injective near `0`, so its derivative at `0` does not
vanish, which bounds `f` by a multiple of `‖z‖` at infinity. Liouville's theorem for functions
of polynomial growth (`Differentiable.exists_eq_polynomial_eval_of_isBigO_pow`) then makes `f` a
polynomial of degree at most one.

## Main results

* `Differentiable.exists_eq_mul_add_of_injective`: an injective entire function is affine.
* `Differentiable.injective_iff_exists_eq_mul_add`: an entire function is injective exactly when
  it is a nonconstant affine map.

## References

* J. B. Conway, *Functions of One Complex Variable I*, Springer GTM 11, on the conformal
  automorphisms of the plane.
-/

public section

open Filter Set Metric Bornology Topology Function

namespace Differentiable

variable {f : ℂ → ℂ}

/-- Off the unit disc an injective entire function stays a fixed distance away from its value
at `0`: the image of the unit disc is an open neighbourhood of `f 0`, which the function does not
enter again. -/
private theorem exists_pos_le_norm_sub_of_injective (hf : Differentiable ℂ f)
    (hinj : Injective f) : ∃ r > 0, ∀ z : ℂ, 1 ≤ ‖z‖ → r ≤ ‖f z - f 0‖ := by
  have hopen : IsOpenMap f := by
    refine (AnalyticOnNhd.is_constant_or_isOpenMap fun z _ => hf.analyticAt z).resolve_left ?_
    rintro ⟨w, hw⟩
    exact zero_ne_one (hinj ((hw 0).trans (hw 1).symm))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (hopen _ isOpen_ball) (f 0)
    ⟨0, mem_ball_self one_pos, rfl⟩
  refine ⟨r, hr, fun z hz => not_lt.1 fun hlt => ?_⟩
  obtain ⟨w, hw, hwz⟩ := hball (mem_ball_iff_norm.2 hlt)
  rw [hinj hwz, mem_ball_zero_iff] at hw
  exact hz.not_gt hw

/-- On the closed unit disc, a point `w ≠ 0` has `f (1 / w) ≠ f 0`, for `f` as in
`exists_pos_le_norm_sub_of_injective`. -/
private theorem sub_ne_zero_of_norm_le_one {r : ℝ} (hr : 0 < r)
    (hfar : ∀ z : ℂ, 1 ≤ ‖z‖ → r ≤ ‖f z - f 0‖) {w : ℂ} (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1) :
    f w⁻¹ - f 0 ≠ 0 := by
  refine norm_pos_iff.1 (hr.trans_le (hfar _ ?_))
  rw [norm_inv]
  exact (one_le_inv₀ (norm_pos_iff.2 hw)).2 hw1

/-- The inverted function `w ↦ (f (1 / w) - f 0)⁻¹` is holomorphic on the punctured closed unit
disc, for `f` as in `exists_pos_le_norm_sub_of_injective`. -/
private theorem differentiableAt_inv_sub (hf : Differentiable ℂ f) {r : ℝ} (hr : 0 < r)
    (hfar : ∀ z : ℂ, 1 ≤ ‖z‖ → r ≤ ‖f z - f 0‖) {w : ℂ} (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1) :
    DifferentiableAt ℂ (fun w => (f w⁻¹ - f 0)⁻¹) w :=
  (((hf w⁻¹).comp w (differentiableAt_inv hw)).sub_const (f 0)).inv
    (sub_ne_zero_of_norm_le_one hr hfar hw hw1)

/-- The inverted function `w ↦ (f (1 / w) - f 0)⁻¹` tends to `0` at `0`: its removable
singularity there is a zero. Otherwise `f` would have a finite limit at infinity, and so would be
constant by Liouville's theorem. -/
private theorem tendsto_inv_sub_nhdsNE_zero (hf : Differentiable ℂ f) (hinj : Injective f)
    {r : ℝ} (hr : 0 < r) (hfar : ∀ z : ℂ, 1 ≤ ‖z‖ → r ≤ ‖f z - f 0‖) :
    Tendsto (fun w => (f w⁻¹ - f 0)⁻¹) (𝓝[≠] 0) (𝓝 0) := by
  have hdisc : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ≠ 0 ∧ ‖w‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (closedBall_mem_nhds 0 one_pos)]
      with w hw hw1
    exact ⟨hw, mem_closedBall_zero_iff.1 hw1⟩
  have hd : ∀ᶠ w in 𝓝[≠] (0 : ℂ), DifferentiableAt ℂ (fun w => (f w⁻¹ - f 0)⁻¹) w :=
    hdisc.mono fun w hw => differentiableAt_inv_sub hf hr hfar hw.1 hw.2
  have hb : IsBoundedUnder (· ≤ ·) (𝓝[≠] (0 : ℂ))
      fun w => ‖(f w⁻¹ - f 0)⁻¹ - (f 0⁻¹ - f 0)⁻¹‖ := by
    refine isBoundedUnder_of_eventually_le (a := r⁻¹) (hdisc.mono fun w hw => ?_)
    rw [inv_zero, sub_self, inv_zero, sub_zero, norm_inv]
    have hnorm : 1 ≤ ‖w⁻¹‖ := by
      rw [norm_inv]
      exact (one_le_inv₀ (norm_pos_iff.2 hw.1)).2 hw.2
    exact inv_anti₀ hr (hfar _ hnorm)
  have hL := Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_bounded_under hd hb
  obtain hL0 | hL0 := eq_or_ne (limUnder (𝓝[≠] (0 : ℂ)) fun w => (f w⁻¹ - f 0)⁻¹) 0
  · rwa [hL0] at hL
  -- A nonzero limit gives `f` a finite limit at infinity.
  have hlim : Tendsto f (cocompact ℂ) (𝓝 (f 0 + (limUnder (𝓝[≠] (0 : ℂ))
      fun w => (f w⁻¹ - f 0)⁻¹)⁻¹)) := by
    rw [← Metric.cobounded_eq_cocompact]
    refine (tendsto_const_nhds.add ((hL.comp tendsto_inv₀_cobounded').inv₀ hL0)).congr
      fun z => ?_
    simp
  exact absurd (hinj ((hf.apply_eq_of_tendsto_cocompact 0 hlim).trans
    (hf.apply_eq_of_tendsto_cocompact 1 hlim).symm)) zero_ne_one

/-- **Injective entire functions are affine.** An injective holomorphic map `f : ℂ → ℂ` is
`z ↦ a z + b` for some `a ≠ 0`. -/
theorem exists_eq_mul_add_of_injective (hf : Differentiable ℂ f) (hinj : Injective f) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z = a * z + b := by
  obtain ⟨r, hr, hfar⟩ := exists_pos_le_norm_sub_of_injective hf hinj
  set φ : ℂ → ℂ := fun w => (f w⁻¹ - f 0)⁻¹
  have hφ0 : φ 0 = 0 := by simp [φ]
  -- `φ` is holomorphic on the unit disc, with its removable singularity at `0` filled by `0`.
  have hdiff : DifferentiableOn ℂ φ (ball 0 1) := by
    refine (Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (ball_mem_nhds 0 one_pos)).1 ⟨fun w hw => ?_, ?_⟩
    · exact (differentiableAt_inv_sub hf hr hfar hw.2
        (mem_ball_zero_iff.1 hw.1).le).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hφ0]
      exact tendsto_inv_sub_nhdsNE_zero hf hinj hr hfar
  -- `φ` is injective on the unit disc, so its derivative at `0` does not vanish.
  have hinjφ : InjOn φ (ball 0 1) := by
    have hne : ∀ w ∈ ball (0 : ℂ) 1, w ≠ 0 → φ w ≠ 0 := fun w hw hw0 =>
      inv_ne_zero (sub_ne_zero_of_norm_le_one hr hfar hw0 (mem_ball_zero_iff.1 hw).le)
    intro w hw w' hw' h
    obtain rfl | hw0 := eq_or_ne w 0
    · by_contra hw'0
      exact hne w' hw' (Ne.symm hw'0) (h.symm.trans hφ0)
    obtain rfl | hw'0 := eq_or_ne w' 0
    · exact absurd (h.trans hφ0) (hne w hw hw0)
    exact inv_injective (hinj (sub_left_injective (inv_injective h)))
  have hd : _root_.deriv φ 0 ≠ 0 :=
    TauCeti.deriv_ne_zero_of_injOn hdiff isOpen_ball hinjφ (mem_ball_self one_pos)
  -- Near `0`, `‖φ w‖` is at least half of `‖φ'(0)‖ ‖w‖`.
  have hslope : ∀ᶠ w in 𝓝 (0 : ℂ), ‖_root_.deriv φ 0‖ / 2 * ‖w‖ ≤ ‖φ w‖ := by
    have hc : ContinuousAt (dslope φ 0) 0 :=
      continuousAt_dslope_same.2 (hdiff.differentiableAt (ball_mem_nhds 0 one_pos))
    have hpos : 0 < ‖_root_.deriv φ 0‖ := norm_pos_iff.2 hd
    have hlt : ‖_root_.deriv φ 0‖ / 2 < ‖dslope φ 0 0‖ := by rw [dslope_same]; linarith
    filter_upwards [hc.norm.eventually (lt_mem_nhds hlt)] with w hw
    have hφw := sub_smul_dslope φ 0 w
    rw [sub_zero, hφ0, sub_zero, smul_eq_mul] at hφw
    rw [← hφw, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left hw.le (norm_nonneg w)
  -- Hence `‖f z - f 0‖ ≤ 2 ‖z‖ / ‖φ'(0)‖` at infinity, so `f` has linear growth.
  have hO : f =O[cobounded ℂ] (· ^ 1) := by
    have hpos : 0 < ‖_root_.deriv φ 0‖ := norm_pos_iff.2 hd
    refine Asymptotics.IsBigO.of_bound (‖f 0‖ + 2 / ‖_root_.deriv φ 0‖) ?_
    filter_upwards [tendsto_inv₀_cobounded.eventually hslope, eventually_cobounded_le_norm 1]
      with z hz hz1
    have hz0 : 0 < ‖z‖ := one_pos.trans_le hz1
    have hu : 0 < ‖f z - f 0‖ := hr.trans_le (hfar z hz1)
    simp only [φ, inv_inv, norm_inv] at hz
    have hbound : ‖f z - f 0‖ ≤ 2 / ‖_root_.deriv φ 0‖ * ‖z‖ := by
      rw [← inv_inv ‖f z - f 0‖]
      calc ‖f z - f 0‖⁻¹⁻¹ ≤ (‖_root_.deriv φ 0‖ / 2 * ‖z‖⁻¹)⁻¹ :=
            inv_anti₀ (by positivity) hz
        _ = 2 / ‖_root_.deriv φ 0‖ * ‖z‖ := by field_simp
    calc ‖f z‖ = ‖f 0 + (f z - f 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖f 0‖ + ‖f z - f 0‖ := norm_add_le _ _
      _ ≤ ‖f 0‖ * ‖z‖ + 2 / ‖_root_.deriv φ 0‖ * ‖z‖ := by
          gcongr
          exact le_mul_of_one_le_right (norm_nonneg _) hz1
      _ = (‖f 0‖ + 2 / ‖_root_.deriv φ 0‖) * ‖z ^ 1‖ := by rw [pow_one]; ring
  obtain ⟨p, hp, hfp⟩ := hf.exists_eq_polynomial_eval_of_isBigO_pow hO
  obtain ⟨a, b, rfl⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hp
  refine ⟨a, b, fun ha => zero_ne_one (hinj ?_), fun z => by simp [hfp]⟩
  simp [hfp, ha]

/-- **The biholomorphisms of `ℂ` are the affine maps.** An entire function is injective exactly
when it is `z ↦ a z + b` for some `a ≠ 0`. -/
theorem injective_iff_exists_eq_mul_add (hf : Differentiable ℂ f) :
    Injective f ↔ ∃ a b : ℂ, a ≠ 0 ∧ ∀ z, f z = a * z + b := by
  refine ⟨hf.exists_eq_mul_add_of_injective, ?_⟩
  rintro ⟨a, b, ha, hab⟩ z w h
  rw [hab, hab] at h
  exact mul_left_cancel₀ ha (add_right_cancel h)

end Differentiable
