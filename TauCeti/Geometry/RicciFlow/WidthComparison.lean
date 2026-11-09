/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The scalar comparison for Ricci-flow extinction

The width inequality in a smooth epoch of three-dimensional Ricci flow has the form
`D⁺W(t) ≤ -2π + 3W(t)/(1+4t)`. We prove its regular-slab comparison for continuous
functions, using the upper forward-difference formulation, not assuming differentiability
of the width. The comparison restarts at any nonnegative time. Multiplication by
`(1+4t)^(-3/4)` gives the normalized bound used to propagate estimates across epochs.

The explicit comparison profile eventually becomes negative for every finite initial value.
Consequently a nonnegative continuous function cannot satisfy this width inequality for all
nonnegative times. These are scalar statements: no existence of a geometric flow or width
estimate is asserted here.

The argument follows Morgan–Tian, *Ricci Flow and the Poincaré Conjecture* (2007),
Proposition 18.18 and the proof of Theorem 18.1. The comparison uses Mathlib's
`image_le_of_liminf_slope_right_lt_deriv_boundary'` with a strict perturbation of the barrier.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- The zero-event-error width profile with initial value `w` at time zero. -/
noncomputable def ricciWidthProfile (w t : ℝ) : ℝ :=
  (w + 2 * Real.pi) * (1 + 4 * t) ^ (3 / 4 : ℝ) - 2 * Real.pi * (1 + 4 * t)

/-- The explicit formula for the zero-event-error profile. -/
theorem ricciWidthProfile_def (w t : ℝ) :
    ricciWidthProfile w t =
      (w + 2 * Real.pi) * (1 + 4 * t) ^ (3 / 4 : ℝ) - 2 * Real.pi * (1 + 4 * t) :=
  (rfl)

/-- The comparison profile starts at the prescribed width. -/
@[simp]
theorem ricciWidthProfile_zero (w : ℝ) : ricciWidthProfile w 0 = w := by
  simp [ricciWidthProfile]

/-- The profile solves the scalar equation with forcing term `-2π`. -/
theorem hasDerivAt_ricciWidthProfile (w : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (ricciWidthProfile w)
      (-2 * Real.pi + 3 * ricciWidthProfile w t / (1 + 4 * t)) t := by
  have hpos : 0 < 1 + 4 * t := by positivity
  have hlin := ((hasDerivAt_id t).const_mul 4).const_add 1
  convert ((hlin.rpow_const (p := (3 / 4 : ℝ)) (Or.inl hpos.ne')).const_mul
    (w + 2 * Real.pi)).sub (hlin.const_mul (2 * Real.pi)) using 1
  · rfl
  · dsimp [ricciWidthProfile]
    rw [Real.rpow_sub hpos, Real.rpow_one]
    field_simp
    ring

/-- The integrating factor converts the profile to an affine function of `(1+4t)^(1/4)`. -/
theorem mul_ricciWidthProfile (w : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (1 + 4 * t) ^ (-3 / 4 : ℝ) * ricciWidthProfile w t =
      w + 2 * Real.pi - 2 * Real.pi * (1 + 4 * t) ^ (1 / 4 : ℝ) := by
  have hpos : 0 < 1 + 4 * t := by positivity
  have hcancel : (1 + 4 * t) ^ (-3 / 4 : ℝ) * (1 + 4 * t) ^ (3 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hpos]
    norm_num
  have hquarter : (1 + 4 * t) ^ (-3 / 4 : ℝ) * (1 + 4 * t) =
      (1 + 4 * t) ^ (1 / 4 : ℝ) := by
    nth_rw 2 [← Real.rpow_one (1 + 4 * t)]
    rw [← Real.rpow_add hpos]
    norm_num
  dsimp [ricciWidthProfile]
  calc
    _ = (w + 2 * Real.pi) *
        ((1 + 4 * t) ^ (-3 / 4 : ℝ) * (1 + 4 * t) ^ (3 / 4 : ℝ)) -
        2 * Real.pi * ((1 + 4 * t) ^ (-3 / 4 : ℝ) * (1 + 4 * t)) := by ring
    _ = _ := by rw [hcancel, hquarter]; ring

/-- A continuous function satisfying the upper forward width inequality stays below any
comparison profile that bounds it at the initial time. The derivative hypothesis is required
only before the right endpoint, and the conclusion includes both endpoints. -/
theorem le_ricciWidthProfile_of_forward_le {W : ℝ → ℝ} {a b w : ℝ} (ha : 0 ≤ a)
    (hW : ContinuousOn W (Icc a b)) (hinit : W a ≤ ricciWidthProfile w a)
    (hforward : ∀ t ∈ Ico a b, ∀ η > 0, ∃ δ > 0, ∀ h, 0 < h → h < δ → t + h ≤ b →
      (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η) :
    ∀ t ∈ Icc a b, W t ≤ ricciWidthProfile w t := by
  have hslope : ∀ t ∈ Ico a b, ∀ r,
      -2 * Real.pi + 3 * W t / (1 + 4 * t) < r →
      ∃ᶠ z in 𝓝[>] t, slope W t z < r := by
    intro t ht r hr
    obtain ⟨δ, hδ, hbound⟩ := hforward t ht
      ((r - (-2 * Real.pi + 3 * W t / (1 + 4 * t))) / 2) (by linarith)
    apply Filter.Eventually.frequently
    filter_upwards [Ioo_mem_nhdsGT (lt_min ht.2 (by linarith : t < t + δ))] with z hz
    have h := hbound (z - t) (by linarith [hz.1]) (by linarith [(lt_min_iff.mp hz.2).2])
      (by linarith [(lt_min_iff.mp hz.2).1])
    simp only [add_sub_cancel] at h
    rw [slope_def_field]
    linarith
  have hperturb (ε : ℝ) (hε : 0 < ε) :
      ∀ t ∈ Icc a b, W t ≤ ricciWidthProfile w t + ε * (1 + 4 * t) := by
    apply image_le_of_liminf_slope_right_lt_deriv_boundary' hW hslope
    · exact hinit.trans (le_add_of_nonneg_right (by positivity))
    · exact fun t ht ↦ ((hasDerivAt_ricciWidthProfile w (ha.trans ht.1)).continuousAt.add
        (by fun_prop)).continuousWithinAt
    · intro t ht
      exact ((hasDerivAt_ricciWidthProfile w (ha.trans ht.1)).add
        ((((hasDerivAt_id t).const_mul 4).const_add 1).const_mul ε)).hasDerivWithinAt
    · intro t ht heq
      have hpos : 0 < 1 + 4 * t := by linarith [ht.1]
      rw [heq]
      field_simp
      nlinarith
  intro t ht
  have hc : ContinuousWithinAt
      (fun ε : ℝ ↦ ricciWidthProfile w t + ε * (1 + 4 * t)) (Ioi 0) 0 := by fun_prop
  have h := continuousWithinAt_const.closure_le (by simp) hc (fun ε hε ↦ hperturb ε hε t ht)
  simpa using h

/-- The normalized regular-slab comparison, restarted at any nonnegative time `a`.
No sign assumption on `W` is needed for comparison. -/
theorem ricciWidth_normalized_le_of_forward_le {W : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hW : ContinuousOn W (Icc a b))
    (hforward : ∀ t ∈ Ico a b, ∀ η > 0, ∃ δ > 0, ∀ h, 0 < h → h < δ → t + h ≤ b →
      (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η) :
    ∀ t ∈ Icc a b, (1 + 4 * t) ^ (-3 / 4 : ℝ) * W t ≤
      (1 + 4 * a) ^ (-3 / 4 : ℝ) * W a -
        2 * Real.pi * ((1 + 4 * t) ^ (1 / 4 : ℝ) - (1 + 4 * a) ^ (1 / 4 : ℝ)) := by
  let w := (1 + 4 * a) ^ (-3 / 4 : ℝ) * W a +
    2 * Real.pi * (1 + 4 * a) ^ (1 / 4 : ℝ) - 2 * Real.pi
  have heq : W a = ricciWidthProfile w a := by
    have h := mul_ricciWidthProfile w ha
    have hpos : 0 < (1 + 4 * a) ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
    apply (mul_left_cancel₀ hpos.ne' (b := W a) (c := ricciWidthProfile w a))
    rw [h]
    dsimp [w]
    ring
  have hcomp := le_ricciWidthProfile_of_forward_le ha hW heq.le hforward
  intro t ht
  have h := mul_le_mul_of_nonneg_left (hcomp t ht)
    (Real.rpow_nonneg (by linarith [ht.1] : 0 ≤ 1 + 4 * t) (-3 / 4 : ℝ))
  rw [mul_ricciWidthProfile w (ha.trans ht.1)] at h
  dsimp [w] at h
  linarith

/-- Every finite initial width gives an eventually negative comparison profile. -/
theorem eventually_ricciWidthProfile_neg (w : ℝ) :
    ∀ᶠ t in atTop, ricciWidthProfile w t < 0 := by
  have hlin : Tendsto (fun t : ℝ ↦ 1 + 4 * t) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 4))
  have hgrow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlin
  filter_upwards [eventually_ge_atTop (0 : ℝ),
    hgrow.eventually (eventually_gt_atTop ((w + 2 * Real.pi) / (2 * Real.pi)))] with t ht hg
  simp only [Function.comp_apply] at hg
  have hnorm := mul_ricciWidthProfile w ht
  have hpi : 0 < 2 * Real.pi := by positivity
  have hneg : w + 2 * Real.pi - 2 * Real.pi * (1 + 4 * t) ^ (1 / 4 : ℝ) < 0 := by
    have := (div_lt_iff₀ hpi).1 hg
    nlinarith
  have hpos : 0 < (1 + 4 * t) ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  nlinarith

/-- A nonnegative continuous width cannot obey the forward inequality for all future times.
This is the scalar contradiction behind finite extinction, without surgery events. -/
theorem not_forall_ricciWidth_forward_le {W : ℝ → ℝ}
    (hW : ContinuousOn W (Ici 0)) (hnonneg : ∀ t ∈ Ici 0, 0 ≤ W t) :
    ¬ (∀ t ∈ Ici 0, ∀ η > 0, ∃ δ > 0, ∀ h, 0 < h → h < δ →
      (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η) := by
  intro hforward
  obtain ⟨t, ht, hneg⟩ := ((eventually_ge_atTop (0 : ℝ)).and
    (eventually_ricciWidthProfile_neg (W 0))).exists
  have hbound := le_ricciWidthProfile_of_forward_le (a := 0) (b := t) (w := W 0)
    le_rfl (hW.mono (fun _ hx ↦ hx.1)) (by simp) (fun s hs η hη ↦ by
      obtain ⟨δ, hδ, hb⟩ := hforward s hs.1 η hη
      exact ⟨δ, hδ, fun h hh hhδ _ ↦ hb h hh hhδ⟩) t ⟨ht, le_rfl⟩
  linarith [hnonneg t ht]

end TauCeti
