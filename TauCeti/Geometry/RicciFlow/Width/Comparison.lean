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

Surgery events interrupt the comparison. At an event time `tⱼ` the width may exceed its upper
limit from the left by an error `eⱼ`. Chaining the normalized estimates through finitely many
events, each error enters with the weight `(1+4tⱼ)^(-3/4)`, which gives
`(1+4T)^(-3/4) W(T) ≤ W(0) + Σⱼ (1+4tⱼ)^(-3/4) eⱼ - 2π((1+4T)^(1/4)-1)` when the first epoch
starts at time zero. A bound `E` on the weighted error sum then bounds every time at which the
width is still nonnegative, explicitly in terms of the normalized initial width and `E`.

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

/-- The normalized restart estimate on a half-open epoch `[a, b)`, whose forward inequality is
only required for increments staying strictly before `b`. -/
private theorem ricciWidth_normalized_le_of_forward_lt {W : ℝ → ℝ} {a b : ℝ} (ha : 0 ≤ a)
    (hW : ContinuousOn W (Ico a b))
    (hforward : ∀ t ∈ Ico a b, ∀ η > 0, ∃ δ > 0, ∀ h, 0 < h → h < δ → t + h < b →
      (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η) :
    ∀ t ∈ Ico a b, (1 + 4 * t) ^ (-3 / 4 : ℝ) * W t ≤
      (1 + 4 * a) ^ (-3 / 4 : ℝ) * W a -
        2 * Real.pi * ((1 + 4 * t) ^ (1 / 4 : ℝ) - (1 + 4 * a) ^ (1 / 4 : ℝ)) := by
  intro t ht
  refine ricciWidth_normalized_le_of_forward_le ha (hW.mono (Icc_subset_Ico_right ht.2))
    (fun s hs η hη ↦ ?_) t ⟨ht.1, le_rfl⟩
  obtain ⟨δ, hδ, hb⟩ := hforward s ⟨hs.1, hs.2.trans ht.2⟩ η hη
  exact ⟨δ, hδ, fun h h0 hhδ hle ↦ hb h h0 hhδ (hle.trans_lt ht.2)⟩

/-- A normalized upper barrier on `[a, b)` passes to the event time `b`, up to the weighted
jump `e`, when `W b - e` is at most the upper limit of `W` from the left at `b`. -/
private theorem ricciWidth_normalized_le_of_frequently_le {W : ℝ → ℝ} {a b e C : ℝ}
    (ha : 0 ≤ a) (hab : a < b)
    (hbound : ∀ t ∈ Ico a b,
      (1 + 4 * t) ^ (-3 / 4 : ℝ) * W t ≤ C - 2 * Real.pi * (1 + 4 * t) ^ (1 / 4 : ℝ))
    (hjump : ∀ η > 0, ∃ᶠ s in 𝓝[<] b, W b ≤ W s + e + η) :
    (1 + 4 * b) ^ (-3 / 4 : ℝ) * W b ≤
      C - 2 * Real.pi * (1 + 4 * b) ^ (1 / 4 : ℝ) + (1 + 4 * b) ^ (-3 / 4 : ℝ) * e := by
  have hpos : 0 < (1 + 4 * b) ^ (-3 / 4 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hne : 1 + 4 * b ≠ 0 := by linarith
  -- Compare `W b - e - η` with the barrier at nearby earlier times, then let `η` tend to zero.
  have hη (η : ℝ) (hη : 0 < η) : (1 + 4 * b) ^ (-3 / 4 : ℝ) * (W b - e - η) ≤
      C - 2 * Real.pi * (1 + 4 * b) ^ (1 / 4 : ℝ) := by
    have hcont : ContinuousAt (fun s : ℝ ↦ C - 2 * Real.pi * (1 + 4 * s) ^ (1 / 4 : ℝ) -
        (1 + 4 * s) ^ (-3 / 4 : ℝ) * (W b - e - η)) b := by
      fun_prop (disch := exact Or.inl hne)
    have hfreq : ∃ᶠ s in 𝓝[<] b, 0 ≤ C - 2 * Real.pi * (1 + 4 * s) ^ (1 / 4 : ℝ) -
        (1 + 4 * s) ^ (-3 / 4 : ℝ) * (W b - e - η) :=
      (hjump η hη).mp (Filter.mem_of_superset (Ioo_mem_nhdsLT hab) fun s hs hjs ↦ by
        have hs0 : 0 ≤ (1 + 4 * s) ^ (-3 / 4 : ℝ) := Real.rpow_nonneg (by linarith [hs.1]) _
        have := mul_le_mul_of_nonneg_left (by linarith : W b - e - η ≤ W s) hs0
        linarith [hbound s (Ioo_subset_Ico_self hs)])
    have h := ge_of_tendsto_of_frequently (hcont.tendsto.mono_left nhdsWithin_le_nhds) hfreq
    linarith
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have h := hη (ε / (1 + 4 * b) ^ (-3 / 4 : ℝ)) (by positivity)
  rw [mul_sub, mul_div_cancel₀ _ hpos.ne'] at h
  linarith

/-- **Finite-event propagation of the width comparison.** Let `τ 0 < τ 1 < ⋯ < τ n` be event
times, with `0 ≤ τ 0`, and let `τ (n + 1)` bound the final epoch. On each epoch
`[τ k, τ (k + 1))` the function `W` is continuous and satisfies the upper forward width
inequality. At the event time `τ (k + 1)` its value exceeds the upper limit of `W` from the left
by at most `e k`. Then every later value obeys the normalized bound in which each event error
enters with the weight `(1 + 4 τ (k + 1)) ^ (-3/4)`. With no events (`n = 0`) this is the
regular-slab comparison on `[τ 0, τ 1)`. -/
theorem ricciWidth_normalized_le_of_forward_le_of_jump_le {W : ℝ → ℝ} {τ e : ℕ → ℝ} {n : ℕ}
    (hτ₀ : 0 ≤ τ 0) (hτ : ∀ k < n, τ k < τ (k + 1))
    (hW : ∀ k ≤ n, ContinuousOn W (Ico (τ k) (τ (k + 1))))
    (hforward : ∀ k ≤ n, ∀ t ∈ Ico (τ k) (τ (k + 1)), ∀ η > 0, ∃ δ > 0, ∀ h, 0 < h → h < δ →
      t + h < τ (k + 1) →
        (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η)
    (hjump : ∀ k < n, ∀ η > 0, ∃ᶠ s in 𝓝[<] τ (k + 1), W (τ (k + 1)) ≤ W s + e k + η) :
    ∀ t ∈ Ico (τ n) (τ (n + 1)), (1 + 4 * t) ^ (-3 / 4 : ℝ) * W t ≤
      (1 + 4 * τ 0) ^ (-3 / 4 : ℝ) * W (τ 0) +
        ∑ k ∈ Finset.range n, (1 + 4 * τ (k + 1)) ^ (-3 / 4 : ℝ) * e k -
        2 * Real.pi * ((1 + 4 * t) ^ (1 / 4 : ℝ) - (1 + 4 * τ 0) ^ (1 / 4 : ℝ)) := by
  -- Each epoch bound, restarted from the normalized bound at the epoch's initial time.
  have hepoch (m : ℕ) (hm : m ≤ n) (hτm : 0 ≤ τ m) {B : ℝ}
      (hB : (1 + 4 * τ m) ^ (-3 / 4 : ℝ) * W (τ m) ≤
        B - 2 * Real.pi * ((1 + 4 * τ m) ^ (1 / 4 : ℝ) - (1 + 4 * τ 0) ^ (1 / 4 : ℝ))) :
      ∀ t ∈ Ico (τ m) (τ (m + 1)), (1 + 4 * t) ^ (-3 / 4 : ℝ) * W t ≤
        B - 2 * Real.pi * ((1 + 4 * t) ^ (1 / 4 : ℝ) - (1 + 4 * τ 0) ^ (1 / 4 : ℝ)) := by
    intro t ht
    have h := ricciWidth_normalized_le_of_forward_lt hτm (hW m hm) (hforward m hm) t ht
    linarith
  -- Induct over the event times, crossing one event at each step.
  have hevent : ∀ m ≤ n, 0 ≤ τ m ∧ (1 + 4 * τ m) ^ (-3 / 4 : ℝ) * W (τ m) ≤
      (1 + 4 * τ 0) ^ (-3 / 4 : ℝ) * W (τ 0) +
        ∑ k ∈ Finset.range m, (1 + 4 * τ (k + 1)) ^ (-3 / 4 : ℝ) * e k -
        2 * Real.pi * ((1 + 4 * τ m) ^ (1 / 4 : ℝ) - (1 + 4 * τ 0) ^ (1 / 4 : ℝ)) := by
    intro m hm
    induction m with
    | zero => simp [hτ₀]
    | succ m ih =>
      obtain ⟨hτm, hm'⟩ := ih (by omega)
      have hlt := hτ m (by omega)
      have h := ricciWidth_normalized_le_of_frequently_le
        (C := (1 + 4 * τ 0) ^ (-3 / 4 : ℝ) * W (τ 0) +
          ∑ k ∈ Finset.range m, (1 + 4 * τ (k + 1)) ^ (-3 / 4 : ℝ) * e k +
          2 * Real.pi * (1 + 4 * τ 0) ^ (1 / 4 : ℝ))
        hτm hlt (fun t ht ↦ by linarith [hepoch m (by omega) hτm hm' t ht])
        (hjump m (by omega))
      refine ⟨hτm.trans hlt.le, ?_⟩
      rw [Finset.sum_range_succ]
      linarith
  obtain ⟨hτn, hn⟩ := hevent n le_rfl
  exact hepoch n le_rfl hτn hn

/-- **Extinction-time bound.** Under the hypotheses of finite-event propagation, suppose the
total weighted event error is at most `E`. Then every time `t` of the final epoch at which the
width is still nonnegative satisfies `t ≤ ((q₀ + (N₀ W(τ 0) + E) / (2π))^4 - 1) / 4`, where
`q₀ = (1 + 4 τ 0)^(1/4)` and `N₀ = (1 + 4 τ 0)^(-3/4)`. -/
theorem ricciWidth_time_le_of_forward_le_of_jump_le {W : ℝ → ℝ} {τ e : ℕ → ℝ} {n : ℕ}
    {E : ℝ} (hτ₀ : 0 ≤ τ 0) (hτ : ∀ k < n, τ k < τ (k + 1))
    (hW : ∀ k ≤ n, ContinuousOn W (Ico (τ k) (τ (k + 1))))
    (hforward : ∀ k ≤ n, ∀ t ∈ Ico (τ k) (τ (k + 1)), ∀ η > 0, ∃ δ > 0, ∀ h, 0 < h → h < δ →
      t + h < τ (k + 1) →
        (W (t + h) - W t) / h ≤ -2 * Real.pi + 3 * W t / (1 + 4 * t) + η)
    (hjump : ∀ k < n, ∀ η > 0, ∃ᶠ s in 𝓝[<] τ (k + 1), W (τ (k + 1)) ≤ W s + e k + η)
    (hE : ∑ k ∈ Finset.range n, (1 + 4 * τ (k + 1)) ^ (-3 / 4 : ℝ) * e k ≤ E)
    {t : ℝ} (ht : t ∈ Ico (τ n) (τ (n + 1))) (hWt : 0 ≤ W t) :
    t ≤ (((1 + 4 * τ 0) ^ (1 / 4 : ℝ) +
      ((1 + 4 * τ 0) ^ (-3 / 4 : ℝ) * W (τ 0) + E) / (2 * Real.pi)) ^ 4 - 1) / 4 := by
  have hmono : ∀ m ≤ n, τ 0 ≤ τ m := by
    intro m hm
    induction m with
    | zero => exact le_rfl
    | succ m ih => exact (ih (by omega)).trans (hτ m (by omega)).le
  have ht0 : 0 ≤ 1 + 4 * t := by linarith [hmono n le_rfl, ht.1]
  have hbound := ricciWidth_normalized_le_of_forward_le_of_jump_le hτ₀ hτ hW hforward hjump t ht
  have hnorm : 0 ≤ (1 + 4 * t) ^ (-3 / 4 : ℝ) * W t := mul_nonneg (by positivity) hWt
  have hpi : 0 < 2 * Real.pi := by positivity
  have hq : (1 + 4 * t) ^ (1 / 4 : ℝ) ≤ (1 + 4 * τ 0) ^ (1 / 4 : ℝ) +
      ((1 + 4 * τ 0) ^ (-3 / 4 : ℝ) * W (τ 0) + E) / (2 * Real.pi) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hpi]
    linarith
  have h4 : ((1 + 4 * t) ^ (1 / 4 : ℝ)) ^ 4 = 1 + 4 * t := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0]
    norm_num
  have hpow := pow_le_pow_left₀ (by positivity) hq 4
  rw [h4] at hpow
  linarith

end TauCeti
