/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Bounds
import TauCeti.Analysis.SpecialFunctions.Log.Deriv

/-!
# The inverse logarithm and the iterated logarithm near the origin

This file complements Mathlib's `Mathlib.Analysis.SpecialFunctions.Log.InvLog`, which records the
discontinuities of `x ↦ (log x)⁻¹` at `±1`, with its behaviour at the origin, the continuous
extension of `(log t)⁻¹ - (t - 1)⁻¹` across `t = 1`, the symmetric folded profile
`(log (1 + u))⁻¹ + (log (1 - u))⁻¹`, and bounds on the iterated logarithm `log log (1 / x)` near
the origin:

* `Real.continuousAt_inv_log_zero`: `(log x)⁻¹ → 0` as `x → 0`, so with Mathlib's conventions
  `log 0 = 0` and `0⁻¹ = 0` the function `x ↦ (log x)⁻¹` is continuous at the origin;
* `TauCeti.continuousAt_inv_log_sub_inv_sub_one_zero`,
  `TauCeti.tendsto_inv_log_sub_inv_sub_one_nhdsNE_one`,
  `TauCeti.continuousOn_update_inv_log_sub_inv_sub_one`,
  `TauCeti.exists_abs_inv_log_sub_inv_sub_one_le`: `(log t)⁻¹ - (t - 1)⁻¹` is continuous at
  `0` (with value `1`), tends to `1 / 2` as `t → 1`, `t ≠ 1`, extends continuously across
  `t = 1` on `[0, ∞)`, and is bounded in absolute value on `[a, b]` for `a ≥ 0`;
* `TauCeti.tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsNE_zero`,
  `TauCeti.continuousAt_inv_log_one_add_add_inv_log_one_sub_one`,
  `TauCeti.abs_inv_log_one_add_add_inv_log_one_sub_le`: the symmetric profile
  `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` tends to `1` as `u → 0`, `u ≠ 0`, is continuous at `1`, and
  satisfies `|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3` on `(0, 1 / 2]`;
* `Real.abs_log_log_inv_le`: for `0 ≤ x < e⁻¹`, `|log log (1 / x)| ≤ log (1 / x)`.

It also records the calculus of the radial profile `r ↦ log log (c / r)`, which for `c ≠ 0` has
an iterated-logarithmic singularity at the origin:

* `Real.hasDerivAt_log_log_const_div`: the derivative of `log log (c / r)` is `-(r log (c / r))⁻¹`
  wherever `r ∉ {0, c, -c}`;
* `Real.tendsto_log_log_const_div_nhdsNE_zero`: `log log (c / r) → ∞` as `r → 0`, for `c ≠ 0`.
-/

public section

open Filter Set Topology

namespace Real

/-- The function `x ↦ (log x)⁻¹` is continuous at the origin, where it takes the value `0`. -/
theorem continuousAt_inv_log_zero : ContinuousAt (fun x ↦ (log x)⁻¹) 0 := by
  rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
  simpa [Function.comp_def] using tendsto_inv_atBot_zero.comp tendsto_log_nhdsNE_zero

/-- For `0 ≤ x < e⁻¹`, `|log log (1 / x)| ≤ log (1 / x)`. -/
theorem abs_log_log_inv_le {x : ℝ} (hx : 0 ≤ x) (hx1 : x < exp (-1)) :
    |log (log x⁻¹)| ≤ -log x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hlog : log x < -1 := (log_lt_iff_lt_exp hx).2 hx1
  have hx' : 1 < log x⁻¹ := by rw [log_inv]; linarith
  rw [abs_of_pos (log_pos hx')]
  have := log_le_sub_one_of_pos (zero_lt_one.trans hx')
  rw [log_inv] at this ⊢
  linarith

/-- The derivative of the radial profile: `d/dr log log (c / r) = -(r log (c / r))⁻¹` wherever
`r ∉ {0, c, -c}`. For `c = 0` both sides vanish. -/
theorem hasDerivAt_log_log_const_div {c r : ℝ} (hr : r ≠ 0) (hrc : r ≠ c) (hrc' : r ≠ -c) :
    HasDerivAt (fun s : ℝ => log (log (c / s))) (-(r * log (c / r))⁻¹) r := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using hasDerivAt_const r (0 : ℝ)
  have h1 : c / r ≠ 1 := fun h => hrc ((div_eq_one_iff_eq hr).1 h).symm
  have h2 : c / r ≠ -1 := fun h => hrc' (by rw [div_eq_iff hr] at h; linarith)
  have hL : log (c / r) ≠ 0 := log_ne_zero.2 ⟨div_ne_zero hc hr, h1, h2⟩
  refine ((hasDerivAt_log_const_div hc hr).log hL).congr_deriv ?_
  field_simp

/-- The radial profile `log log (c / r)` tends to `∞` as `r → 0`, for `c ≠ 0`. -/
theorem tendsto_log_log_const_div_nhdsNE_zero {c : ℝ} (hc : c ≠ 0) :
    Tendsto (fun r : ℝ => log (log (c / r))) (𝓝[≠] 0) atTop := by
  have h : Tendsto (fun r : ℝ => log c + -log r) (𝓝[≠] 0) atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_neg_atBot_atTop.comp tendsto_log_nhdsNE_zero)
  refine tendsto_log_atTop.comp (h.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [log_div hc hr, sub_eq_add_neg]

end Real

namespace TauCeti

open _root_.Real

/-- `t ↦ (log t)⁻¹ - (t - 1)⁻¹` is continuous at `0`, where it takes the value `1`. -/
theorem continuousAt_inv_log_sub_inv_sub_one_zero :
    ContinuousAt (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) 0 :=
  continuousAt_inv_log_zero.sub (by fun_prop (disch := norm_num))

/-- `(log t)⁻¹ - (t - 1)⁻¹ → 1 / 2` as `t → 1`, `t ≠ 1`. -/
theorem tendsto_inv_log_sub_inv_sub_one_nhdsNE_one :
    Tendsto (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
  have hnum : Tendsto (fun t : ℝ ↦ (t - 1 - log t) / (t - 1) ^ 2) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE (f' := fun t : ℝ ↦ 1 - t⁻¹)
      (g' := fun t : ℝ ↦ 2 * (t - 1)) ?_ ?_ ?_ ?_ ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)] with t ht
      exact ((hasDerivAt_id' t).sub_const 1).sub (hasDerivAt_log ht.ne')
    · filter_upwards with t
      simpa using ((hasDerivAt_id' t).sub_const 1).fun_pow 2
    · filter_upwards [self_mem_nhdsWithin] with t (ht : t ≠ 1)
      exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr ht)
    · have hc : ContinuousAt (fun t : ℝ ↦ t - 1 - log t) 1 :=
        (continuousAt_id.sub continuousAt_const).sub (continuousAt_log one_ne_zero)
      simpa [log_one] using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hc : ContinuousAt (fun t : ℝ ↦ (t - 1) ^ 2) 1 := by fun_prop
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    · have hc : ContinuousAt (fun t : ℝ ↦ (2 * t)⁻¹) 1 := by fun_prop (disch := norm_num)
      have hlim : Tendsto (fun t : ℝ ↦ (2 * t)⁻¹) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
        simpa [one_div] using hc.tendsto.mono_left nhdsWithin_le_nhds
      refine hlim.congr' ?_
      filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin]
        with t ht0 (ht1 : t ≠ 1)
      have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
      field_simp [ht0.ne', hsub]
  have hden : Tendsto (fun t : ℝ ↦ log t / (t - 1)) (𝓝[≠] 1) (𝓝 1) := by
    have hd : HasDerivAt log 1 1 := by simpa using hasDerivAt_log one_ne_zero
    exact hd.tendsto_slope.congr fun t ↦ by simp [slope_def_field, log_one]
  have hq : Tendsto
      (fun t : ℝ ↦ ((t - 1 - log t) / (t - 1) ^ 2) / (log t / (t - 1)))
      (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    simpa [Pi.div_def] using hnum.div hden one_ne_zero
  refine hq.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds one_pos), self_mem_nhdsWithin] with t ht0 ht1
  have hlt : log t ≠ 0 := log_ne_zero_of_pos_of_ne_one ht0 ht1
  have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
  field_simp [hlt, hsub]

/-- Updating `t ↦ (log t)⁻¹ - (t - 1)⁻¹` by `1 / 2` at `t = 1` gives a continuous function on
`[0, ∞)`. -/
theorem continuousOn_update_inv_log_sub_inv_sub_one :
    ContinuousOn (Function.update (fun t : ℝ ↦ (log t)⁻¹ - (t - 1)⁻¹) 1 (1 / 2)) (Ici 0) := by
  rw [continuousOn_update_iff]
  refine ⟨fun t ⟨ht0, ht1⟩ ↦ ?_, fun _ ↦
    tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.mono_left
      (nhdsWithin_mono 1 fun _ h ↦ h.2)⟩
  rcases eq_or_lt_of_le ht0 with rfl | htpos
  · exact continuousAt_inv_log_sub_inv_sub_one_zero.continuousWithinAt
  · have htne : t ≠ 0 := htpos.ne'
    have hlt : log t ≠ 0 := log_ne_zero_of_pos_of_ne_one htpos ht1
    have hsub : t - 1 ≠ 0 := sub_ne_zero.mpr ht1
    exact (by fun_prop (disch := assumption) :
      ContinuousAt (fun u : ℝ ↦ (log u)⁻¹ - (u - 1)⁻¹) t).continuousWithinAt

/-- The regularized integrand `(log t)⁻¹ - (t - 1)⁻¹` is bounded in absolute value on every
compact interval `[a, b]` with `0 ≤ a`. -/
theorem exists_abs_inv_log_sub_inv_sub_one_le {a b : ℝ} (ha : 0 ≤ a) :
    ∃ C : ℝ, ∀ t ∈ Icc a b, |(log t)⁻¹ - (t - 1)⁻¹| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_update_inv_log_sub_inv_sub_one.mono fun t (ht : t ∈ Icc a b) ↦ ha.trans ht.1)
  refine ⟨max C 0, fun t ht ↦ ?_⟩
  rcases eq_or_ne t 1 with rfl | ht1
  · simp
  · calc |(log t)⁻¹ - (t - 1)⁻¹|
        = ‖Function.update (fun u : ℝ ↦ (log u)⁻¹ - (u - 1)⁻¹) 1 (1 / 2) t‖ := by
          rw [Function.update_of_ne ht1, norm_eq_abs]
      _ ≤ C := hC t ht
      _ ≤ max C 0 := le_max_left _ _

/-- The symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹` tends to `1` as `u → 0`,
`u ≠ 0`. -/
theorem tendsto_inv_log_one_add_add_inv_log_one_sub_nhdsNE_zero :
    Tendsto (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) (𝓝[≠] 0) (𝓝 1) := by
  have hp : Tendsto (fun u : ℝ ↦ (log (1 + u))⁻¹ - u⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun u : ℝ ↦ 1 + u) (𝓝[≠] 0) (𝓝[≠] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_const_add (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
          exact mem_compl_singleton_iff.mpr (by simpa using hu))
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).congr fun u ↦ ?_
    simp [Function.comp_apply]
  have hm : Tendsto (fun u : ℝ ↦ (log (1 - u))⁻¹ + u⁻¹) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    have h1 : Tendsto (fun u : ℝ ↦ 1 - u) (𝓝[≠] 0) (𝓝[≠] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((continuous_sub_left (1 : ℝ)).tendsto 0).mono_left nhdsWithin_le_nhds)
        (by
          filter_upwards [self_mem_nhdsWithin] with u (hu : u ≠ 0)
          exact mem_compl_singleton_iff.mpr (by simp [sub_eq_self, hu]))
    refine (tendsto_inv_log_sub_inv_sub_one_nhdsNE_one.comp h1).congr fun u ↦ ?_
    simp only [Function.comp_apply, sub_sub_cancel_left, inv_neg, sub_neg_eq_add]
  have hsum : Tendsto
      (fun u : ℝ ↦ ((log (1 + u))⁻¹ - u⁻¹) + ((log (1 - u))⁻¹ + u⁻¹))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa only [add_halves] using hp.add hm
  exact hsum.congr fun u ↦ by ring

/-- The symmetric integrand `u ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹` is continuous at `1`, where it
takes the value `(log 2)⁻¹`. -/
theorem continuousAt_inv_log_one_add_add_inv_log_one_sub_one :
    ContinuousAt (fun u : ℝ ↦ (log (1 + u))⁻¹ + (log (1 - u))⁻¹) 1 := by
  have h1 : ContinuousAt (fun u : ℝ ↦ (log (1 + u))⁻¹) 1 :=
    ((continuousAt_log (by norm_num)).comp (by fun_prop)).inv₀ (by
      have h11 : (1 : ℝ) + 1 = 2 := by norm_num
      dsimp only [Function.comp_apply]
      rw [h11]
      exact (log_pos one_lt_two).ne')
  have h2 : ContinuousAt (fun u : ℝ ↦ (log (1 - u))⁻¹) 1 := by
    have h0 : ContinuousAt (fun t : ℝ ↦ (log t)⁻¹) (1 - 1) := by
      simpa [sub_self] using continuousAt_inv_log_zero
    exact h0.comp (continuous_sub_left (1 : ℝ)).continuousAt
  exact h1.add h2

/-- Explicit bound on `(0, 1 / 2]` for the symmetric integrand `(log (1 + u))⁻¹ + (log (1 - u))⁻¹`:
`|(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3`. -/
theorem abs_inv_log_one_add_add_inv_log_one_sub_le {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |(log (1 + u))⁻¹ + (log (1 - u))⁻¹| ≤ 16 * log (4 / 3) / 3 := by
  have h1u : 0 < 1 + u := by linarith
  have h1mu : 0 < 1 - u := by linarith
  have hlp : 0 < log (1 + u) := log_pos (by linarith)
  have hlm : 0 < -log (1 - u) := neg_pos.mpr (log_neg h1mu (by linarith))
  -- Rewrite as `-log (1 - u^2) / (log (1 + u) * (-log (1 - u)))`.
  have hrew : (log (1 + u))⁻¹ + (log (1 - u))⁻¹ =
      -log (1 - u ^ 2) / (log (1 + u) * (-log (1 - u))) := by
    have hmul : log (1 + u) + log (1 - u) = log (1 - u ^ 2) := by
      rw [← log_mul h1u.ne' h1mu.ne']; ring_nf
    have hlm_ne : log (1 - u) ≠ 0 := (log_neg h1mu (by linarith)).ne
    field_simp [hlp.ne', hlm_ne]
    linarith [hmul]
  have hnum_nonneg : 0 ≤ -log (1 - u ^ 2) :=
    neg_nonneg.mpr (log_nonpos (by nlinarith) (by nlinarith))
  rw [abs_of_nonneg (by rw [hrew]; positivity), hrew]
  -- Lower bound `log (1 + u) ≥ (3 / 4) * u` by concavity of `log` on `[1, 3 / 2]`.
  have hlp_ge : 3 / 4 * u ≤ log (1 + u) := by
    have hlog32 : (3 / 8 : ℝ) ≤ log (3 / 2) := by linarith [lt_log_three_halves]
    have hconc : (1 - 2 * u) • log 1 + (2 * u) • log (3 / 2) ≤
        log ((1 - 2 * u) • 1 + (2 * u) • (3 / 2)) :=
      strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
        (by linarith) (by linarith) (by ring)
    simp only [smul_eq_mul, log_one, mul_zero, zero_add] at hconc
    have hcomb : (1 - 2 * u) * 1 + 2 * u * (3 / 2) = 1 + u := by ring
    rw [hcomb] at hconc
    nlinarith
  have hlm_ge : u ≤ -log (1 - u) := by linarith [log_le_sub_one_of_pos h1mu]
  -- Upper bound `-log (1 - u^2) ≤ 4 * log (4 / 3) * u^2` by concavity of `log` on `[3 / 4, 1]`.
  have hnum_le : -log (1 - u ^ 2) ≤ 4 * log (4 / 3) * u ^ 2 := by
    have hconc : (1 - 4 * u ^ 2) • log 1 + (4 * u ^ 2) • log (3 / 4) ≤
        log ((1 - 4 * u ^ 2) • 1 + (4 * u ^ 2) • (3 / 4)) :=
      strictConcaveOn_log_Ioi.concaveOn.2 (by norm_num) (by norm_num)
        (by nlinarith) (by positivity) (by ring)
    simp only [smul_eq_mul, log_one, mul_zero, zero_add] at hconc
    have hcomb : (1 - 4 * u ^ 2) * 1 + 4 * u ^ 2 * (3 / 4) = 1 - u ^ 2 := by ring
    have hlog34 : log (3 / 4 : ℝ) = -log (4 / 3) := by rw [← log_inv]; norm_num
    rw [hcomb, hlog34] at hconc
    linarith
  have hden_ge : 3 / 4 * u ^ 2 ≤ log (1 + u) * (-log (1 - u)) := by
    calc 3 / 4 * u ^ 2 = (3 / 4 * u) * u := by ring
      _ ≤ log (1 + u) * (-log (1 - u)) := mul_le_mul hlp_ge hlm_ge hu0.le hlp.le
  calc -log (1 - u ^ 2) / (log (1 + u) * (-log (1 - u)))
      ≤ (4 * log (4 / 3) * u ^ 2) / (3 / 4 * u ^ 2) :=
        div_le_div₀ (by have : 0 ≤ log (4 / 3) := log_nonneg (by norm_num); positivity)
          hnum_le (by positivity) hden_ge
    _ = 16 * log (4 / 3) / 3 := by field_simp [hu0.ne']; ring

end TauCeti
