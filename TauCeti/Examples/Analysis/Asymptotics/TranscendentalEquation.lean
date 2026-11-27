/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import TauCeti.Analysis.Asymptotics.TranscendentalEquation

/-!
# Successive resubstitution for `t² - log t = y` (DLMF 2.2.3–2.2.6)

DLMF's example of the method of successive resubstitution. For `y > ½ (1 + log 2)` the equation
`t² - log t = y` has a unique root `t > 2^{-1/2}` (DLMF 2.2.3). In the variable `x = t²` it reads
`x - ½ log x = y`, and `x ↦ x - ½ log x` is continuous and strictly increasing on `[½, ∞)` and
asymptotic to the identity, so the inversion theorem of DLMF 2.2.1–2.2.2
(`ContinuousOn.existsUnique_root_of_isEquivalent`, `MonotoneOn.root_isEquivalent`) applies.
Substituting the leading approximation `t ∼ y^{1/2}` back into `t² = y + log t` gives the
correction `t² = y + ½ log y + o(1)` for `t²`. The correction for `t` itself follows by factoring
`t² - y = (t - y^{1/2}) (t + y^{1/2})`: then `t - y^{1/2} = log t / (t + y^{1/2}) → 0`, and the
normalized remainder of DLMF 2.2.6 equals `((t² - y - ½ log y) - (t - y^{1/2})²) / 2`.

The asymptotic results hold for any function `t` that is eventually a root with `t ≥ a`, for a
fixed `a > 0`: for large `y` the equation also has a small root near `e^{-y}`, and any positive
lower bound eventually excludes it.

## Main results

All in the namespace `TauCeti.Examples.TranscendentalEquation`:

* `existsUnique_sq_sub_log_eq`: existence and uniqueness of the root (DLMF 2.2.3).
* `sq_sub_log_root_isEquivalent`: `t ∼ y^{1/2}` as `y → ∞` (DLMF 2.2.4).
* `isLittleO_sq_sub_log_root_sq_remainder`: `t² = y + ½ log y + o(1)` (DLMF 2.2.5).
* `isLittleO_sq_sub_log_root_remainder`: `t = y^{1/2} (1 + ¼ y⁻¹ log y + o(y⁻¹))` (DLMF 2.2.6).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.2, <https://dlmf.nist.gov/2.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/AsymptoticApproximations/Basics/Transcendental.lean`.
-/

public section

open Filter Real Set Asymptotics
open scoped Topology

namespace TauCeti.Examples.TranscendentalEquation

/-- `x ↦ x - ½ log x` is strictly increasing on `[½, ∞)`. -/
private lemma strictMonoOn_sub_log_div_two :
    StrictMonoOn (fun x : ℝ => x - log x / 2) (Ici (1 / 2)) := by
  intro x hx y _ hxy
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hlt : log (y / x) < y / x - 1 :=
    log_lt_sub_one_of_pos (div_pos (hx0.trans hxy) hx0) ((one_lt_div hx0).mpr hxy).ne'
  rw [log_div (hx0.trans hxy).ne' hx0.ne', div_sub_one hx0.ne', lt_div_iff₀ hx0] at hlt
  dsimp only
  nlinarith [mem_Ici.mp hx]

/-- `x - ½ log x ∼ x` as `x → ∞`. -/
private lemma sub_log_div_two_isEquivalent : (fun x : ℝ => x - log x / 2) ~[atTop] id :=
  (IsEquivalent.refl.sub_isLittleO (isLittleO_log_id_atTop.const_mul_left (1 / 2))).congr_left
    (Eventually.of_forall fun x => by simp [div_eq_inv_mul])

/-- The cutoff `2^{-1/2}` squares to `½`. -/
private lemma inv_sqrt_two_sq : ((√2)⁻¹ : ℝ) ^ 2 = 1 / 2 := by
  rw [inv_pow, sq_sqrt (by norm_num), one_div]

/-- A root `t > 2^{-1/2}` of `t² - log t = y` gives the root `x = t² > ½` of `x - ½ log x = y`. -/
private lemma half_lt_sq_and_sub_log_div_two_eq {t y : ℝ} (ht : (√2)⁻¹ < t)
    (hty : t ^ 2 - log t = y) :
    1 / 2 < t ^ 2 ∧ t ^ 2 - log (t ^ 2) / 2 = y := by
  refine ⟨?_, ?_⟩
  · rw [← inv_sqrt_two_sq]
    exact pow_lt_pow_left₀ ht (by positivity) two_ne_zero
  · rw [log_pow]
    push_cast
    linarith

/-- DLMF 2.2.3: for every `y > ½ (1 + log 2)` the equation `t² - log t = y` has a unique root
`t > 2^{-1/2}`. -/
theorem existsUnique_sq_sub_log_eq {y : ℝ} (hy : (1 + log 2) / 2 < y) :
    ∃! t : ℝ, (√2)⁻¹ < t ∧ t ^ 2 - log t = y := by
  have hf0 : (fun x : ℝ => x - log x / 2) (1 / 2) < y := by
    simp only [one_div, log_inv]
    linarith
  have hcont : ContinuousOn (fun x : ℝ => x - log x / 2) (Ici (1 / 2)) :=
    continuousOn_id.sub ((continuousOn_log.mono fun x hx =>
      (lt_of_lt_of_le (by norm_num) (mem_Ici.mp hx)).ne').div_const 2)
  obtain ⟨x, ⟨hx, hfx⟩, hu⟩ := hcont.existsUnique_root_of_isEquivalent
    strictMonoOn_sub_log_div_two sub_log_div_two_isEquivalent hf0
  have hx0 : 0 < x := lt_trans (by norm_num) hx
  refine ⟨√x, ⟨?_, ?_⟩, fun t ht => ?_⟩
  · rw [lt_sqrt (by positivity), inv_sqrt_two_sq]
    exact hx
  · rw [sq_sqrt hx0.le, log_sqrt hx0.le]
    exact hfx
  · rw [← hu (t ^ 2) (half_lt_sq_and_sub_log_div_two_eq ht.1 ht.2),
      sqrt_sq (lt_trans (by positivity) ht.1).le]

/-- A fixed positive lower bound `a` eventually selects the root `t > 2^{-1/2}`: a root `t` of
`t² - log t = y` with `a ≤ t ≤ 2^{-1/2}` has `y ≤ ½ - log a`. -/
private lemma eventually_inv_sqrt_two_lt_root {a : ℝ} (ha : 0 < a) {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, a ≤ t y ∧ t y ^ 2 - log (t y) = y) :
    ∀ᶠ y in atTop, (√2)⁻¹ < t y ∧ t y ^ 2 - log (t y) = y := by
  filter_upwards [ht, eventually_gt_atTop (1 / 2 - log a)] with y ⟨hat, hy⟩ hya
  refine ⟨lt_of_not_ge fun hle ↦ ?_, hy⟩
  have hsq : t y ^ 2 ≤ 1 / 2 := by
    rw [← inv_sqrt_two_sq]
    exact pow_le_pow_left₀ (ha.trans_le hat).le hle 2
  have hlog : log a ≤ log (t y) := log_le_log ha hat
  linarith

/-- DLMF 2.2.4: if `a > 0` and `t y` is eventually a root `t ≥ a` of `t² - log t = y`, then
`t(y) ∼ y^{1/2}` as `y → ∞`. -/
theorem sq_sub_log_root_isEquivalent {a : ℝ} (ha : 0 < a) {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, a ≤ t y ∧ t y ^ 2 - log (t y) = y) :
    t ~[atTop] fun y => √y := by
  have ht' := eventually_inv_sqrt_two_lt_root ha ht
  have hs : (fun y => t y ^ 2) ~[atTop] id := by
    refine (strictMonoOn_sub_log_div_two.monotoneOn).root_isEquivalent
      sub_log_div_two_isEquivalent ?_
    filter_upwards [ht'] with y hy
    obtain ⟨h1, h2⟩ := half_lt_sq_and_sub_log_div_two_eq hy.1 hy.2
    exact ⟨h1.le, h2⟩
  refine (hs.symm.rpow (fun y => sq_nonneg (t y)) (r := 1 / 2)).symm.congr_left ?_ |>.congr_right
    (Eventually.of_forall fun y => (sqrt_eq_rpow y).symm)
  filter_upwards [ht] with y hy
  rw [Pi.pow_apply, ← sqrt_eq_rpow, sqrt_sq (ha.trans_le hy.1).le]

/-- DLMF 2.2.5: if `a > 0` and `t y` is eventually a root `t ≥ a` of `t² - log t = y`, then
`t² = y + log t = y + ½ log y + o(1)` as `y → ∞`: the remainder `t² - (y + ½ log y)` is `o(1)`. -/
theorem isLittleO_sq_sub_log_root_sq_remainder {a : ℝ} (ha : 0 < a) {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, a ≤ t y ∧ t y ^ 2 - log (t y) = y) :
    (fun y => t y ^ 2 - (y + log y / 2)) =o[atTop] fun _ => (1 : ℝ) := by
  have hratio := (isEquivalent_iff_tendsto_one (tendsto_sqrt_atTop.eventually_ne_atTop 0)).mp
    (sq_sub_log_root_isEquivalent ha ht)
  have hlog := hratio.log one_ne_zero
  rw [log_one] at hlog
  refine (isLittleO_one_iff ℝ).mpr (hlog.congr' ?_)
  filter_upwards [ht, eventually_gt_atTop 0] with y hy hy0
  rw [Pi.div_apply, log_div (ha.trans_le hy.1).ne' (sqrt_pos.mpr hy0).ne', log_sqrt hy0.le]
  linarith [hy.2]

/-- DLMF 2.2.6: if `a > 0` and `t y` is eventually a root `t ≥ a` of `t² - log t = y`, then
`t = y^{1/2} (1 + ¼ y⁻¹ log y + o(y⁻¹))` as `y → ∞`: the remainder
`t - y^{1/2} (1 + ¼ y⁻¹ log y)` is `o(y^{1/2} y⁻¹)`. -/
theorem isLittleO_sq_sub_log_root_remainder {a : ℝ} (ha : 0 < a) {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, a ≤ t y ∧ t y ^ 2 - log (t y) = y) :
    (fun y => t y - √y * (1 + y⁻¹ * log y / 4)) =o[atTop] fun y => √y * y⁻¹ := by
  have htt : Tendsto t atTop atTop :=
    (sq_sub_log_root_isEquivalent ha ht).symm.tendsto_atTop tendsto_sqrt_atTop
  -- `log t = o(t)` and `t ≤ t + √y`, so `log t / (t + √y) → 0`
  have hq : Tendsto (fun y => log (t y) / (t y + √y)) atTop (𝓝 0) := by
    refine ((isLittleO_log_id_atTop.comp_tendsto htt).trans_isBigO
      (IsBigO.of_bound' ?_)).tendsto_div_nhds_zero
    filter_upwards [ht] with y hy
    have ht0 : 0 < t y := ha.trans_le hy.1
    rw [Function.comp_apply, id, norm_of_nonneg ht0.le, norm_of_nonneg (by positivity)]
    exact le_add_of_nonneg_right (sqrt_nonneg y)
  -- `t² - y = (t - √y) (t + √y) = log t`, so `t - √y = log t / (t + √y) → 0`
  have hd : Tendsto (fun y => t y - √y) atTop (𝓝 0) := by
    refine hq.congr' ?_
    filter_upwards [ht, eventually_ge_atTop 0] with y hy hy0
    have hpos : 0 < t y + √y := add_pos_of_pos_of_nonneg (ha.trans_le hy.1) (sqrt_nonneg y)
    rw [div_eq_iff hpos.ne']
    linear_combination -hy.2 + sq_sqrt hy0
  have he := (isLittleO_one_iff ℝ).mp (isLittleO_sq_sub_log_root_sq_remainder ha ht)
  have hlim := (he.sub (hd.pow 2)).div_const 2
  rw [zero_pow two_ne_zero, sub_zero, zero_div] at hlim
  refine (isLittleO_iff_tendsto' ?_).mpr (hlim.congr' ?_)
  · filter_upwards [eventually_gt_atTop 0] with y hy hz
    exact absurd hz (mul_ne_zero (sqrt_pos.mpr hy).ne' (inv_ne_zero hy.ne'))
  -- the normalized remainder is `((t² - y - ½ log y) - (t - √y)²) / 2`
  filter_upwards [eventually_gt_atTop 0] with y hy
  obtain ⟨s, hs0, rfl⟩ : ∃ s, 0 < s ∧ y = s ^ 2 := ⟨√y, sqrt_pos.mpr hy, (sq_sqrt hy.le).symm⟩
  rw [sqrt_sq hs0.le]
  field_simp
  ring

end TauCeti.Examples.TranscendentalEquation
