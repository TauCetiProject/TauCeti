/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Asymptotics.TranscendentalEquation
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Successive resubstitution for `t² - log t = y` (DLMF 2.2.3–2.2.6)

DLMF's example of the method of successive resubstitution. For `y > ½ (1 + log 2)` the equation
`t² - log t = y` has a unique root `t > 2^{-1/2}` (DLMF 2.2.3). In the variable `x = t²` it reads
`x - ½ log x = y`, and `x ↦ x - ½ log x` is continuous and strictly increasing on `[½, ∞)` and
asymptotic to the identity, so the inversion theorem of DLMF 2.2.1–2.2.2
(`ContinuousOn.existsUnique_root_of_isEquivalent`, `MonotoneOn.root_isEquivalent`) applies.
Substituting the leading approximation back into the equation twice gives the two first
corrections. The asymptotic results hold for any function `t` that is eventually such a root.

## Main results

* `Asymptotics.existsUnique_sq_sub_log_eq`: existence and uniqueness of the root (DLMF 2.2.3).
* `Asymptotics.sq_sub_log_root_isEquivalent`: `t ∼ y^{1/2}` as `y → ∞` (DLMF 2.2.4).
* `Asymptotics.isLittleO_sq_sub_log_root_sq`: `t² = y + ½ log y + o(1)` (DLMF 2.2.5).
* `Asymptotics.isLittleO_sq_sub_log_root`: `t = y^{1/2} (1 + ¼ y⁻¹ log y + o(y⁻¹))`
  (DLMF 2.2.6).

## References

* [DLMF] *NIST Digital Library of Mathematical Functions*, §2.2, <https://dlmf.nist.gov/2.2>.

The proofs are adapted from the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>),
file `DLMF/AsymptoticApproximations/Basics/Transcendental.lean`.
-/

public section

open Filter Real Set
open scoped Topology

namespace Asymptotics

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
private lemma sub_log_div_two_isEquivalent : (fun x : ℝ => x - log x / 2) ~[atTop] id := by
  refine IsLittleO.isEquivalent
    ((isLittleO_log_id_atTop.const_mul_left (1 / 2)).neg_left.congr_left fun x => ?_)
  simp only [Pi.sub_apply, id]
  ring

/-- A root `t > 2^{-1/2}` of `t² - log t = y` gives the root `x = t² > ½` of `x - ½ log x = y`. -/
private lemma sq_sub_log_div_two_eq {t y : ℝ} (ht : (√2)⁻¹ < t) (hty : t ^ 2 - log t = y) :
    1 / 2 < t ^ 2 ∧ t ^ 2 - log (t ^ 2) / 2 = y := by
  refine ⟨?_, ?_⟩
  · have h := pow_lt_pow_left₀ ht (by positivity) two_ne_zero
    rwa [inv_pow, sq_sqrt (by norm_num), ← one_div] at h
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
  · rw [← sqrt_inv, ← one_div]
    exact sqrt_lt_sqrt (by norm_num) hx
  · rw [sq_sqrt hx0.le, log_sqrt hx0.le]
    exact hfx
  · rw [← hu (t ^ 2) (sq_sub_log_div_two_eq ht.1 ht.2),
      sqrt_sq (lt_trans (by positivity) ht.1).le]

/-- DLMF 2.2.4: a function `t` such that `t y` is eventually a root `t > 2^{-1/2}` of
`t² - log t = y` satisfies `t(y) ∼ y^{1/2}` as `y → ∞`. -/
theorem sq_sub_log_root_isEquivalent {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (√2)⁻¹ < t y ∧ t y ^ 2 - log (t y) = y) :
    t ~[atTop] fun y => √y := by
  have hs : (fun y => t y ^ 2) ~[atTop] id := by
    refine (strictMonoOn_sub_log_div_two.monotoneOn).root_isEquivalent
      sub_log_div_two_isEquivalent ?_
    filter_upwards [ht] with y hy
    obtain ⟨h1, h2⟩ := sq_sub_log_div_two_eq hy.1 hy.2
    exact ⟨h1.le, h2⟩
  have hsq : (fun y => t y ^ 2) ~[atTop] fun y => max y 0 :=
    hs.congr_right (by filter_upwards [eventually_ge_atTop 0] with y hy using (max_eq_left hy).symm)
  refine (hsq.rpow (fun y => le_max_right y 0) (r := 1 / 2)).congr_left ?_ |>.congr_right ?_
  · filter_upwards [ht] with y hy
    simp only [Pi.pow_apply]
    rw [← sqrt_eq_rpow, sqrt_sq (lt_trans (by positivity) hy.1).le]
  · filter_upwards [eventually_ge_atTop 0] with y hy
    simp only [Pi.pow_apply]
    rw [max_eq_left hy, ← sqrt_eq_rpow]

/-- DLMF 2.2.5: a function `t` such that `t y` is eventually a root `t > 2^{-1/2}` of
`t² - log t = y` satisfies `t² = y + log t = y + ½ log y + o(1)` as `y → ∞`. -/
theorem isLittleO_sq_sub_log_root_sq {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (√2)⁻¹ < t y ∧ t y ^ 2 - log (t y) = y) :
    (fun y => t y ^ 2 - (y + log y / 2)) =o[atTop] fun _ => (1 : ℝ) := by
  have hz : ∀ᶠ y : ℝ in atTop, √y ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with y hy using (sqrt_pos.mpr hy).ne'
  have hratio := (isEquivalent_iff_tendsto_one hz).mp (sq_sub_log_root_isEquivalent ht)
  have hlog := (continuousAt_log one_ne_zero).tendsto.comp hratio
  rw [log_one] at hlog
  refine (isLittleO_one_iff ℝ).mpr (hlog.congr' ?_)
  filter_upwards [ht, eventually_gt_atTop 0] with y hy hy0
  rw [Function.comp_apply, Pi.div_apply,
    log_div (lt_trans (by positivity) hy.1).ne' (sqrt_pos.mpr hy0).ne', log_sqrt hy0.le]
  linarith [hy.2]

/-- DLMF 2.2.6: a function `t` such that `t y` is eventually a root `t > 2^{-1/2}` of
`t² - log t = y` satisfies `t = y^{1/2} (1 + ¼ y⁻¹ log y + o(y⁻¹))` as `y → ∞`. -/
theorem isLittleO_sq_sub_log_root {t : ℝ → ℝ}
    (ht : ∀ᶠ y in atTop, (√2)⁻¹ < t y ∧ t y ^ 2 - log (t y) = y) :
    (fun y => t y - √y * (1 + y⁻¹ * log y / 4)) =o[atTop] fun y => √y * y⁻¹ := by
  have hlead := sq_sub_log_root_isEquivalent ht
  have htt : Tendsto t atTop atTop := hlead.symm.tendsto_atTop tendsto_sqrt_atTop
  have htn : ∀ᶠ y in atTop, t y ≠ 0 := by
    filter_upwards [ht] with y hy using (lt_trans (by positivity) hy.1).ne'
  have hr := (isEquivalent_iff_tendsto_one htn).mp hlead.symm
  have hl := isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp htt
  have hq : Tendsto (fun y => log (t y) / (t y + √y)) atTop (𝓝 0) := by
    have hh := hl.div (tendsto_const_nhds.add hr) (by norm_num : (1 : ℝ) + 1 ≠ 0)
    rw [zero_div] at hh
    refine hh.congr' ?_
    filter_upwards [ht] with y hy
    have ht0 : 0 < t y := lt_trans (by positivity) hy.1
    simp only [Function.comp_apply, Pi.div_apply, id]
    field_simp
  have he := (isLittleO_one_iff ℝ).mp (isLittleO_sq_sub_log_root_sq ht)
  have hscaled := (he.div_const 2).sub ((hq.pow 2).div_const 2)
  simp only [zero_div, zero_pow two_ne_zero, sub_zero] at hscaled
  refine (isLittleO_iff_tendsto' ?_).mpr (hscaled.congr' ?_)
  · filter_upwards [eventually_gt_atTop 0] with y hy hz
    exact absurd hz (mul_ne_zero (sqrt_pos.mpr hy).ne' (inv_ne_zero hy.ne'))
  filter_upwards [ht, eventually_gt_atTop 0] with y hy hy0
  have ht0 : 0 < t y := lt_trans (by positivity) hy.1
  have hs : √y ^ 2 = y := sq_sqrt hy0.le
  have heq : log (t y) = (t y - √y) * (t y + √y) := by nlinarith [hy.2]
  rw [heq, mul_div_cancel_right₀ _ (by positivity : t y + √y ≠ 0)]
  field_simp
  nlinarith [hy.2]

end Asymptotics
