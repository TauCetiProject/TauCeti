/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalAverage

/-!
# Cosecant sums on a uniform grid

The sum of `1 / sin (π k / q)` over the nonzero frequencies `1 ≤ k < q` is bounded
by `(2q / π) log (4q / π)`. The leading constant `2 / π` is used in explicit
Pólya–Vinogradov bounds for character interval sums.

The midpoint integral comparison is from C. Pomerance, *Remarks on the Pólya–Vinogradov
inequality*, Integers 11 (2011), 531–542, proof of Lemma 4. Here the symmetric integral is
bounded directly by `x < tan x`, so no positive inverse-square correction is needed.
-/

public section

open Set MeasureTheory intervalIntegral
open scoped Interval

namespace Real

/-- Cosecant is convex on `(0, π)`: it is the decreasing convex reciprocal composed with
positive concave sine. -/
theorem convexOn_inv_sin_Ioo : ConvexOn ℝ (Ioo 0 π) (fun x ↦ (sin x)⁻¹) := by
  have hsin := strictConcaveOn_sin_Icc.concaveOn.subset Ioo_subset_Icc_self (convex_Ioo 0 π)
  have hinv : ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ x⁻¹) := by
    simpa only [zpow_neg_one] using (convexOn_zpow (𝕜 := ℝ) (-1))
  refine ⟨hsin.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  have hx' := sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hy' := sin_pos_of_pos_of_lt_pi hy.1 hy.2
  have hpos : 0 < a * sin x + b * sin y := by
    rcases ha.eq_or_lt with rfl | ha'
    · simp_all
    · exact add_pos_of_pos_of_nonneg (mul_pos ha' hx') (mul_nonneg hb hy'.le)
  have hle := hsin.2 hx hy ha hb hab
  exact ((inv_le_inv₀ (hpos.trans_le hle) hpos).2 hle).trans (hinv.2 hx' hy' ha hb hab)

/-- The derivative of `log (tan (x / 2))` is cosecant wherever `sin x` is nonzero. -/
theorem hasDerivAt_log_tan_half {x : ℝ} (hx : sin x ≠ 0) :
    HasDerivAt (fun t ↦ log (tan (t / 2))) (sin x)⁻¹ x := by
  have hs : sin x = 2 * sin (x / 2) * cos (x / 2) := by
    rw [← sin_two_mul, mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
  have hs' : sin (x / 2) ≠ 0 := fun h ↦ hx (by simp [hs, h])
  have hc : cos (x / 2) ≠ 0 := fun h ↦ hx (by simp [hs, h])
  have ht : tan (x / 2) ≠ 0 := by rw [tan_eq_sin_div_cos]; exact div_ne_zero hs' hc
  have h : HasDerivAt (fun t ↦ tan (t / 2)) (1 / cos (x / 2) ^ 2 * (1 / 2)) x := by
    simpa only [Function.comp_def, id_eq, smul_eq_mul, mul_comm] using
      (hasDerivAt_tan hc).scomp x ((hasDerivAt_id x).div_const 2)
  convert h.log ht using 1
  rw [hs, tan_eq_sin_div_cos]
  field_simp

/-- The integral of cosecant on an interval not containing a zero of sine. -/
theorem integral_inv_sin {a b : ℝ} (hne : ∀ x ∈ uIcc a b, sin x ≠ 0) :
    (∫ x in a..b, (sin x)⁻¹) = log (tan (b / 2)) - log (tan (a / 2)) :=
  integral_eq_sub_of_hasDerivAt (fun x hx ↦ hasDerivAt_log_tan_half (hne x hx))
    ((continuous_sin.continuousOn.inv₀ hne).intervalIntegrable)

/-- Cosecant is continuous between its consecutive poles at `0` and `π`. -/
theorem continuousOn_inv_sin_Ioo : ContinuousOn (fun x ↦ (sin x)⁻¹) (Ioo 0 π) :=
  continuous_sin.continuousOn.inv₀ fun _ hx ↦ (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'

private theorem mul_inv_sin_midpoint_le {a b : ℝ} (ha : 0 < a) (hb : b < π) (hab : a ≤ b) :
    (b - a) * (sin ((a + b) / 2))⁻¹ ≤ ∫ x in a..b, (sin x)⁻¹ := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hsub : Icc a b ⊆ Ioo 0 π := fun _ hx ↦ ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
  have hc := continuousOn_inv_sin_Ioo.mono hsub
  have hf : ∀ᵐ x ∂volume.restrict (Ioc a b), x ∈ Icc a b :=
    (ae_restrict_mem measurableSet_Ioc).mono fun _ hx ↦ Ioc_subset_Icc_self hx
  have h := (convexOn_inv_sin_Ioo.subset hsub (convex_Icc _ _)).map_set_average_le
    (f := fun x : ℝ ↦ x) hc isClosed_Icc (by simp [hab.not_ge]) (by simp) hf
    ((continuous_id.intervalIntegrable _ _).1) ((hc.intervalIntegrable_of_Icc hab.le).1)
  have havg : (⨍ x : ℝ in a..b, x) = (a + b) / 2 := by
    rw [interval_average_eq_div, integral_id]
    field_simp
    ring
  have h' : (sin (⨍ x : ℝ in a..b, x))⁻¹ ≤ ⨍ x in a..b, (sin x)⁻¹ := by
    simpa only [uIoc_of_le hab.le, Function.comp_apply] using h
  rw [havg, interval_average_eq_div] at h'
  simpa only [mul_comm (b - a)] using (le_div_iff₀ (sub_pos.mpr hab)).mp h'

private theorem mul_sum_inv_sin_le_integral {q : ℕ} (hq : 0 < q) :
    (π / q) * (∑ k ∈ Finset.Ico 1 q, (sin (π * k / q))⁻¹) ≤
      ∫ x in π / (2 * q)..π - π / (2 * q), (sin x)⁻¹ := by
  let h : ℝ := π / q
  let a (k : ℕ) := h * ((k : ℝ) - 1 / 2)
  have hq₀ : (0 : ℝ) < q := by positivity
  have hh : 0 < h := div_pos pi_pos hq₀
  have hmul : h * q = π := div_mul_cancel₀ _ hq₀.ne'
  have hstep (k : ℕ) : a (k + 1) - a k = h := by simp [a]; ring
  have hmid (k : ℕ) : (a k + a (k + 1)) / 2 = π * k / q := by simp [a, h]; ring
  have hends (k : ℕ) (hk : k ∈ Finset.Ico 1 q) : 0 < a k ∧ a (k + 1) < π := by
    have hk₁ : (1 : ℝ) ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    have hkq : ((k + 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast (Finset.mem_Ico.mp hk).2
    exact ⟨mul_pos hh (by linarith), by rw [← hmul]; exact mul_lt_mul_of_pos_left (by linarith) hh⟩
  have ha₁ : a 1 = π / (2 * q) := by simp [a, h]; ring
  have haq : a q = π - π / (2 * q) := calc
    a q = h * q - a 1 := by simp [a]; ring
    _ = _ := by rw [hmul, ha₁]
  rw [← haq, ← ha₁, Finset.mul_sum,
    ← sum_integral_adjacent_intervals_Ico (a := a) (by omega : 1 ≤ q)]
  · refine Finset.sum_le_sum fun k hk ↦ ?_
    obtain ⟨ha, hb⟩ := hends k hk
    have hab : a k ≤ a (k + 1) := by linarith [hstep k]
    simpa only [hstep k, hmid k] using mul_inv_sin_midpoint_le ha hb hab
  · intro k hk
    obtain ⟨ha, hb⟩ := hends k (Finset.mem_Ico.mpr hk)
    have hab : a k ≤ a (k + 1) := by linarith [hstep k]
    have hsub : Icc (a k) (a (k + 1)) ⊆ Ioo 0 π := fun _ hx ↦
      ⟨ha.trans_le hx.1, hx.2.trans_lt hb⟩
    exact (continuousOn_inv_sin_Ioo.mono hsub).intervalIntegrable_of_Icc hab

/-- The sum of cosecants at the nonzero frequencies of level `q` is strictly less than
`(2q / π) log (4q / π)`. This includes the empty sum at `q = 1`. -/
theorem sum_inv_sin_pi_mul_div_lt {q : ℕ} (hq : 0 < q) :
    ∑ k ∈ Finset.Ico 1 q, (sin (π * k / q))⁻¹ <
      (2 * q / π) * log (4 * q / π) := by
  have hq₀ : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hq₁ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  let t : ℝ := π / (4 * q)
  have ht : 0 < t := by positivity
  have ht' : t < π / 2 := by
    rw [div_lt_div_iff_of_pos_left pi_pos (by positivity) (by norm_num)]
    linarith
  have hleft : π / (2 * q) = 2 * t := by dsimp only [t]; ring
  have hright : (π - π / (2 * q)) / 2 = π / 2 - t := by rw [hleft]; ring
  have hmid : π / (2 * q) < π := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * q)]
    nlinarith only [pi_pos, mul_nonneg pi_pos.le (sub_nonneg.mpr hq₁)]
  have hsub : uIcc (π / (2 * q)) (π - π / (2 * q)) ⊆ Ioo 0 π :=
    (ordConnected_Ioo (a := 0) (b := π)).uIcc_subset
      ⟨by positivity, hmid⟩ ⟨sub_pos.mpr hmid, sub_lt_self _ (by positivity)⟩
  have hI := integral_inv_sin fun x hx ↦ (sin_pos_of_pos_of_lt_pi (hsub hx).1 (hsub hx).2).ne'
  have hval : (∫ x in π / (2 * q)..π - π / (2 * q), (sin x)⁻¹) = 2 * log (tan t)⁻¹ := by
    have ht₂ : (π / (2 * q)) / 2 = t := by rw [hleft]; ring
    simp only [hI, hright, tan_pi_div_two_sub, ht₂, log_inv]
    ring
  have hlog := log_lt_log (inv_pos.mpr (ht.trans (lt_tan ht ht')))
    (inv_strictAnti₀ ht (lt_tan ht ht'))
  have h := mul_sum_inv_sin_le_integral hq
  rw [hval] at h
  have hscaled := h.trans_lt (mul_lt_mul_of_pos_left hlog (by norm_num : (0 : ℝ) < 2))
  rw [mul_comm (π / q), ← lt_div_iff₀ (div_pos pi_pos hq₀)] at hscaled
  have hinv : t⁻¹ = 4 * q / π := by simp [t]
  have hscale : 2 * log (4 * q / π) / (π / q) = 2 * q / π * log (4 * q / π) := by
    rw [div_div_eq_mul_div]
    ring
  rwa [hinv, hscale] at hscaled

end Real
