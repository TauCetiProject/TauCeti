/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Normed.Group.FunctionSeries
import TauCeti.Analysis.PSeries.Shifted

/-!
# Symmetric sums of shifted reciprocal powers

After removing the term at the nearest pole, the paired sum of reciprocal powers at shifts
`±t` is bounded by `2 re (ζ(k)) - 1` for `|t| ≤ 1` and `k > 1`. The bound is attained at
zero and by the limiting remainder at either endpoint. The cubic case bounds the error sum
in the approximation of ζ by a partial sum at a half-integer.

The estimates use `Real.norm_one_div_add_pow_add_one_div_add_sub_pow_le` and Mathlib's
`zeta_nat_eq_tsum_of_gt_one` and `continuousOn_tsum`.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

/-- The sum of the two reciprocal-power series starting at one and two is
`2 re (ζ(k)) - 1` for `k > 1`. -/
theorem hasSum_one_div_natCast_add_one_pow_add_one_div_natCast_add_two_pow
    {k : ℕ} (hk : 1 < k) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ k + 1 / ((n : ℝ) + 2) ^ k)
      (2 * (riemannZeta k).re - 1) := by
  have hs : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ k) :=
    by simpa only [one_div] using Real.summable_nat_pow_inv.mpr hk
  have hr : (∑' n : ℕ, 1 / (n : ℝ) ^ k) = (riemannZeta k).re := by
    have h := Complex.ofReal_tsum (L := SummationFilter.unconditional ℕ)
      (fun n : ℕ ↦ 1 / (n : ℝ) ^ k)
    simp only [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast, Complex.ofReal_one,
      ← zeta_nat_eq_tsum_of_gt_one hk] at h
    exact Complex.ofReal_re _ ▸ congrArg Complex.re h
  have hs₁ : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ k) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hs
  have hs₂ : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 2) ^ k) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using (summable_nat_add_iff 2).mpr hs
  have h₁ := hs.tsum_eq_zero_add
  have h₂ := hs₁.tsum_eq_zero_add
  convert (hs₁.add hs₂).hasSum using 1
  rw [hs₁.tsum_add hs₂]
  have hk₀ : k ≠ 0 := by omega
  simp only [Nat.cast_zero, Nat.cast_add, Nat.cast_one, zero_pow hk₀, div_zero, zero_add,
    one_pow, div_one, add_assoc, one_add_one_eq_two] at h₁ h₂
  linarith only [hr, h₁, h₂]

/-- The paired reciprocal-power series converges for every shift when `k > 1`. Its sum
splits into the term at `1 - |t|` and the paired tail with successive starting indices. -/
theorem hasSum_one_div_sub_pow_add_one_div_add_pow {k : ℕ} (hk : 1 < k) (t : ℝ) :
    HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 - t) ^ k + 1 / ((n : ℝ) + 1 + t) ^ k)
      (1 / (1 - |t|) ^ k +
        ∑' n : ℕ, (1 / ((n : ℝ) + 1 + |t|) ^ k + 1 / ((n : ℝ) + 2 - |t|) ^ k)) := by
  have heven (n : ℕ) :
      1 / ((n : ℝ) + 1 - t) ^ k + 1 / ((n : ℝ) + 1 + t) ^ k =
        1 / ((n : ℝ) + 1 - |t|) ^ k + 1 / ((n : ℝ) + 1 + |t|) ^ k := by
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h]
    · simp only [abs_of_neg h, sub_eq_add_neg, neg_neg]
      exact add_comm _ _
  have hminus : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 - |t|) ^ k) := by
    simpa only [add_sub_assoc] using (Real.summable_one_div_nat_add_pow_iff (1 - |t|)).mpr hk
  have hplus : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1 + |t|) ^ k) := by
    simpa only [add_assoc] using (Real.summable_one_div_nat_add_pow_iff (1 + |t|)).mpr hk
  convert ((hminus.add hplus).hasSum.congr_fun fun n ↦ heven n) using 1
  symm
  rw [hminus.tsum_add hplus, hminus.tsum_eq_zero_add, add_assoc]
  simp only [Nat.cast_zero, zero_add]
  congr 1
  have hshift : Summable (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1 - |t|) ^ k) :=
    hminus.comp_injective Nat.succ_injective
  rw [← hshift.tsum_add hplus]
  refine tsum_congr fun n ↦ ?_
  simp only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
  exact add_comm _ _

/-- The paired reciprocal-power sum is at most its nearest-pole term plus
`2 re (ζ(k)) - 1` for `k > 1` and `|t| ≤ 1`. At `t = 0` the bound is attained.
At `|t| = 1` the zero denominator contributes zero by Lean's division convention. -/
theorem tsum_one_div_sub_pow_add_one_div_add_pow_le {k : ℕ} (hk : 1 < k) {t : ℝ} (ht : |t| ≤ 1) :
    (∑' n : ℕ, (1 / ((n : ℝ) + 1 - t) ^ k + 1 / ((n : ℝ) + 1 + t) ^ k)) ≤
      1 / (1 - |t|) ^ k + (2 * (riemannZeta k).re - 1) := by
  rw [(hasSum_one_div_sub_pow_add_one_div_add_pow hk t).tsum_eq]
  apply (add_le_add_iff_left _).2
  have hsum := hasSum_one_div_natCast_add_one_pow_add_one_div_natCast_add_two_pow hk
  have hnorm (n : ℕ) :
      ‖1 / ((n : ℝ) + 1 + |t|) ^ k + 1 / ((n : ℝ) + 2 - |t|) ^ k‖ ≤
        1 / ((n : ℝ) + 1) ^ k + 1 / ((n : ℝ) + 2) ^ k := by
    simpa only [add_assoc, one_add_one_eq_two] using
      Real.norm_one_div_add_pow_add_one_div_add_sub_pow_le (a := (n : ℝ) + 1) (by positivity)
        ⟨abs_nonneg t, ht⟩ k
  rw [← hsum.tsum_eq]
  exact (Summable.of_norm_bounded hsum.summable hnorm).tsum_le_tsum
    (fun n ↦ (Real.le_norm_self _).trans (hnorm n)) hsum.summable

-- The comparison is exact at zero shift.
example {k : ℕ} (hk : 1 < k) :
    (∑' n : ℕ, (1 / ((n : ℝ) + 1 - 0) ^ k + 1 / ((n : ℝ) + 1 + 0) ^ k)) =
      2 * (riemannZeta k).re := by
  rw [(hasSum_one_div_sub_pow_add_one_div_add_pow hk 0).tsum_eq]
  simp only [abs_zero, sub_zero, add_zero, one_pow, div_one]
  rw [(hasSum_one_div_natCast_add_one_pow_add_one_div_natCast_add_two_pow hk).tsum_eq]
  ring

/-- The remainder after removing the nearest-pole term tends to `2 re (ζ(k)) - 1`
as `t` approaches either endpoint of `[-1, 1]` from within the interval, for `k > 1`. -/
theorem tendsto_tsum_one_div_sub_pow_add_one_div_add_pow_sub {k : ℕ} (hk : 1 < k) {x : ℝ}
    (hx : |x| = 1) :
    Tendsto (fun t : ℝ ↦
      (∑' n : ℕ, (1 / ((n : ℝ) + 1 - t) ^ k + 1 / ((n : ℝ) + 1 + t) ^ k)) -
        1 / (1 - |t|) ^ k) (𝓝[Icc (-1) 1] x) (𝓝 (2 * (riemannZeta k).re - 1)) := by
  have hsum := hasSum_one_div_natCast_add_one_pow_add_one_div_natCast_add_two_pow hk
  have hcont : ContinuousOn
      (fun t : ℝ ↦ ∑' n : ℕ, (1 / ((n : ℝ) + 1 + |t|) ^ k + 1 / ((n : ℝ) + 2 - |t|) ^ k))
      (Icc (-1) 1) := by
    refine continuousOn_tsum (fun n ↦ ?_) hsum.summable (fun n t ht ↦ ?_)
    · have hd₂ (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : ((n : ℝ) + 2 - |t|) ^ k ≠ 0 := by
        have ht₁ : |t| ≤ 1 := abs_le.mpr ht
        exact pow_ne_zero _ (ne_of_gt (by linarith [Nat.cast_nonneg (α := ℝ) n]))
      exact (continuousOn_const.div (by fun_prop) (fun _ _ ↦ by positivity)).add
        (continuousOn_const.div (by fun_prop) hd₂)
    · simpa only [add_assoc, one_add_one_eq_two] using
        Real.norm_one_div_add_pow_add_one_div_add_sub_pow_le (a := (n : ℝ) + 1) (by positivity)
          ⟨abs_nonneg t, abs_le.mpr ht⟩ k
  have hv : (∑' n : ℕ, (1 / ((n : ℝ) + 1 + |x|) ^ k + 1 / ((n : ℝ) + 2 - |x|) ^ k)) =
      2 * (riemannZeta k).re - 1 := by
    rw [← hsum.tsum_eq]
    refine tsum_congr fun n ↦ ?_
    have hsub : (n : ℝ) + 2 - 1 = n + 1 := by ring
    simp only [hx, add_assoc, one_add_one_eq_two, hsub]
    exact add_comm _ _
  rw [← hv]
  refine (hcont x (abs_le.mp hx.le)).tendsto.congr' (Eventually.of_forall fun t ↦ ?_)
  simp only [(hasSum_one_div_sub_pow_add_one_div_add_pow hk t).tsum_eq, add_sub_cancel_left]

end TauCeti
