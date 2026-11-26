/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import TauCeti.Topology.MetricSpace.ModulusOfContinuity

import Mathlib.Topology.Algebra.InfiniteSum.Real
import TauCeti.Topology.Instances.NNReal.Dyadic.Grid

/-!
# Dyadic chaining bound for the uniform modulus of continuity on `[0, 1]`

For a continuous map `f : ℝ≥0 → Y` on `[0, 1]` (`Set.Iic 1`) into a pseudometric space, any bound
`C ≥ 0` on level-`n` dyadic increments of length strictly below `h + 2⁻ⁿ` together with a summable
sequence `M` bounding single-step dyadic increments at all finer levels `r ≥ n + 1` controls the
uniform modulus `TauCeti.modulusOfContinuityOn f (Set.Iic 1) h` by `C + 2 * ∑' k, M (n + 1 + k)`.

This deterministic reduction turns uniform modulus upper bounds over continuum pairs in `[0, 1]`
into finitely many coarse dyadic increments plus summable single-step dyadic tails, as used in
Borel–Cantelli upper bounds for stochastic processes such as Lévy's uniform modulus of continuity
for Brownian motion.

## Main results

* `ContinuousOn.modulusOfContinuityOn_Iic_one_le_of_dyadic`: bounds
  `TauCeti.modulusOfContinuityOn f (Set.Iic 1) h` by `C + 2 * ∑' k, M (n + 1 + k)` from coarse
  level-`n` dyadic increments and summable finer single-step dyadic increments.
-/

public section

open Filter Set
open scoped NNReal Topology

namespace TauCeti

private lemma dist_approxDyadicNNRat_succ_le {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ≥0 → Y} {x : ℝ≥0} (hx : x ≤ 1) (r : ℕ) {B : ℝ}
    (hB0 : 0 ≤ B)
    (hstep : ∀ i < 2 ^ (r + 1),
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ (r + 1))) (f ((i : ℝ≥0) / 2 ^ (r + 1))) ≤ B) :
    dist (f (approxDyadicNNRat r x : ℝ≥0)) (f (approxDyadicNNRat (r + 1) x : ℝ≥0)) ≤ B := by
  set k := ⌊(x : ℝ) * 2 ^ r⌋₊ with hk_def
  set m := ⌊(x : ℝ) * 2 ^ (r + 1)⌋₊ with hm_def
  have hm_le_pow : m ≤ 2 ^ (r + 1) := by
    have h1 : (dyadicNNRat (r + 1) m : ℝ≥0) ≤ (1 : ℕ) := by
      simpa [approxDyadicNNRat_def, ← hm_def] using (coe_approxDyadicNNRat_le (r + 1) x).trans hx
    simpa using coe_dyadicNNRat_le_natCast_iff.1 h1
  have h2k_le : 2 * k ≤ m := by
    refine Nat.le_floor ?_
    calc ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by push_cast; ring
      _ ≤ 2 * ((x : ℝ) * (2 : ℝ) ^ r) := by gcongr; exact Nat.floor_le (by positivity)
      _ = (x : ℝ) * (2 : ℝ) ^ (r + 1) := by rw [pow_succ]; ring
  have hm_lt : m < 2 * k + 2 := by
    rw [← @Nat.cast_lt ℝ]
    calc (m : ℝ) ≤ (x : ℝ) * (2 : ℝ) ^ (r + 1) := Nat.floor_le (by positivity)
      _ = 2 * ((x : ℝ) * (2 : ℝ) ^ r) := by rw [pow_succ]; ring
      _ < 2 * ((k : ℝ) + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = ((2 * k + 2 : ℕ) : ℝ) := by push_cast; ring
  have h2k_eq : (approxDyadicNNRat r x : ℝ≥0) = ((2 * k : ℕ) : ℝ≥0) / 2 ^ (r + 1) := by
    rw [approxDyadicNNRat_def, ← hk_def, ← dyadicNNRat_double, coe_dyadicNNRat]
  rcases eq_or_lt_of_le h2k_le with h_eq | h_lt
  · have hsame : approxDyadicNNRat (r + 1) x = approxDyadicNNRat r x := by
      rw [approxDyadicNNRat_def, approxDyadicNNRat_def, ← hk_def, ← hm_def, ← h_eq,
        dyadicNNRat_double]
    rw [hsame, dist_self]
    exact hB0
  · have hm_eq : m = 2 * k + 1 := by omega
    have hi_lt : 2 * k < 2 ^ (r + 1) := by omega
    have hm_approx :
        (approxDyadicNNRat (r + 1) x : ℝ≥0) = ((2 * k + 1 : ℕ) : ℝ≥0) / 2 ^ (r + 1) := by
      rw [approxDyadicNNRat_def, ← hm_def, hm_eq, coe_dyadicNNRat]
    rw [h2k_eq, hm_approx, dist_comm]
    exact hstep (2 * k) hi_lt

private lemma dist_approxDyadicNNRat_le_tsum {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ≥0 → Y} (hf : ContinuousOn f (Iic 1))
    {x : ℝ≥0} (hx : x ≤ 1) (n : ℕ) {M : ℕ → ℝ} (hM_sum : Summable M)
    (hM : ∀ r ≥ n + 1, ∀ i < 2 ^ r,
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r)) (f ((i : ℝ≥0) / 2 ^ r)) ≤ M r) :
    dist (f (approxDyadicNNRat n x : ℝ≥0)) (f x) ≤ ∑' k : ℕ, M (n + 1 + k) := by
  have hM_nonneg (k : ℕ) : 0 ≤ M (n + 1 + k) :=
    dist_nonneg.trans (hM (n + 1 + k) (by omega) 0 (Nat.two_pow_pos _))
  have hshift_sum : Summable (fun k : ℕ ↦ M (n + 1 + k)) :=
    hM_sum.comp_injective (add_right_injective (n + 1))
  have hstep (k : ℕ) :
      dist (f (approxDyadicNNRat (k + n) x : ℝ≥0))
        (f (approxDyadicNNRat (k.succ + n) x : ℝ≥0)) ≤ M (n + 1 + k) := by
    have hidx : n + 1 + k = k + n + 1 := by omega
    rw [Nat.succ_add, hidx]
    exact dist_approxDyadicNNRat_succ_le hx (k + n) (hidx ▸ hM_nonneg k)
      (hM (k + n + 1) (by omega))
  have h_app : Tendsto (fun k : ℕ ↦ (approxDyadicNNRat (k + n) x : ℝ≥0)) atTop (𝓝 x) :=
    (tendsto_approxDyadicNNRat x).comp (tendsto_add_atTop_nat n)
  have h_nhds : Tendsto (fun k : ℕ ↦ (approxDyadicNNRat (k + n) x : ℝ≥0)) atTop (𝓝[Iic 1] x) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_app
      (Eventually.of_forall fun k ↦ (coe_approxDyadicNNRat_le (k + n) x).trans hx)
  simpa only [Nat.zero_add] using dist_le_tsum_of_dist_le_of_tendsto₀
    (f := fun k ↦ f (approxDyadicNNRat (k + n) x : ℝ≥0)) (fun k ↦ M (n + 1 + k))
    hstep hshift_sum ((hf x hx).tendsto.comp h_nhds)

private lemma dist_le_of_dyadic {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ≥0 → Y} (hf : ContinuousOn f (Iic 1)) (n : ℕ)
    {h C : ℝ} (hC0 : 0 ≤ C)
    (hcoarse : ∀ i j : ℕ, i < j → j ≤ 2 ^ n →
      ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ n < h + 1 / (2 : ℝ) ^ n →
      dist (f ((j : ℝ≥0) / 2 ^ n)) (f ((i : ℝ≥0) / 2 ^ n)) ≤ C)
    {M : ℕ → ℝ} (hM_sum : Summable M)
    (hM : ∀ r ≥ n + 1, ∀ i < 2 ^ r,
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r)) (f ((i : ℝ≥0) / 2 ^ r)) ≤ M r)
    {s t : ℝ≥0} (hst : s ≤ t) (ht1 : t ≤ 1) (hdiff : (t : ℝ) - s ≤ h) :
    dist (f s) (f t) ≤ C + 2 * ∑' k : ℕ, M (n + 1 + k) := by
  have hs1 : s ≤ 1 := hst.trans ht1
  -- Approximate `s` and `t` from below on the level-`n` dyadic grid.
  set i := ⌊(s : ℝ) * 2 ^ n⌋₊ with hi_def
  set j := ⌊(t : ℝ) * 2 ^ n⌋₊ with hj_def
  have hij : i ≤ j := Nat.floor_mono (by gcongr)
  have hj_le : j ≤ 2 ^ n := by
    have h1 : (dyadicNNRat n j : ℝ≥0) ≤ (1 : ℕ) := by
      simpa [approxDyadicNNRat_def, ← hj_def] using (coe_approxDyadicNNRat_le n t).trans ht1
    simpa using coe_dyadicNNRat_le_natCast_iff.1 h1
  -- Bound the coarse level-`n` jump between `approxDyadicNNRat n s` and `approxDyadicNNRat n t`.
  have hmid : dist (f (approxDyadicNNRat n s : ℝ≥0)) (f (approxDyadicNNRat n t : ℝ≥0)) ≤ C := by
    rcases eq_or_lt_of_le hij with h_eq | h_lt
    · rw [approxDyadicNNRat_def, approxDyadicNNRat_def, ← hi_def, ← hj_def, h_eq, dist_self]
      exact hC0
    · have hlen : ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ n < h + 1 / (2 : ℝ) ^ n := by
        have h2 : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
        have hrhs : h + 1 / (2 : ℝ) ^ n = (h * (2 : ℝ) ^ n + 1) / (2 : ℝ) ^ n := by
          field_simp
        rw [Nat.cast_sub hij, hrhs, div_lt_div_iff_of_pos_right h2]
        have hj_r : (j : ℝ) ≤ (t : ℝ) * (2 : ℝ) ^ n := Nat.floor_le (by positivity)
        have hi_r : (s : ℝ) * (2 : ℝ) ^ n < (i : ℝ) + 1 := Nat.lt_floor_add_one _
        have hts_mul : ((t : ℝ) - s) * (2 : ℝ) ^ n ≤ h * (2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_right hdiff h2.le
        linarith
      rw [approxDyadicNNRat_def, approxDyadicNNRat_def, ← hi_def, ← hj_def, coe_dyadicNNRat,
        coe_dyadicNNRat, dist_comm]
      exact hcoarse i j h_lt hj_le hlen
  -- Combine the coarse jump with the two dyadic refinement tails at `s` and `t`.
  have htail_s := dist_approxDyadicNNRat_le_tsum hf hs1 n hM_sum hM
  have htail_t := dist_approxDyadicNNRat_le_tsum hf ht1 n hM_sum hM
  calc dist (f s) (f t)
      ≤ dist (f s) (f (approxDyadicNNRat n s : ℝ≥0)) +
          dist (f (approxDyadicNNRat n s : ℝ≥0)) (f (approxDyadicNNRat n t : ℝ≥0)) +
          dist (f (approxDyadicNNRat n t : ℝ≥0)) (f t) := dist_triangle4 _ _ _ _
    _ = dist (f (approxDyadicNNRat n s : ℝ≥0)) (f s) +
          dist (f (approxDyadicNNRat n s : ℝ≥0)) (f (approxDyadicNNRat n t : ℝ≥0)) +
          dist (f (approxDyadicNNRat n t : ℝ≥0)) (f t) := by rw [dist_comm (f s)]
    _ ≤ C + 2 * ∑' k : ℕ, M (n + 1 + k) := by linarith

end TauCeti

/-- **Deterministic dyadic chaining bound on `[0, 1]`**: if `f : ℝ≥0 → Y` is continuous on `[0, 1]`,
`C ≥ 0` bounds every level-`n` dyadic increment of length `< h + 2 ^ (-n)`, and a summable sequence
`M` bounds single-step dyadic increments at all finer levels `r ≥ n + 1`, then
`modulusOfContinuityOn f (Set.Iic 1) h ≤ C + 2 * ∑' k, M (n + 1 + k)`. -/
theorem ContinuousOn.modulusOfContinuityOn_Iic_one_le_of_dyadic {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ≥0 → Y} (hf : ContinuousOn f (Iic 1)) (n : ℕ) {h C : ℝ} (hC0 : 0 ≤ C)
    (hcoarse : ∀ i j : ℕ, i < j → j ≤ 2 ^ n →
      ((j - i : ℕ) : ℝ) / (2 : ℝ) ^ n < h + 1 / (2 : ℝ) ^ n →
      dist (f ((j : ℝ≥0) / 2 ^ n)) (f ((i : ℝ≥0) / 2 ^ n)) ≤ C)
    {M : ℕ → ℝ} (hM_sum : Summable M)
    (hM : ∀ r ≥ n + 1, ∀ i < 2 ^ r,
      dist (f (((i + 1 : ℕ) : ℝ≥0) / 2 ^ r)) (f ((i : ℝ≥0) / 2 ^ r)) ≤ M r) :
    TauCeti.modulusOfContinuityOn f (Iic 1) h ≤ C + 2 * ∑' k : ℕ, M (n + 1 + k) := by
  have htsum_nonneg : 0 ≤ ∑' k : ℕ, M (n + 1 + k) :=
    (dist_nonneg (x := f (TauCeti.approxDyadicNNRat n 0 : ℝ≥0)) (y := f 0)).trans
      (TauCeti.dist_approxDyadicNNRat_le_tsum hf zero_le_one n hM_sum hM)
  -- Reduce to ordered pairs `x ≤ y` in `[0, 1]` and apply `TauCeti.dist_le_of_dyadic`.
  refine TauCeti.modulusOfContinuityOn_le (by positivity) fun x hx y hy hxy ↦ ?_
  rcases le_total x y with hle | hle
  · refine TauCeti.dist_le_of_dyadic hf n hC0 hcoarse hM_sum hM hle hy ?_
    rwa [NNReal.dist_eq, abs_of_nonpos (sub_nonpos.2 (NNReal.coe_le_coe.2 hle)), neg_sub] at hxy
  · rw [dist_comm]
    refine TauCeti.dist_le_of_dyadic hf n hC0 hcoarse hM_sum hM hle hx ?_
    rwa [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (NNReal.coe_le_coe.2 hle))] at hxy
