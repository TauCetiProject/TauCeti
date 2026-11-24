/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.Harmonic.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Asymptotic growth of real-power partial sums

For every real exponent `α`, the partial sums `∑_{j=1}^{n-1} j^α` fall into three exact asymptotic
regimes as `n → ∞`:

* `α < -1`: `∑_{j=1}^{n-1} j^α = Θ(1)` (and `= O(1)` iff `α < -1`), by `p`-series summability above
  and the first summand `1^α = 1` below;
* `α = -1`: `∑_{j=1}^{n-1} j^{-1} = Θ(log n)` (with `∑_{j=1}^{n-1} j^α = O(log n)` iff `α ≤ -1`),
  by the harmonic-number bounds;
* `-1 < α`: `∑_{j=1}^{n-1} j^α = Θ(n^{α+1})` (and `= O(n^{α+1})` iff `-1 < α`), with the explicit
  non-asymptotic upper bound `∑_{j=1}^{n-1} j^α ≤ n^{α+1} / (α + 1)` for all `n : ℕ` proved by
  telescoping tangent-line inequalities on `t ↦ t^{α+1} / (α + 1)`.

Combining the convergent and growing regimes yields the single-scale characterization
`∑_{j=1}^{n-1} j^α = O(n^{α+1} + 1) ↔ α ≠ -1`, which bounds discrete remainder sums without
splitting into `α < -1` and `-1 < α` cases.

For complex exponents, a power sum `∑_{n=1}^{N} n ^ (-s)` whose weights `n ^ (1 - Re s)` are at
most `M ≥ 0` has norm at most `M (1 + log N)`, the bound used for Dirichlet polynomials near the
line `Re s = 1`.

## Main results

* `TauCeti.sum_Ico_rpow_le`: `∑ j ∈ Ico 1 n, (j : ℝ) ^ α ≤ (n : ℝ) ^ (α + 1) / (α + 1)` for
  `-1 < α` and every `n : ℕ`.
* `TauCeti.isBigO_sum_Ico_rpow_one_iff` and `TauCeti.isTheta_sum_Ico_rpow_one_iff`:
  `O(1)` and `Θ(1)` characterizations (`α < -1`).
* `TauCeti.isBigO_sum_Ico_rpow_log_iff` and `TauCeti.isTheta_sum_Ico_rpow_log_iff`:
  `O(log n)` (`α ≤ -1`) and `Θ(log n)` (`α = -1`) characterizations.
* `TauCeti.isBigO_sum_Ico_rpow_rpow_add_one_iff` and
  `TauCeti.isTheta_sum_Ico_rpow_rpow_add_one_iff`: `O(n^{α+1})` and `Θ(n^{α+1})` characterizations
  (`-1 < α`).
* `TauCeti.isBigO_sum_Ico_rpow_rpow_add_one_add_one_iff`:
  `∑ j ∈ Ico 1 n, (j : ℝ) ^ α = O(n^{α+1} + 1)` iff `α ≠ -1`.
* `TauCeti.norm_sum_Icc_cpow_neg_le_mul_one_add_log`: `‖∑_{n=1}^{N} n ^ (-s)‖ ≤ M (1 + log N)`
  when every weight `n ^ (1 - Re s)`, `1 ≤ n ≤ N`, is at most `M ≥ 0`.

## References

* NIST *Digital Library of Mathematical Functions*, §2.10(ii), formulas 2.10.10–2.10.11.
* F. W. J. Olver, *Asymptotics and Special Functions*, Chapter 8, §4.
-/

public section

open Asymptotics Filter Finset Topology

namespace TauCeti

/-- **Explicit upper bound on partial sums of real powers.** For `-1 < α` and every natural number
`n`, `∑ j ∈ Ico 1 n, (j : ℝ) ^ α ≤ (n : ℝ) ^ (α + 1) / (α + 1)`. -/
theorem sum_Ico_rpow_le {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∑ j ∈ Ico 1 n, (j : ℝ) ^ α ≤ (n : ℝ) ^ (α + 1) / (α + 1) := by
  have hα₁ : 0 < α + 1 := by linarith
  rcases eq_or_ne n 0 with rfl | hn₀
  · simp [Real.zero_rpow hα₁.ne']
  have hn₁ : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn₀
  rcases le_total 0 α with hα₀ | hα₀
  · have hstep : ∀ j ∈ Ico 1 n,
        (j : ℝ) ^ α ≤ (((j + 1 : ℕ) : ℝ) ^ (α + 1) - (j : ℝ) ^ (α + 1)) / (α + 1) := by
      intro j _
      have h := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow (p := α + 1)
        (u := (j + 1 : ℕ)) (v := j) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      rw [add_sub_cancel_right, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one] at h
      rw [le_div_iff₀ hα₁, Nat.cast_add, Nat.cast_one]
      linarith
    calc ∑ j ∈ Ico 1 n, (j : ℝ) ^ α
        ≤ ∑ j ∈ Ico 1 n, (((j + 1 : ℕ) : ℝ) ^ (α + 1) - (j : ℝ) ^ (α + 1)) / (α + 1) :=
          sum_le_sum hstep
      _ = ((n : ℝ) ^ (α + 1) - (1 : ℝ) ^ (α + 1)) / (α + 1) := by
          rw [← sum_div, sum_Ico_sub (fun k : ℕ ↦ (k : ℝ) ^ (α + 1)) hn₁, Nat.cast_one]
      _ ≤ (n : ℝ) ^ (α + 1) / (α + 1) := by
          rw [Real.one_rpow]
          exact div_le_div_of_nonneg_right (by linarith) hα₁.le
  · calc ∑ j ∈ Ico 1 n, (j : ℝ) ^ α
        ≤ ∑ j ∈ Ico 1 n, ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) / (α + 1) :=
          sum_le_sum fun j hj ↦ by
            rw [Nat.cast_sub (mem_Ico.mp hj).1, Nat.cast_one]
            exact Real.rpow_le_rpow_sub_sub_one_rpow_div hα hα₀
              (Nat.one_le_cast.mpr (mem_Ico.mp hj).1)
      _ = (((n - 1 : ℕ) : ℝ) ^ (α + 1) - (0 : ℝ) ^ (α + 1)) / (α + 1) := by
          have htel : ∑ j ∈ Ico 1 n, ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) =
              ((n - 1 : ℕ) : ℝ) ^ (α + 1) - (0 : ℝ) ^ (α + 1) := by
            simpa only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero] using
              sum_Ico_sub (fun k : ℕ ↦ ((k - 1 : ℕ) : ℝ) ^ (α + 1)) hn₁
          rw [← sum_div, htel]
      _ ≤ (n : ℝ) ^ (α + 1) / (α + 1) := by
          rw [Real.zero_rpow hα₁.ne', sub_zero]
          exact div_le_div_of_nonneg_right
            (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le n 1) hα₁.le)
            hα₁.le

/-- Lower bound matching `sum_Ico_rpow_le` for `-1 < α`: `(n : ℝ) ^ (α + 1) = O(∑_{j=1}^{n-1} j^α)`
as `n → ∞`. -/
private theorem isBigO_rpow_add_one_sum_Ico_rpow {α : ℝ} (hα : -1 < α) :
    (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) =O[atTop] fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
  have hα₁ : 0 < α + 1 := by linarith
  rcases le_total 0 α with hα₀ | hα₀
  · refine .of_bound ((2 : ℝ) ^ (α + 1) * (α + 1)) ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hstep : ∀ j ∈ Ico 1 n,
        ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) / (α + 1) ≤ (j : ℝ) ^ α := by
      intro j hj
      have h := Real.rpow_add_mul_rpow_sub_one_mul_sub_le_rpow (p := α + 1)
        (u := (j - 1 : ℕ)) (v := j) (by linarith) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      rw [add_sub_cancel_right, Nat.cast_sub (mem_Ico.mp hj).1, Nat.cast_one] at h
      rw [div_le_iff₀ hα₁, Nat.cast_sub (mem_Ico.mp hj).1, Nat.cast_one]
      linarith
    have htel : (((n - 1 : ℕ) : ℝ) ^ (α + 1)) / (α + 1) ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
      have hs := sum_le_sum hstep
      have ht : ∑ j ∈ Ico 1 n, ((j : ℝ) ^ (α + 1) - ((j - 1 : ℕ) : ℝ) ^ (α + 1)) =
          ((n - 1 : ℕ) : ℝ) ^ (α + 1) - (0 : ℝ) ^ (α + 1) := by
        simpa only [Nat.add_sub_cancel, Nat.sub_self, Nat.cast_zero] using
          sum_Ico_sub (fun k : ℕ ↦ ((k - 1 : ℕ) : ℝ) ^ (α + 1)) (by omega : 1 ≤ n)
      rwa [← sum_div, ht, Real.zero_rpow hα₁.ne', sub_zero] at hs
    have hhalf : (n : ℝ) / 2 ≤ ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hpow := Real.rpow_le_rpow (by positivity) hhalf hα₁.le
    rw [Real.div_rpow (Nat.cast_nonneg n) zero_le_two, div_le_iff₀ (by positivity)] at hpow
    rw [div_le_iff₀ hα₁] at htel
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity)]
    calc (n : ℝ) ^ (α + 1) ≤ ((n - 1 : ℕ) : ℝ) ^ (α + 1) * (2 : ℝ) ^ (α + 1) := hpow
      _ ≤ ((∑ j ∈ Ico 1 n, (j : ℝ) ^ α) * (α + 1)) * (2 : ℝ) ^ (α + 1) :=
          mul_le_mul_of_nonneg_right htel (by positivity)
      _ = (2 : ℝ) ^ (α + 1) * (α + 1) * ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by ring
  · refine .of_bound (2 * (α + 1)) ?_
    have htend : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) atTop atTop :=
      (tendsto_rpow_atTop hα₁).comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, htend.eventually_ge_atTop 2] with n hn hn₂
    have htel : ((n : ℝ) ^ (α + 1) - 1) / (α + 1) ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
      have hs := sum_le_sum (s := Ico 1 n) fun j hj ↦ by
        simpa only [← Nat.cast_add_one] using
          Real.add_one_rpow_sub_rpow_div_le_rpow hα₀ (Nat.cast_pos.mpr (mem_Ico.mp hj).1)
      rwa [← sum_div, sum_Ico_sub (fun k : ℕ ↦ (k : ℝ) ^ (α + 1)) hn, Nat.cast_one,
        Real.one_rpow] at hs
    rw [Real.norm_of_nonneg (by positivity),
      Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity)]
    have hmul := mul_le_mul_of_nonneg_left htel (by positivity : 0 ≤ 2 * (α + 1))
    field_simp at hmul
    linarith

/-- For `α = -1`, `∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ) = Θ(log n)` as `n → ∞`. -/
private theorem isTheta_sum_Ico_rpow_neg_one_log :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =Θ[atTop] fun n : ℕ ↦ Real.log n := by
  have heq : ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ) = (harmonic (n - 1) : ℝ) := by
    intro n hn
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, ← Ico_add_one_right_eq_Icc, Nat.sub_add_cancel hn]
    refine sum_congr rfl fun j _ ↦ ?_
    rw [Real.rpow_neg_one, Rat.cast_inv, Rat.cast_natCast]
  refine ⟨.of_bound 2 ?_, .of_bound 1 ?_⟩
  · have hlog : Tendsto (fun n : ℕ ↦ Real.log n) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 2, hlog.eventually_ge_atTop 1] with n _ hln
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), heq n (by omega),
      Real.norm_of_nonneg (by linarith)]
    have h₁ : (harmonic (n - 1) : ℝ) ≤ 1 + Real.log (n - 1 : ℕ) := harmonic_le_one_add_log (n - 1)
    have h₂ : Real.log (n - 1 : ℕ) ≤ Real.log n :=
      Real.log_le_log (Nat.cast_pos.mpr (by omega)) (by exact_mod_cast Nat.sub_le n 1)
    linarith
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlog_nn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    rw [Real.norm_of_nonneg hlog_nn, Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
      heq n hn, one_mul]
    simpa only [Nat.sub_add_cancel hn] using log_add_one_le_harmonic (n - 1)

/-- **Boundedness characterization of real-power partial sums.** `∑_{j=1}^{n-1} j^α = O(1)` as
`n → ∞` if and only if `α < -1`. -/
theorem isBigO_sum_Ico_rpow_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ↔ α < -1 := by
  constructor
  · intro h
    by_contra! hα
    have hmono : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
        fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α := by
      refine .of_bound 1 (Eventually.of_forall fun n ↦ ?_)
      rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
        Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), one_mul]
      exact sum_le_sum fun j hj ↦
        Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr (mem_Ico.mp hj).1) hα
    have hlo := (Real.isLittleO_const_log_atTop (c := (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop).trans_isBigO
      (isTheta_sum_Ico_rpow_neg_one_log.2.trans (hmono.trans h))
    obtain ⟨_, hhalf⟩ := (hlo.def one_half_pos).exists
    dsimp only [Function.comp_apply] at hhalf
    norm_num at hhalf
  · intro hα
    have hsum : Summable (fun j : ℕ ↦ (j : ℝ) ^ α) := Real.summable_nat_rpow.mpr hα
    refine .of_bound (∑' j : ℕ, (j : ℝ) ^ α) (Eventually.of_forall fun n ↦ ?_)
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), norm_one, mul_one]
    exact hsum.sum_le_tsum (Ico 1 n) fun j _ ↦ by positivity

/-- **Exact `Θ(1)` characterization of real-power partial sums.** `∑_{j=1}^{n-1} j^α = Θ(1)` as
`n → ∞` if and only if `α < -1`. -/
theorem isTheta_sum_Ico_rpow_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =Θ[atTop] (fun _ : ℕ ↦ (1 : ℝ)) ↔ α < -1 := by
  refine ⟨fun h ↦ isBigO_sum_Ico_rpow_one_iff.mp h.1,
    fun hα ↦ ⟨isBigO_sum_Ico_rpow_one_iff.mpr hα, ?_⟩⟩
  refine .of_bound 1 ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [norm_one, Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity), one_mul]
  have h1 : ((1 : ℕ) : ℝ) ^ α ≤ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α :=
    single_le_sum (f := fun j : ℕ ↦ (j : ℝ) ^ α) (fun j _ ↦ by positivity)
      (mem_Ico.mpr ⟨le_rfl, hn⟩)
  simpa using h1

/-- **Logarithmic big-O characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = O(log n)` as `n → ∞` if and only if `α ≤ -1`. -/
theorem isBigO_sum_Ico_rpow_log_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun n : ℕ ↦ Real.log n) ↔ α ≤ -1 := by
  constructor
  · intro h
    by_contra! hα
    have hpow := (isBigO_rpow_add_one_sum_Ico_rpow hα).trans h
    have hlo : (fun n : ℕ ↦ Real.log n) =o[atTop] fun n : ℕ ↦ (n : ℝ) ^ (α + 1) :=
      (isLittleO_log_rpow_atTop (by linarith : 0 < α + 1)).comp_tendsto tendsto_natCast_atTop_atTop
    have hlt := hpow.trans_isLittleO hlo
    obtain ⟨n, hn, hhalf⟩ := ((eventually_gt_atTop 0).and (hlt.def one_half_pos)).exists
    have hpos : 0 < ‖(n : ℝ) ^ (α + 1)‖ :=
      norm_pos_iff.mpr (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _).ne'
    linarith
  · intro hα
    rcases hα.lt_or_eq with hlt | rfl
    · exact (isBigO_sum_Ico_rpow_one_iff.mpr hlt).trans
        (Real.isLittleO_const_log_atTop.comp_tendsto tendsto_natCast_atTop_atTop).isBigO
    · exact isTheta_sum_Ico_rpow_neg_one_log.1

/-- **Exact `Θ(log n)` characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = Θ(log n)` as `n → ∞` if and only if `α = -1`. -/
theorem isTheta_sum_Ico_rpow_log_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =Θ[atTop] (fun n : ℕ ↦ Real.log n) ↔ α = -1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ isTheta_sum_Ico_rpow_neg_one_log⟩
  have hle : α ≤ -1 := isBigO_sum_Ico_rpow_log_iff.mp h.1
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    have hlo := (Real.isLittleO_const_log_atTop (c := (1 : ℝ)).comp_tendsto
      tendsto_natCast_atTop_atTop).trans_isBigO
      (h.2.trans (isBigO_sum_Ico_rpow_one_iff.mpr hlt))
    obtain ⟨_, hhalf⟩ := (hlo.def one_half_pos).exists
    dsimp only [Function.comp_apply] at hhalf
    norm_num at hhalf
  · exact heq

/-- **Power-growth big-O characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = O(n^{α+1})` as `n → ∞` if and only if `-1 < α`. -/
theorem isBigO_sum_Ico_rpow_rpow_add_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) ↔
      -1 < α := by
  constructor
  · intro h
    by_contra! hα
    rcases hα.lt_or_eq with hlt | rfl
    · have hone := (isTheta_sum_Ico_rpow_one_iff.mpr hlt).2.trans h
      have hzero : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) atTop (𝓝 0) :=
        ((tendsto_rpow_neg_atTop (by linarith : 0 < -(α + 1))).comp
          tendsto_natCast_atTop_atTop).congr fun n ↦ by
            dsimp only [Function.comp_apply]
            rw [neg_neg]
      have hlim := hone.trans_tendsto hzero
      exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)
    · have hbdd : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
          fun _ : ℕ ↦ (1 : ℝ) := by
        simpa only [neg_add_cancel, Real.rpow_zero] using h
      exact (lt_irrefl (-1 : ℝ)) (isBigO_sum_Ico_rpow_one_iff.mp hbdd)
  · intro hα
    refine .of_bound (α + 1)⁻¹ (Eventually.of_forall fun n ↦ ?_)
    have : 0 < α + 1 := by linarith
    rw [Real.norm_of_nonneg (sum_nonneg fun _ _ ↦ by positivity),
      Real.norm_of_nonneg (by positivity), inv_mul_eq_div]
    exact sum_Ico_rpow_le hα n

/-- **Exact `Θ(n^{α+1})` characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = Θ(n^{α+1})` as `n → ∞` if and only if `-1 < α`. -/
theorem isTheta_sum_Ico_rpow_rpow_add_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =Θ[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (α + 1)) ↔
      -1 < α :=
  ⟨fun h ↦ isBigO_sum_Ico_rpow_rpow_add_one_iff.mp h.1,
    fun hα ↦ ⟨isBigO_sum_Ico_rpow_rpow_add_one_iff.mpr hα, isBigO_rpow_add_one_sum_Ico_rpow hα⟩⟩

/-- **Combined scale characterization of real-power partial sums.**
`∑_{j=1}^{n-1} j^α = O(n^{α+1} + 1)` as `n → ∞` if and only if `α ≠ -1`. -/
theorem isBigO_sum_Ico_rpow_rpow_add_one_add_one_iff {α : ℝ} :
    (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ α) =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (α + 1) + 1) ↔
      α ≠ -1 := by
  constructor
  · rintro h rfl
    have hbdd : (fun n : ℕ ↦ ∑ j ∈ Ico 1 n, (j : ℝ) ^ (-1 : ℝ)) =O[atTop]
        fun _ : ℕ ↦ (1 : ℝ) := by
      refine (h.congr_right fun n ↦ ?_).trans (isBigO_const_const (2 : ℝ) one_ne_zero atTop)
      rw [neg_add_cancel, Real.rpow_zero]
      norm_num
    exact (lt_irrefl (-1 : ℝ)) (isBigO_sum_Ico_rpow_one_iff.mp hbdd)
  · intro hne
    rcases hne.lt_or_gt with hlt | hgt
    · refine (isBigO_sum_Ico_rpow_one_iff.mpr hlt).trans
        (.of_bound 1 (Eventually.of_forall fun n ↦ ?_))
      have hnn : 0 ≤ (n : ℝ) ^ (α + 1) := by positivity
      rw [norm_one, Real.norm_of_nonneg (by positivity), one_mul]
      linarith
    · refine (isBigO_sum_Ico_rpow_rpow_add_one_iff.mpr hgt).trans
        (.of_bound 1 (Eventually.of_forall fun n ↦ ?_))
      have hnn : 0 ≤ (n : ℝ) ^ (α + 1) := by positivity
      rw [Real.norm_of_nonneg hnn, Real.norm_of_nonneg (by positivity), one_mul]
      linarith

/-- **Harmonic bound for a complex power sum.** If `0 ≤ M` and every weight `n ^ (1 - Re s)` with
`1 ≤ n ≤ N` is at most `M`, then `‖∑_{n=1}^{N} n ^ (-s)‖ ≤ M (1 + log N)`. -/
theorem norm_sum_Icc_cpow_neg_le_mul_one_add_log {s : ℂ} {N : ℕ} {M : ℝ} (hM₀ : 0 ≤ M)
    (hM : ∀ n : ℕ, 0 < n → n ≤ N → (n : ℝ) ^ (1 - s.re) ≤ M) :
    ‖∑ n ∈ Icc 1 N, (n : ℂ) ^ (-s)‖ ≤ M * (1 + Real.log N) := by
  refine (norm_sum_le _ _).trans ?_
  have hsum : ∑ n ∈ Icc 1 N, ‖(n : ℂ) ^ (-s)‖ ≤ ∑ n ∈ Icc 1 N, M * (n : ℝ)⁻¹ := by
    refine sum_le_sum fun n hn ↦ ?_
    obtain ⟨hn₁, hnN⟩ := mem_Icc.mp hn
    rw [Complex.norm_natCast_cpow_of_pos hn₁, Complex.neg_re, show -s.re = 1 - s.re - 1 by ring,
      Real.rpow_sub_one (by positivity), div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hM n hn₁ hnN) (by positivity)
  have hH : ∑ n ∈ Icc 1 N, (n : ℝ)⁻¹ ≤ 1 + Real.log N := by
    have := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at this
    push_cast at this
    exact this
  rw [← mul_sum] at hsum
  exact hsum.trans (mul_le_mul_of_nonneg_left hH hM₀)

end TauCeti
