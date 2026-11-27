/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import TauCeti.NumberTheory.Mertens.Basic
import TauCeti.Order.Filter.AtTopBot

/-!
# Ordered prime sums and products along slowly growing cutoffs

Let `B : ℕ → ℕ` be a monotone sequence of cutoffs tending to infinity with
`log B (k + 1) / log B k → 1`, for instance `B k = 2 ^ k` or `B k = k ^ 2`. Mertens' interval
estimate `∑_{y < p ≤ x} 1 / p = log (log x / log y) + O(1 / log y)`
(`TauCeti.exists_abs_sum_sdiff_primesLE_inv_sub_log_div_le`) bounds the reciprocal prime sum over
a block `(B k, B (k + 1)]` by `|log (log B (k + 1) / log B k)| + O(1 / log B k)`, so these block
sums tend to zero (`TauCeti.tendsto_sum_sdiff_primesLE_inv_of_tendsto_log_div`).

Consequently a cutoff `n` and the largest `B k ≤ n` differ only by primes whose reciprocals sum
to almost nothing. For `‖f p‖ ≤ C / p` the ordered sums `∑ p ≤ n, f p` converge exactly when the
sums `∑ p ≤ B k, f p` do, and for `‖g p - 1‖ ≤ C / p` the same holds for the ordered products
`∏ p ≤ n, g p`. The Euler factors `(1 - c p / p)⁻¹` with `‖c p‖ ≤ 1` are treated in
`TauCeti/NumberTheory/LSeries/BoundaryConvergence/OrderedEulerProduct.lean`.

Along an arbitrary cofinal sequence of cutoffs only the forward implication holds, and it is
`Filter.Tendsto.comp`. Some growth condition is needed for the converse: the primes in `(x, x²]`
have reciprocal sum tending to `log 2`, so for cutoffs such as `B k = 2 ^ (2 ^ k)` the block
sums do not tend to zero (`TauCeti.exists_abs_sum_sdiff_primesLE_sq_inv_sub_log_two_le`). In
`TauCeti/NumberTheory/LSeries/BoundaryConvergence/SquaringCutoff.lean` this gives Euler products
that converge along the cutoffs `2 ^ 4 ^ m` but have no ordered limit. The cutoffs passing at
most one new prime per step are handled by `Nat.tendsto_prod_primesLE_comp_iff` without any growth
condition.

## Main results

* `TauCeti.exists_abs_sum_sdiff_primesLE_sq_inv_sub_log_two_le`: the reciprocal prime sum over a
  squaring block `(n, n ^ 2]` is `log 2 + O(1 / log n)`.
* `TauCeti.tendsto_sum_sdiff_primesLE_inv_of_tendsto_log_div`: the reciprocal prime sums over the
  blocks `(B k, B (k + 1)]` tend to zero.
* `TauCeti.tendsto_sum_primesLE_comp_iff_of_tendsto_log_div`: ordered sums of `f` with
  `‖f p‖ ≤ C / p` converge along `B` exactly when they converge.
* `TauCeti.tendsto_prod_primesLE_comp_iff_of_tendsto_log_div`: the same for ordered products of
  `g` with `‖g p - 1‖ ≤ C / p`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874),
  46–62.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti

variable {B : ℕ → ℕ}

/-- **Reciprocal prime sums over slowly growing blocks.** If the cutoffs `B k` tend to infinity
and `log B (k + 1) / log B k → 1`, then the sums of `1 / p` over the primes `B k < p ≤ B (k + 1)`
tend to zero. -/
theorem tendsto_sum_sdiff_primesLE_inv_of_tendsto_log_div (hB : Tendsto B atTop atTop)
    (hlog : Tendsto (fun k ↦ Real.log (B (k + 1)) / Real.log (B k)) atTop (𝓝 1)) :
    Tendsto (fun k ↦ ∑ p ∈ Nat.primesLE (B (k + 1)) \ Nat.primesLE (B k), (p : ℝ)⁻¹) atTop
      (𝓝 0) := by
  obtain ⟨C, hC⟩ := exists_abs_sum_sdiff_primesLE_inv_sub_log_div_le
  have hlogB : Tendsto (fun k ↦ Real.log (B k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hB)
  have hupper : Tendsto (fun k ↦ |Real.log (Real.log (B (k + 1)) / Real.log (B k))| +
      C / Real.log (B k)) atTop (𝓝 0) := by
    simpa using (((Real.continuousAt_log one_ne_zero).tendsto.comp hlog).abs).add
      (tendsto_const_nhds.div_atTop hlogB)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall fun k ↦ sum_nonneg fun p _ ↦ by positivity) ?_
  filter_upwards [hB.eventually_ge_atTop 2] with k hk
  have hk2 : (2 : ℝ) ≤ B k := by exact_mod_cast hk
  rcases le_or_gt (B (k + 1)) (B k) with hle | hlt
  · -- The block is empty, and the interval estimate on `(B k, B k]` shows `0 ≤ C / log B k`.
    have hC0 := hC (B k) (B k) hk2 le_rfl
    simp only [Nat.floor_natCast, sdiff_self, bot_eq_empty, sum_empty] at hC0
    rw [sdiff_eq_empty_iff_subset.mpr (Nat.primesLE_mono hle), sum_empty]
    exact add_nonneg (abs_nonneg _) ((abs_nonneg _).trans hC0)
  have h := (abs_le.mp (hC (B k) (B (k + 1)) hk2 (by exact_mod_cast hlt.le))).2
  simp only [Nat.floor_natCast] at h
  linarith [le_abs_self (Real.log (Real.log (B (k + 1)) / Real.log (B k)))]

/-- **Reciprocal prime sums over squaring blocks.** There is an absolute constant `C` such that
for every natural number `n ≥ 2`, `|∑_{n < p ≤ n ^ 2} p⁻¹ - log 2| ≤ C / log n`. So along cutoffs
that square at each step, the block sums tend to `log 2` rather than to zero. -/
theorem exists_abs_sum_sdiff_primesLE_sq_inv_sub_log_two_le :
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n →
      |(∑ p ∈ Nat.primesLE (n ^ 2) \ Nat.primesLE n, (p : ℝ)⁻¹) - Real.log 2| ≤
        C / Real.log n := by
  obtain ⟨C, hC⟩ := exists_abs_sum_sdiff_primesLE_inv_sub_log_div_le
  refine ⟨C, fun n hn ↦ ?_⟩
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h := hC n ((n ^ 2 : ℕ) : ℝ) hn2 (by push_cast; nlinarith)
  simp only [Nat.floor_natCast] at h
  simpa [Real.log_pow, mul_div_cancel_right₀ _ hlog] using h

section Comparison

variable (hBm : Monotone B) (hB : Tendsto B atTop atTop)
  (hlog : Tendsto (fun k ↦ Real.log (B (k + 1)) / Real.log (B k)) atTop (𝓝 1))
include hBm hB hlog

omit hBm in
/-- For `n ≥ B 0` in the block `B (κ n) ≤ n < B (κ n + 1)`, the reciprocal prime sum over
`(B (κ n), n]` tends to zero as `n → ∞`, provided `κ n` tends to infinity. -/
private theorem tendsto_sum_sdiff_primesLE_block_inv {κ : ℕ → ℕ} (hκ : Tendsto κ atTop atTop)
    (hblock : ∀ n, B 0 ≤ n → B (κ n) ≤ n ∧ n < B (κ n + 1)) :
    Tendsto (fun n ↦ ∑ p ∈ Nat.primesLE n \ Nat.primesLE (B (κ n)), (p : ℝ)⁻¹) atTop (𝓝 0) := by
  refine squeeze_zero' (.of_forall fun n ↦ sum_nonneg fun p _ ↦ by positivity) ?_
    ((tendsto_sum_sdiff_primesLE_inv_of_tendsto_log_div hB hlog).comp hκ)
  filter_upwards [eventually_ge_atTop (B 0)] with n hn
  exact sum_le_sum_of_subset_of_nonneg
    (sdiff_subset_sdiff (Nat.primesLE_mono (hblock n hn).2.le) le_rfl)
    fun _ _ _ ↦ by positivity

/-- **Ordered prime sums along slowly growing cutoffs.** Let `‖f p‖ ≤ C / p` at every prime `p`,
and let the cutoffs `B k` be monotone, tend to infinity and satisfy
`log B (k + 1) / log B k → 1`. Then the sums of `f` over the primes `p ≤ B k` converge exactly
when the ordered sums over the primes `p ≤ n` do. -/
theorem tendsto_sum_primesLE_comp_iff_of_tendsto_log_div {E : Type*} [SeminormedAddCommGroup E]
    {f : ℕ → E} {C : ℝ} (hf : ∀ p, p.Prime → ‖f p‖ ≤ C / p) {L : E} :
    Tendsto (fun k ↦ ∑ p ∈ Nat.primesLE (B k), f p) atTop (𝓝 L) ↔
      Tendsto (fun n ↦ ∑ p ∈ Nat.primesLE n, f p) atTop (𝓝 L) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp hB⟩
  obtain ⟨κ, hκ, hblock⟩ := exists_tendsto_atTop_le_lt_succ hBm hB
  have hS := (tendsto_sum_sdiff_primesLE_block_inv hB hlog hκ hblock).const_mul C
  rw [mul_zero] at hS
  have hdiff : Tendsto (fun n ↦ ∑ p ∈ Nat.primesLE n, f p - ∑ p ∈ Nat.primesLE (B (κ n)), f p)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hS
    filter_upwards [eventually_ge_atTop (B 0)] with n hn
    rw [← sum_sdiff_eq_sub (Nat.primesLE_mono (hblock n hn).1), mul_sum]
    exact (norm_sum_le _ _).trans (sum_le_sum fun p hp ↦
      (hf p (Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1)).trans_eq (div_eq_mul_inv _ _))
  simpa using (h.comp hκ).add hdiff

/-- **Ordered prime products along slowly growing cutoffs.** Let `‖g p - 1‖ ≤ C / p` at every
prime `p`, and let the cutoffs `B k` be monotone, tend to infinity and satisfy
`log B (k + 1) / log B k → 1`. Then the products of `g` over the primes `p ≤ B k` converge exactly
when the ordered products over the primes `p ≤ n` do. -/
theorem tendsto_prod_primesLE_comp_iff_of_tendsto_log_div {R : Type*} [NormedCommRing R]
    [NormOneClass R] {g : ℕ → R} {C : ℝ} (hg : ∀ p, p.Prime → ‖g p - 1‖ ≤ C / p) {L : R} :
    Tendsto (fun k ↦ ∏ p ∈ Nat.primesLE (B k), g p) atTop (𝓝 L) ↔
      Tendsto (fun n ↦ ∏ p ∈ Nat.primesLE n, g p) atTop (𝓝 L) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp hB⟩
  obtain ⟨κ, hκ, hblock⟩ := exists_tendsto_atTop_le_lt_succ hBm hB
  have hS := (tendsto_sum_sdiff_primesLE_block_inv hB hlog hκ hblock).const_mul C
  rw [mul_zero] at hS
  replace hS := (Real.continuous_exp.tendsto 0).comp hS
  rw [Real.exp_zero] at hS
  -- The factors over the primes in `(B (κ n), n]` multiply to almost `1`.
  have hratio : Tendsto (fun n ↦ ∏ p ∈ Nat.primesLE n \ Nat.primesLE (B (κ n)), g p) atTop
      (𝓝 1) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) (.of_forall fun n ↦ ?_)
      (by simpa using hS.sub_const 1)
    have hprod := (Nat.primesLE n \ Nat.primesLE (B (κ n))).norm_prod_one_add_sub_one_le
      fun p ↦ g p - 1
    simp only [add_sub_cancel] at hprod
    refine hprod.trans (sub_le_sub_right (Real.exp_le_exp.mpr ?_) 1)
    rw [mul_sum]
    exact sum_le_sum fun p hp ↦
      (hg p (Nat.prime_of_mem_primesLE (mem_sdiff.mp hp).1)).trans_eq (div_eq_mul_inv _ _)
  have heq : (fun n ↦ (∏ p ∈ Nat.primesLE n \ Nat.primesLE (B (κ n)), g p) *
      ∏ p ∈ Nat.primesLE (B (κ n)), g p) =ᶠ[atTop] fun n ↦ ∏ p ∈ Nat.primesLE n, g p := by
    filter_upwards [eventually_ge_atTop (B 0)] with n hn
    exact prod_sdiff (Nat.primesLE_mono (hblock n hn).1)
  simpa using (hratio.mul (h.comp hκ)).congr' heq

end Comparison

end TauCeti
