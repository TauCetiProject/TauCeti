/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Bounds
import TauCeti.NumberTheory.Chebyshev.Mertens
import TauCeti.NumberTheory.PrimeCounting
import TauCeti.Order.Filter.AtTopBot

/-!
# Ordered prime sums and products along slowly growing cutoffs

Let `B : ℕ → ℕ` be a monotone sequence of cutoffs tending to infinity with
`log B (k + 1) / log B k → 1`, for instance `B k = 2 ^ k` or `B k = k ^ 2`. Mertens' first
theorem `∑_{y < p ≤ x} log p / p = log (x / y) + O(1)`
(`Chebyshev.abs_sum_primesLE_filter_gt_log_div_sub_log_div_le`) bounds the reciprocal prime sum
over a block `(B k, B (k + 1)]` by `log B (k + 1) / log B k - 1 + O(1 / log B k)`, so these block
sums tend to zero (`TauCeti.tendsto_sum_sdiff_primesLE_inv_of_tendsto_log_div`).

Consequently a cutoff `n` and the largest `B k ≤ n` differ only by primes whose reciprocals sum
to almost nothing. For `‖f p‖ ≤ C / p` the ordered sums `∑ p ≤ n, f p` converge exactly when the
sums `∑ p ≤ B k, f p` do, and for `‖g p - 1‖ ≤ C / p` the same holds for the ordered products
`∏ p ≤ n, g p`. This applies to the Euler factors `(1 - c p / p)⁻¹` with `‖c p‖ ≤ 1`, such as
those of a Dirichlet `L`-function at `s = 1`, where only ordered cutoffs make sense.

Along an arbitrary cofinal sequence of cutoffs only the forward implication holds, and it is
`Filter.Tendsto.comp`. Some growth condition is needed for the converse: the primes in `(x, x²]`
have reciprocal sum tending to `log 2`, so for cutoffs such as `B k = 2 ^ (2 ^ k)` the block
sums do not tend to zero. The cutoffs passing at most one new prime per step are handled by
`Nat.tendsto_prod_primesLE_comp_iff` without any growth condition.

## Main results

* `TauCeti.tendsto_sum_sdiff_primesLE_inv_of_tendsto_log_div`: the reciprocal prime sums over the
  blocks `(B k, B (k + 1)]` tend to zero.
* `TauCeti.tendsto_sum_primesLE_comp_iff_of_tendsto_log_div`: ordered sums of `f` with
  `‖f p‖ ≤ C / p` converge along `B` exactly when they converge.
* `TauCeti.tendsto_prod_primesLE_comp_iff_of_tendsto_log_div`: the same for ordered products of
  `g` with `‖g p - 1‖ ≤ C / p`.
* `TauCeti.tendsto_prod_primesLE_inv_comp_iff_of_tendsto_log_div`: the same for the ordered Euler
  products `∏ p ≤ n, (1 - c p / p)⁻¹` with `‖c p‖ ≤ 1`.
* `TauCeti.tendsto_prod_primesLE_pow_inv_iff`: the special case of the cutoffs `a ^ k`.

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
  set c : ℝ := 2 * (Real.log 4 + 4)
  have hlogB : Tendsto (fun k ↦ Real.log (B k)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hB)
  have hupper : Tendsto (fun k ↦ |Real.log (B (k + 1)) / Real.log (B k) - 1| +
      c / Real.log (B k)) atTop (𝓝 0) := by
    simpa using ((hlog.sub_const 1).abs).add (tendsto_const_nhds.div_atTop hlogB)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (.of_forall fun k ↦ sum_nonneg fun p _ ↦ by positivity) ?_
  filter_upwards [hB.eventually_ge_atTop 2] with k hk
  have hpos : 0 < Real.log (B k) := Real.log_pos (by exact_mod_cast hk)
  rcases le_or_gt (B (k + 1)) (B k) with hle | hlt
  · rw [sdiff_eq_empty_iff_subset.mpr (Nat.primesLE_mono hle), sum_empty]
    positivity
  -- The block is the set of primes `p ≤ B (k + 1)` with `B k < p`, whose sum of `log p / p` is
  -- `log (B (k + 1) / B k) + O(1)` by Mertens' first theorem.
  have hk1 : (1 : ℝ) ≤ B k := by exact_mod_cast (by omega : 1 ≤ B k)
  have hk1' : (1 : ℝ) ≤ B (k + 1) := by exact_mod_cast (by omega : 1 ≤ B (k + 1))
  have hmertens := (abs_le.mp (Chebyshev.abs_sum_primesLE_filter_gt_log_div_sub_log_div_le hk1
    (by exact_mod_cast hlt.le : ((B k : ℕ) : ℝ) ≤ B (k + 1)))).2
  simp only [Nat.floor_natCast, Nat.cast_lt] at hmertens
  rw [← Nat.primesLE_sdiff_eq_filter_lt, Real.log_div (by positivity) (by positivity)] at hmertens
  calc ∑ p ∈ Nat.primesLE (B (k + 1)) \ Nat.primesLE (B k), (p : ℝ)⁻¹
      ≤ ∑ p ∈ Nat.primesLE (B (k + 1)) \ Nat.primesLE (B k),
          Real.log p / p / Real.log (B k) := by
        refine sum_le_sum fun p hp ↦ ?_
        have hp' : B k < p := by
          rw [Nat.primesLE_sdiff_eq_filter_lt, Finset.mem_filter] at hp
          exact hp.2
        rw [show (p : ℝ)⁻¹ = Real.log (B k) / p / Real.log (B k) by field_simp]
        gcongr
    _ = (∑ p ∈ Nat.primesLE (B (k + 1)) \ Nat.primesLE (B k), Real.log p / p) /
          Real.log (B k) := (sum_div _ _ _).symm
    _ ≤ (Real.log (B (k + 1)) - Real.log (B k) + c) / Real.log (B k) := by
        gcongr
        linarith
    _ = Real.log (B (k + 1)) / Real.log (B k) - 1 + c / Real.log (B k) := by
        field_simp
    _ ≤ |Real.log (B (k + 1)) / Real.log (B k) - 1| + c / Real.log (B k) := by
        gcongr
        exact le_abs_self _

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

/-- **Ordered Euler products along slowly growing cutoffs.** Let `‖c p‖ ≤ 1` at every prime `p`,
and let the cutoffs `B k` be monotone, tend to infinity and satisfy
`log B (k + 1) / log B k → 1`. Then the Euler products `∏ p ≤ B k, (1 - c p / p)⁻¹` converge
exactly when the ordered Euler products `∏ p ≤ n, (1 - c p / p)⁻¹` do. -/
theorem tendsto_prod_primesLE_inv_comp_iff_of_tendsto_log_div {c : ℕ → ℂ}
    (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) {L : ℂ} :
    Tendsto (fun k ↦ ∏ p ∈ Nat.primesLE (B k), (1 - c p / p)⁻¹) atTop (𝓝 L) ↔
      Tendsto (fun n ↦ ∏ p ∈ Nat.primesLE n, (1 - c p / p)⁻¹) atTop (𝓝 L) := by
  refine tendsto_prod_primesLE_comp_iff_of_tendsto_log_div hBm hB hlog (C := 2) fun p hp ↦ ?_
  -- With `w = c p / p` of norm at most `1 / 2`, `(1 - w)⁻¹ - 1 = w / (1 - w)` has norm at most
  -- `2 ‖w‖ ≤ 2 / p`.
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hw : ‖c p / p‖ ≤ 1 / p := by
    rw [norm_div, Complex.norm_natCast]
    gcongr
    exact hc p hp
  have hw2 : ‖c p / p‖ ≤ 1 / 2 := hw.trans (by gcongr)
  have hne : 1 - c p / p ≠ 0 := Complex.one_sub_div_natCast_ne_zero hp.one_lt (hc p hp)
  have hnorm : 1 / 2 ≤ ‖1 - c p / p‖ := by
    have := norm_sub_norm_le (1 : ℂ) (c p / p)
    rw [norm_one] at this
    linarith
  have hid : (1 - c p / p)⁻¹ - 1 = c p / p / (1 - c p / p) := by
    field_simp
    ring
  rw [hid, norm_div]
  calc ‖c p / p‖ / ‖1 - c p / p‖ ≤ (1 / p) / (1 / 2) := by gcongr
    _ = 2 / p := by ring

end Comparison

/-- **Ordered Euler products along powers.** Let `‖c p‖ ≤ 1` at every prime `p` and `2 ≤ a`.
The Euler products `∏ p ≤ a ^ k, (1 - c p / p)⁻¹` converge exactly when the ordered Euler
products `∏ p ≤ n, (1 - c p / p)⁻¹` do. -/
theorem tendsto_prod_primesLE_pow_inv_iff {a : ℕ} (ha : 2 ≤ a) {c : ℕ → ℂ}
    (hc : ∀ p, p.Prime → ‖c p‖ ≤ 1) {L : ℂ} :
    Tendsto (fun k ↦ ∏ p ∈ Nat.primesLE (a ^ k), (1 - c p / p)⁻¹) atTop (𝓝 L) ↔
      Tendsto (fun n ↦ ∏ p ∈ Nat.primesLE n, (1 - c p / p)⁻¹) atTop (𝓝 L) := by
  refine tendsto_prod_primesLE_inv_comp_iff_of_tendsto_log_div
    (pow_right_monotone (by omega)) (tendsto_pow_atTop_atTop_of_one_lt (by omega)) ?_ hc
  -- `log (a ^ (k + 1)) / log (a ^ k) = 1 + 1 / k` for `k ≥ 1`.
  have hloga : 0 < Real.log a := Real.log_pos (by exact_mod_cast ha)
  refine (by simpa using (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1 :
    Tendsto (fun k : ℕ ↦ 1 + 1 / (k : ℝ)) atTop (𝓝 1)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  simp only [Nat.cast_pow, Real.log_pow]
  field_simp [hk0]
  push_cast
  ring

end TauCeti
