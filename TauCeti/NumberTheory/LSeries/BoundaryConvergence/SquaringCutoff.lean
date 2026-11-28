/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.BoundaryConvergence.PrimeSum
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.NumberTheory.Mertens.CofinalCutoff

/-!
# Ordered Euler products along squaring cutoffs

Along monotone cutoffs `B k → ∞` with `log B (k + 1) / log B k → 1`, an ordered Euler product
`∏ p ≤ n, (1 - c p / p)⁻¹` with `‖c p‖ ≤ 1` converges exactly when its subsequence along the
cutoffs `B k` does (`TauCeti.LSeries.tendsto_prod_primesLE_inv_comp_iff_of_tendsto_log_div`).
This file shows that the growth condition cannot be dropped, even for cutoffs whose logarithms
grow geometrically: the cutoffs `B m = 2 ^ 4 ^ m`, with `log B (m + 1) / log B m = 4`, do not
suffice.

Split the primes into the squaring blocks `2 ^ 2 ^ k < p ≤ 2 ^ 2 ^ (k + 1)` and give the primes
of the `k`-th block the sign `(-1) ^ k` (`TauCeti.LSeries.squaringBlockSign`). By Mertens'
interval estimate the reciprocal prime sum over the `k`-th block is `log 2 + O(2 ^ (-k))`
(`TauCeti.exists_abs_sum_sdiff_primesLE_sq_inv_sub_log_two_le`). Over two consecutive blocks the
main terms `log 2` cancel and the errors are summable, so the signed prime sums
`∑ p ≤ n, squaringBlockSign p / p` converge along `n = 2 ^ 4 ^ m`, while along
`n = (2 ^ 4 ^ m) ^ 2` they converge to a limit larger by `log 2`. The Euler products follow the
prime sums (`TauCeti.LSeries.tendsto_prod_primesLE_inv_of_tendsto_sum_primesLE_div`): along the
second sequence their limit is twice the nonzero limit along the first, so the ordered Euler
products have no limit.

## Main results

* `TauCeti.LSeries.exists_tendsto_sum_primesLE_squaringBlockSign_div`,
  `TauCeti.LSeries.not_tendsto_sum_primesLE_squaringBlockSign_div`: the signed prime sums
  converge along `2 ^ 4 ^ m` and along `(2 ^ 4 ^ m) ^ 2`, with limits differing by `log 2`, and
  have no ordered limit.
* `TauCeti.LSeries.exists_tendsto_prod_primesLE_squaringBlockSign_inv`,
  `TauCeti.LSeries.not_tendsto_prod_primesLE_squaringBlockSign_inv`: the same for the Euler
  products `∏ p ≤ n, (1 - squaringBlockSign p / p)⁻¹`, whose limits differ by a factor `2`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874),
  46–62.
-/

public section

open Filter Finset
open scoped Topology

namespace TauCeti.LSeries

/-- The sign of the squaring block containing `n`: `squaringBlockSign n = (-1) ^ k` when
`2 ^ 2 ^ k < n ≤ 2 ^ 2 ^ (k + 1)` (`TauCeti.LSeries.squaringBlockSign_eq`). For `n ≤ 2` it is `1`;
these values play no role. -/
def squaringBlockSign (n : ℕ) : ℂ :=
  (-1) ^ Nat.log 2 (Nat.log 2 (n - 1))

/-- The squaring block signs have norm `1`. -/
@[simp] theorem norm_squaringBlockSign (n : ℕ) : ‖squaringBlockSign n‖ = 1 := by
  simp [squaringBlockSign, norm_pow]

/-- On the squaring block `2 ^ 2 ^ k < n ≤ 2 ^ 2 ^ (k + 1)` the sign is `(-1) ^ k`. -/
theorem squaringBlockSign_eq {k n : ℕ} (h₁ : 2 ^ 2 ^ k < n) (h₂ : n ≤ 2 ^ 2 ^ (k + 1)) :
    squaringBlockSign n = (-1) ^ k := by
  have h1 : 1 < 2 ^ 2 ^ k := Nat.one_lt_two_pow (pow_ne_zero k two_ne_zero)
  have hlog₁ : 2 ^ k ≤ Nat.log 2 (n - 1) := Nat.le_log_of_pow_le one_lt_two (by omega)
  have hlog₂ : Nat.log 2 (n - 1) < 2 ^ (k + 1) :=
    Nat.log_lt_of_lt_pow (by omega) (by omega)
  rw [squaringBlockSign, Nat.log_eq_of_pow_le_of_lt_pow hlog₁ hlog₂]

/-- The signed prime sum `∑ p ≤ n, squaringBlockSign p / p`. -/
local notation "𝒮" n:max => ∑ p ∈ Nat.primesLE n, squaringBlockSign p / (p : ℂ)

/-- The reciprocal prime sum over the `k`-th squaring block. -/
local notation "𝔰" k:max =>
  ∑ p ∈ Nat.primesLE (2 ^ 2 ^ (k + 1)) \ Nat.primesLE (2 ^ 2 ^ k), (p : ℝ)⁻¹

/-- Passing the `k`-th squaring block adds its reciprocal prime sum with the sign `(-1) ^ k`. -/
private theorem sum_primesLE_squaringBlockSign_succ (k : ℕ) :
    𝒮 (2 ^ 2 ^ (k + 1)) = 𝒮 (2 ^ 2 ^ k) + (-1) ^ k * ((𝔰 k : ℝ) : ℂ) := by
  have hblock : ∑ p ∈ Nat.primesLE (2 ^ 2 ^ (k + 1)) \ Nat.primesLE (2 ^ 2 ^ k),
      squaringBlockSign p / (p : ℂ) = (-1) ^ k * ((𝔰 k : ℝ) : ℂ) := by
    push_cast
    rw [mul_sum]
    refine sum_congr rfl fun p hp ↦ ?_
    obtain ⟨hp₁, hp₂⟩ := mem_sdiff.mp hp
    have hlt : 2 ^ 2 ^ k < p := by
      by_contra h
      exact hp₂ (Nat.mem_primesLE.mpr ⟨not_lt.mp h, Nat.prime_of_mem_primesLE hp₁⟩)
    rw [squaringBlockSign_eq hlt (Nat.le_of_mem_primesLE hp₁), div_eq_mul_inv]
  rw [← sum_sdiff (Nat.primesLE_mono (Nat.pow_le_pow_right two_pos
    (Nat.pow_le_pow_right two_pos k.le_succ))), hblock, add_comm]

/-- The reciprocal prime sum over the `k`-th squaring block is `log 2 + O(2 ^ (-k))`: the errors
form a summable sequence. -/
private theorem summable_sum_sdiff_primesLE_inv_sub_log_two :
    Summable fun k : ℕ ↦ 𝔰 k - Real.log 2 := by
  obtain ⟨C, hC⟩ := exists_abs_sum_sdiff_primesLE_sq_inv_sub_log_two_le
  refine Summable.of_norm_bounded (summable_geometric_two.mul_left (C / Real.log 2))
    fun k ↦ ?_
  have h := hC (2 ^ 2 ^ k) (Nat.le_self_pow (pow_ne_zero k two_ne_zero) 2)
  rw [← pow_mul, ← pow_succ] at h
  rw [Real.norm_eq_abs]
  refine h.trans_eq ?_
  push_cast
  rw [Real.log_pow, one_div_pow]
  push_cast
  field_simp

private theorem two_pow_four_pow (m : ℕ) : (2 : ℕ) ^ 4 ^ m = 2 ^ 2 ^ (2 * m) := by
  rw [pow_mul]; norm_num

private theorem two_pow_four_pow_sq (m : ℕ) : ((2 : ℕ) ^ 4 ^ m) ^ 2 = 2 ^ 2 ^ (2 * m + 1) := by
  rw [two_pow_four_pow, ← pow_mul, pow_succ]

private theorem neg_one_pow_two_mul (m : ℕ) : (-1 : ℂ) ^ (2 * m) = 1 :=
  Even.neg_one_pow ⟨m, by ring⟩

/-- After an even number of squaring blocks, the signed prime sum differs from its value at `2` by
the partial sum of the paired block errors. -/
private theorem sum_primesLE_squaringBlockSign_two_mul (m : ℕ) :
    𝒮 (2 ^ 2 ^ (2 * m)) = 𝒮 (2 ^ 2 ^ 0) +
      ((∑ j ∈ range m, ((𝔰 (2 * j) - Real.log 2) - (𝔰 (2 * j + 1) - Real.log 2)) : ℝ) : ℂ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, sum_primesLE_squaringBlockSign_succ,
      sum_primesLE_squaringBlockSign_succ, ih, sum_range_succ, neg_one_pow_two_mul,
      (Odd.neg_one_pow ⟨m, rfl⟩ : (-1 : ℂ) ^ (2 * m + 1) = -1)]
    push_cast
    ring

/-- **Signed prime sums along squaring cutoffs.** The signed prime sums
`∑ p ≤ n, squaringBlockSign p / p` converge to some `L` along the cutoffs `n = 2 ^ 4 ^ m`, and to
`L + log 2` along the squared cutoffs `n = (2 ^ 4 ^ m) ^ 2`. -/
theorem exists_tendsto_sum_primesLE_squaringBlockSign_div :
    ∃ L : ℂ,
      Tendsto (fun m : ℕ ↦ ∑ p ∈ Nat.primesLE (2 ^ 4 ^ m), squaringBlockSign p / (p : ℂ)) atTop
        (𝓝 L) ∧
      Tendsto (fun m : ℕ ↦ ∑ p ∈ Nat.primesLE ((2 ^ 4 ^ m) ^ 2),
        squaringBlockSign p / (p : ℂ)) atTop (𝓝 (L + Real.log 2)) := by
  have ht := summable_sum_sdiff_primesLE_inv_sub_log_two
  have hpair := (ht.comp_injective (mul_right_injective₀ two_ne_zero)).sub
    (ht.comp_injective ((add_left_injective 1).comp (mul_right_injective₀ two_ne_zero)))
  have heven : Tendsto (fun m : ℕ ↦ 𝒮 (2 ^ 4 ^ m)) atTop
      (𝓝 (𝒮 (2 ^ 2 ^ 0) + ((∑' j : ℕ, ((𝔰 (2 * j) - Real.log 2) - (𝔰 (2 * j + 1) - Real.log 2)) :
        ℝ) : ℂ))) := by
    refine (tendsto_const_nhds.add ((Complex.continuous_ofReal.tendsto _).comp
      hpair.hasSum.tendsto_sum_nat)).congr fun m ↦ ?_
    simp only [Function.comp_apply, two_pow_four_pow, sum_primesLE_squaringBlockSign_two_mul]
  refine ⟨_, heven, ?_⟩
  -- The odd cutoffs add one more block, with sign `+1` and sum `log 2 + o(1)`.
  have herr := (Complex.continuous_ofReal.tendsto 0).comp
    (ht.tendsto_atTop_zero.comp (tendsto_id.const_mul_atTop' two_pos))
  rw [Complex.ofReal_zero] at herr
  have hodd := (heven.add herr).add_const (Real.log 2 : ℂ)
  rw [add_zero] at hodd
  refine hodd.congr fun m ↦ ?_
  simp only [Function.comp_apply, id_eq]
  rw [two_pow_four_pow_sq, two_pow_four_pow, sum_primesLE_squaringBlockSign_succ,
    neg_one_pow_two_mul]
  push_cast
  ring

private theorem tendsto_two_pow_four_pow : Tendsto (fun m : ℕ ↦ 2 ^ 4 ^ m) atTop atTop :=
  (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))

private theorem tendsto_two_pow_four_pow_sq :
    Tendsto (fun m : ℕ ↦ (2 ^ 4 ^ m) ^ 2) atTop atTop :=
  tendsto_atTop_mono (fun _ ↦ Nat.le_self_pow two_ne_zero _) tendsto_two_pow_four_pow

/-- **The signed prime sums have no ordered limit.** Although they converge along the cutoffs
`2 ^ 4 ^ m`, the ordered sums `∑ p ≤ n, squaringBlockSign p / p` do not converge. -/
theorem not_tendsto_sum_primesLE_squaringBlockSign_div (L : ℂ) :
    ¬Tendsto (fun n : ℕ ↦ ∑ p ∈ Nat.primesLE n, squaringBlockSign p / (p : ℂ)) atTop (𝓝 L) := by
  intro h
  obtain ⟨L', heven, hodd⟩ := exists_tendsto_sum_primesLE_squaringBlockSign_div
  have h₁ := tendsto_nhds_unique (h.comp tendsto_two_pow_four_pow) heven
  have h₂ := tendsto_nhds_unique (h.comp tendsto_two_pow_four_pow_sq) hodd
  have hlog2 : (Real.log 2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos one_lt_two).ne'
  exact hlog2 (by linear_combination h₁ - h₂)

/-- **Euler products along squaring cutoffs.** The Euler products
`∏ p ≤ n, (1 - squaringBlockSign p / p)⁻¹` converge to some nonzero `L` along the cutoffs
`n = 2 ^ 4 ^ m`, and to `2 * L` along the squared cutoffs `n = (2 ^ 4 ^ m) ^ 2`. -/
theorem exists_tendsto_prod_primesLE_squaringBlockSign_inv :
    ∃ L : ℂ, L ≠ 0 ∧
      Tendsto (fun m : ℕ ↦ ∏ p ∈ Nat.primesLE (2 ^ 4 ^ m), (1 - squaringBlockSign p / p)⁻¹)
        atTop (𝓝 L) ∧
      Tendsto (fun m : ℕ ↦ ∏ p ∈ Nat.primesLE ((2 ^ 4 ^ m) ^ 2),
        (1 - squaringBlockSign p / p)⁻¹) atTop (𝓝 (2 * L)) := by
  obtain ⟨L, heven, hodd⟩ := exists_tendsto_sum_primesLE_squaringBlockSign_div
  have hc : ∀ p, p.Prime → ‖squaringBlockSign p‖ ≤ 1 := fun p _ ↦ (norm_squaringBlockSign p).le
  refine ⟨_, Complex.exp_ne_zero _,
    tendsto_prod_primesLE_inv_of_tendsto_sum_primesLE_div hc tendsto_two_pow_four_pow heven, ?_⟩
  convert tendsto_prod_primesLE_inv_of_tendsto_sum_primesLE_div hc tendsto_two_pow_four_pow_sq
    hodd using 2
  have h2 : Complex.exp (Real.log 2) = 2 := by
    rw [← Complex.ofReal_exp, Real.exp_log two_pos, Complex.ofReal_ofNat]
  rw [add_right_comm, Complex.exp_add _ (Real.log 2 : ℂ), h2, mul_comm]

/-- **The Euler products have no ordered limit.** Although they converge along the cutoffs
`2 ^ 4 ^ m`, the ordered Euler products `∏ p ≤ n, (1 - squaringBlockSign p / p)⁻¹` do not
converge. So the growth condition `log B (k + 1) / log B k → 1` in
`TauCeti.LSeries.tendsto_prod_primesLE_inv_comp_iff_of_tendsto_log_div` cannot be dropped. -/
theorem not_tendsto_prod_primesLE_squaringBlockSign_inv (L : ℂ) :
    ¬Tendsto (fun n : ℕ ↦ ∏ p ∈ Nat.primesLE n, (1 - squaringBlockSign p / p)⁻¹) atTop
      (𝓝 L) := by
  intro h
  obtain ⟨L', hL', heven, hodd⟩ := exists_tendsto_prod_primesLE_squaringBlockSign_inv
  have h₁ := tendsto_nhds_unique (h.comp tendsto_two_pow_four_pow) heven
  have h₂ := tendsto_nhds_unique (h.comp tendsto_two_pow_four_pow_sq) hodd
  exact hL' (by linear_combination h₁ - h₂)

end TauCeti.LSeries
