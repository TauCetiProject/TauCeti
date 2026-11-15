/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import TauCeti.NumberTheory.Mertens.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub
import TauCeti.NumberTheory.SumPrimePow

/-!
# Mertens's second theorem in von Mangoldt form

At any prime power `p ^ k` (`k ≥ 1`), the von Mangoldt weight satisfies
`Λ(p ^ k) / (p ^ k log (p ^ k)) = 1 / (k p ^ k)`. Regrouping the finite sum
`∑_{1 ≤ n ≤ N} Λ(n) / (n log n)` by the prime base `p ≤ N` via
`Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log` expresses each prime's contribution as the
`(Nat.log p N)`-th Taylor polynomial of `-log (1 - 1 / p)`. The Taylor remainder bounds of
`TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub` and the prime-power tail estimate
`Nat.sum_primesLE_inv_pow_log_succ_le` then show that for every `N : ℕ`,
`0 ≤ ∑_{p ≤ N} -log (1 - 1 / p) - ∑_{1 ≤ n ≤ N} Λ(n) / (n log n) ≤ 3 / √N`.

Combining this `O(x ^ (-1/2))` comparison with the logarithmic Euler-product expansion of
`TauCeti.NumberTheory.Mertens.Basic` yields **Mertens's second theorem in von Mangoldt form**:
`∑_{1 ≤ n ≤ x} Λ(n) / (n log n) = log log x + γ + O(1 / log x)`, with `γ` the Euler–Mascheroni
constant (no residual higher-prime-power series, since `Λ(n) / (n log n)` already includes every
prime power `p ^ k`). Subtracting the prime terms `1 / p` recovers the convergent series of
higher-prime-power reciprocals `∑_{n ≥ 1, ¬n.Prime} Λ(n) / (n log n) = γ - M`, where `M` is
`TauCeti.meisselMertensConstant`.

## Main results

* `TauCeti.vonMangoldt_div_mul_log_prime_pow`:
  `Λ(p ^ k) / (p ^ k * log (p ^ k)) = (p⁻¹) ^ k / k` for prime `p` and all `k : ℕ`.
* `TauCeti.sum_Icc_vonMangoldt_div_mul_log_eq`: prime-base regrouping of
  `∑_{1 ≤ n ≤ N} Λ(n) / (n log n)`.
* `TauCeti.sum_Icc_vonMangoldt_div_mul_log_le_sum_primesLE_neg_log_one_sub_inv` and
  `TauCeti.sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_div_mul_log_le`:
  `0 ≤ ∑_{p ≤ N} -log (1 - 1 / p) - ∑_{1 ≤ n ≤ N} Λ(n) / (n log n) ≤ 3 / √N`.
* `TauCeti.isBigO_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub`,
  `TauCeti.tendsto_sum_Icc_vonMangoldt_div_mul_log_sub_log_log`, and
  `TauCeti.exists_abs_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub_le`:
  `∑_{1 ≤ n ≤ x} Λ(n) / (n log n) = log log x + γ + O(1 / log x)` (uniformly on `1 < x`).
* `TauCeti.hasSum_vonMangoldt_nonprime_div_mul_log`,
  `TauCeti.summable_vonMangoldt_nonprime_div_mul_log`, and
  `TauCeti.tsum_vonMangoldt_nonprime_div_mul_log`: the higher-prime-power series sums to
  `γ - meisselMertensConstant`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874),
  46–62.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., Chapter I.1,
  Theorem 1.8 and Exercise 18.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I. Classical Theory*, §2.2,
  Theorem 2.7.
-/

public section

open ArithmeticFunction Asymptotics Filter
open scoped Topology

namespace TauCeti

/-! ### Prime-power identity and finite cutoff comparison -/

/-- At any prime power `p ^ k` (including `k = 0`, where both sides vanish by division by zero),
`Λ(p ^ k) / (p ^ k * log (p ^ k)) = (p⁻¹) ^ k / k`. -/
theorem vonMangoldt_div_mul_log_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    Λ (p ^ k) / (((p ^ k : ℕ) : ℝ) * Real.log ((p ^ k : ℕ) : ℝ)) =
      ((p : ℝ)⁻¹) ^ k / (k : ℝ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hp0 : (p : ℝ) ≠ 0 := mod_cast hp.ne_zero
  have hk0 : (k : ℝ) ≠ 0 := mod_cast hk
  have hlog : Real.log (p : ℝ) ≠ 0 := (Real.log_pos (mod_cast hp.one_lt)).ne'
  rw [vonMangoldt_apply_pow hk, vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow, inv_pow]
  field_simp

/-- Regrouping `∑_{1 ≤ n ≤ N} Λ(n) / (n log n)` by the prime base expresses each prime's
contribution as the `(Nat.log p N)`-th Taylor polynomial of `-log (1 - 1 / p)`. -/
theorem sum_Icc_vonMangoldt_div_mul_log_eq (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n) =
      ∑ p ∈ Nat.primesLE N, ∑ k ∈ Finset.Icc 1 (p.log N), ((p : ℝ)⁻¹) ^ k / (k : ℝ) := by
  rw [Nat.sum_Icc_eq_sum_primesLE_sum_Icc_log
    (f := fun n : ℕ ↦ Λ n / ((n : ℝ) * Real.log n))
    (fun n hn ↦ by simp [vonMangoldt_eq_zero_iff.mpr hn])]
  exact Finset.sum_congr rfl fun p hp ↦ Finset.sum_congr rfl fun k _ ↦
    vonMangoldt_div_mul_log_prime_pow (Nat.prime_of_mem_primesLE hp) k

/-- The finite von Mangoldt sum `∑_{1 ≤ n ≤ N} Λ(n) / (n log n)` is bounded above by the
logarithmic Euler product `∑_{p ≤ N} -log (1 - 1 / p)`. -/
theorem sum_Icc_vonMangoldt_div_mul_log_le_sum_primesLE_neg_log_one_sub_inv (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n) ≤
      ∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹) := by
  rw [sum_Icc_vonMangoldt_div_mul_log_eq]
  refine Finset.sum_le_sum fun p hp ↦ ?_
  have hp1 : (1 : ℝ) < p := mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
  linarith [Real.neg_log_one_sub_sub_sum_Icc_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ)⁻¹)
    (inv_lt_one_of_one_lt₀ hp1) (p.log N)]

/-- **Quantitative comparison between the logarithmic Euler product and the von Mangoldt sum.**
For every `N : ℕ`, the omitted higher-exponent tails sum to at most `3 / √N`: each prime `p ≤ N`
has `Nat.log p N + 1 ≥ 2` and `1 - 1 / p ≥ 1 / 2`, so its Taylor remainder is at most
`1 / p ^ (Nat.log p N + 1)`. -/
theorem sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_div_mul_log_le (N : ℕ) :
    (∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹)) -
      (∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n)) ≤ 3 / √(N : ℝ) := by
  rw [sum_Icc_vonMangoldt_div_mul_log_eq, ← Finset.sum_sub_distrib]
  refine (Finset.sum_le_sum fun p hp ↦ ?_).trans (Nat.sum_primesLE_inv_pow_log_succ_le N)
  have hprime : p.Prime := Nat.prime_of_mem_primesLE hp
  have hp2 : (2 : ℝ) ≤ p := mod_cast hprime.two_le
  have hp1 : (1 : ℝ) < p := by linarith
  have hlog1 : 1 ≤ p.log N := Nat.log_pos hprime.one_lt (Nat.le_of_mem_primesLE hp)
  have hp_inv_le : (p : ℝ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le two_pos hp2
  have hden : 1 ≤ ((p.log N : ℝ) + 1) * (1 - (p : ℝ)⁻¹) := by
    have hm : (2 : ℝ) ≤ (p.log N : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hlog1
    nlinarith
  calc -Real.log (1 - (p : ℝ)⁻¹) - ∑ k ∈ Finset.Icc 1 (p.log N), ((p : ℝ)⁻¹) ^ k / (k : ℝ)
      ≤ ((p : ℝ)⁻¹) ^ (p.log N + 1) / (((p.log N : ℝ) + 1) * (1 - (p : ℝ)⁻¹)) :=
        Real.neg_log_one_sub_sub_sum_Icc_le (by positivity) (inv_lt_one_of_one_lt₀ hp1) (p.log N)
    _ ≤ ((p : ℝ)⁻¹) ^ (p.log N + 1) := div_le_self (by positivity) hden
    _ = ((p : ℝ) ^ (p.log N + 1))⁻¹ := inv_pow (p : ℝ) (p.log N + 1)

/-! ### Mertens's second theorem in von Mangoldt form -/

/-- Along real cutoffs `x → ∞`, the difference between `∑_{p ≤ x} -log (1 - 1 / p)` and
`∑_{1 ≤ n ≤ x} Λ(n) / (n log n)` is `O(x ^ (-1/2))`. -/
theorem isBigO_sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_div_mul_log :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / ((n : ℝ) * Real.log n)) =O[atTop]
      fun x ↦ x ^ (-(1 / 2 : ℝ)) := by
  have hu : (fun N : ℕ ↦ (∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹)) -
      ∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n)) =O[atTop]
      fun N : ℕ ↦ (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    refine IsBigO.of_bound 3 ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := mod_cast hN
    have h0 : 0 ≤ (∑ p ∈ Nat.primesLE N, -Real.log (1 - (p : ℝ)⁻¹)) -
        ∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n) :=
      sub_nonneg.mpr (sum_Icc_vonMangoldt_div_mul_log_le_sum_primesLE_neg_log_one_sub_inv N)
    rw [Real.norm_of_nonneg h0, Real.norm_of_nonneg (Real.rpow_nonneg hN0.le _),
      Real.rpow_neg hN0.le, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    exact sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_div_mul_log_le N
  exact hu.comp_natFloor_rpow

/-- **Mertens's second theorem in von Mangoldt form** (Tenenbaum, Chapter I.1; Montgomery &
Vaughan, Theorem 2.7):
`∑_{1 ≤ n ≤ x} Λ(n) / (n log n) = log log x + γ + O(1 / log x)` as `x → ∞`. -/
theorem isBigO_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub :
    (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / ((n : ℝ) * Real.log n)) -
      Real.log (Real.log x) - Real.eulerMascheroniConstant) =O[atTop]
      fun x ↦ (Real.log x)⁻¹ := by
  have hrpow_log : (fun x : ℝ ↦ x ^ (-(1 / 2 : ℝ))) =O[atTop] fun x ↦ (Real.log x)⁻¹ :=
    ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).inv_rev
      ((eventually_gt_atTop (1 : ℝ)).mono fun _ hx h ↦
        absurd h (Real.log_pos hx).ne')).isBigO.congr'
      ((eventually_ge_atTop (0 : ℝ)).mono fun _ hx ↦ (Real.rpow_neg hx _).symm) .rfl
  have hdiff :=
    isBigO_sum_primesLE_neg_log_one_sub_inv_sub_sum_Icc_vonMangoldt_div_mul_log.trans hrpow_log
  refine (isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub.sub hdiff).congr_left
    fun x ↦ by ring

/-- **Mertens's second theorem in von Mangoldt form, limit version**:
`∑_{1 ≤ n ≤ x} Λ(n) / (n log n) - log log x` tends to `γ` as `x → ∞`. -/
theorem tendsto_sum_Icc_vonMangoldt_div_mul_log_sub_log_log :
    Tendsto (fun x : ℝ ↦ (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / ((n : ℝ) * Real.log n)) -
      Real.log (Real.log x)) atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := (isBigO_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub.trans_tendsto
    (Real.tendsto_log_atTop.inv_tendsto_atTop)).add_const Real.eulerMascheroniConstant
  simpa using h

/-- **Mertens's second theorem in von Mangoldt form, uniform on `(1, ∞)`**: there exists `C ≥ 0`
such that `|(∑_{1 ≤ n ≤ x} Λ(n) / (n log n)) - log log x - γ| ≤ C / log x` for all `x > 1` (and
in particular for all `x ≥ 2`). -/
theorem exists_abs_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub_le :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 < x →
      |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, Λ n / ((n : ℝ) * Real.log n)) - Real.log (Real.log x) -
        Real.eulerMascheroniConstant| ≤ C / Real.log x :=
  exists_abs_comp_natFloor_sub_log_log_sub_le
    (g := fun N ↦ ∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n))
    isBigO_sum_Icc_vonMangoldt_div_mul_log_sub_log_log_sub

/-! ### Series of higher-prime-power reciprocals -/

/-- **Exact sum of the non-prime von Mangoldt reciprocal series.** Summing `Λ(n) / (n log n)` over
non-prime `n : ℕ` (that is, `1 / (k p ^ k)` over prime powers `p ^ k` with `k ≥ 2`) converges to
`γ - meisselMertensConstant`. -/
theorem hasSum_vonMangoldt_nonprime_div_mul_log :
    HasSum (fun n : ℕ ↦ if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n))
      (Real.eulerMascheroniConstant - meisselMertensConstant) := by
  set f : ℕ → ℝ := fun n ↦ if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n)
  have hf_nonneg (n : ℕ) : 0 ≤ f n := by
    simp only [f]
    split_ifs
    · exact le_rfl
    · rcases eq_or_ne n 0 with rfl | hn0
      · simp
      · exact div_nonneg vonMangoldt_nonneg
          (mul_nonneg (Nat.cast_nonneg n) (Real.log_nonneg (mod_cast Nat.pos_of_ne_zero hn0)))
  rw [hasSum_iff_tendsto_nat_of_nonneg hf_nonneg, ← tendsto_add_atTop_iff_nat 1]
  have hpart (N : ℕ) : ∑ n ∈ Finset.range (N + 1), f n =
      (∑ n ∈ Finset.Icc 1 N, Λ n / ((n : ℝ) * Real.log n)) -
        ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
    have hrange : ∑ n ∈ Finset.range (N + 1), f n = ∑ n ∈ Finset.Icc 1 N, f n := by
      refine (Finset.sum_subset (fun n hn ↦ Finset.mem_range.mpr (by
        rw [Finset.mem_Icc] at hn; lia)) fun n hnR hn ↦ ?_).symm
      rw [Finset.mem_range] at hnR
      have hn0 : n = 0 := by simp only [Finset.mem_Icc, not_and, not_le] at hn; lia
      simp [f, hn0]
    have hprimes : Finset.filter Nat.Prime (Finset.Icc 1 N) = Nat.primesLE N := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
      exact ⟨fun ⟨⟨_, hpN⟩, hp⟩ ↦ ⟨hpN, hp⟩, fun ⟨hpN, hp⟩ ↦ ⟨⟨hp.pos, hpN⟩, hp⟩⟩
    have hprime_sum : ∑ n ∈ Finset.Icc 1 N with n.Prime, Λ n / ((n : ℝ) * Real.log n) =
        ∑ p ∈ Nat.primesLE N, (p : ℝ)⁻¹ := by
      rw [hprimes]
      refine Finset.sum_congr rfl fun p hp ↦ ?_
      simpa using vonMangoldt_div_mul_log_prime_pow (Nat.prime_of_mem_primesLE hp) 1
    rw [hrange, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime f,
      ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) Nat.Prime
        (fun n ↦ Λ n / ((n : ℝ) * Real.log n)), hprime_sum]
    have h1 : ∑ n ∈ Finset.Icc 1 N with n.Prime, f n = 0 :=
      Finset.sum_eq_zero fun n hn ↦ ite_eq_left (Finset.mem_filter.mp hn).2
    have h2 : ∑ n ∈ Finset.Icc 1 N with ¬n.Prime, f n =
        ∑ n ∈ Finset.Icc 1 N with ¬n.Prime, Λ n / ((n : ℝ) * Real.log n) :=
      Finset.sum_congr rfl fun n hn ↦ ite_eq_right (Finset.mem_filter.mp hn).2
    rw [h1, h2]
    ring
  have hlim := (tendsto_sum_Icc_vonMangoldt_div_mul_log_sub_log_log.comp
    tendsto_natCast_atTop_atTop).sub
    (tendsto_sum_primesLE_inv_sub_log_log.comp tendsto_natCast_atTop_atTop)
  refine hlim.congr fun N ↦ ?_
  simp only [Function.comp_apply, Nat.floor_natCast, hpart]
  ring

/-- The non-prime von Mangoldt reciprocal series `∑_{¬n.Prime} Λ(n) / (n log n)` is summable. -/
theorem summable_vonMangoldt_nonprime_div_mul_log :
    Summable fun n : ℕ ↦ if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n) :=
  hasSum_vonMangoldt_nonprime_div_mul_log.summable

/-- Closed form of the non-prime von Mangoldt reciprocal series:
`∑'_{¬n.Prime} Λ(n) / (n log n) = γ - meisselMertensConstant`. -/
theorem tsum_vonMangoldt_nonprime_div_mul_log :
    (∑' n : ℕ, if n.Prime then 0 else Λ n / ((n : ℝ) * Real.log n)) =
      Real.eulerMascheroniConstant - meisselMertensConstant :=
  hasSum_vonMangoldt_nonprime_div_mul_log.tsum_eq

end TauCeti
