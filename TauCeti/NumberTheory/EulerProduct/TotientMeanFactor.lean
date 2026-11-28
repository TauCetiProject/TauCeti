/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Data.Nat.Prime.Basic
import TauCeti.Algebra.Order.Ring.Basic
import TauCeti.Analysis.Normed.Ring.InfiniteProd.Basic
import TauCeti.Analysis.PSeries
import TauCeti.Analysis.SpecialFunctions.Exp.Bounds

/-!
# The local factors `γ_n(p)` and the truncation of their Euler product

For a natural number `n` and a prime `p`, put

`γ_n(p) = 1 - 1/p + (1 + 1/(p - 1)) ^ n / p = 1 - 1/p + p ^ ((n : ℤ) - 1) / (p - 1) ^ n`,

where the exponent `n - 1` is an integer (it is `-1` for `n = 0`).

This is the average over the residues `m` modulo `p` of `(p / (p - 1)) ^ n` if `p ∣ m` and of `1`
otherwise, so `∏_p γ_n(p)` is the Euler product of the mean value of `(m / φ(m)) ^ n`. The product
appears as the leading constant of the second moment in Skorobogatov and Sofos, *Schinzel
Hypothesis on average and rational points*, where it is truncated to the primes `p ≤ log x`.

This file defines `γ_n` on real arguments, proves the local bound
`1 ≤ γ_n(p) ≤ 1 + (2 ^ n - 1) / (p (p - 1))` for `p ≥ 2`, with equality on the right at `p = 2`,
and deduces that the product of
`γ_n(k)` over any set `S` of natural numbers `k > y` is `1 + O_n(1 / y)`, with a constant that
does not depend on `S`. In particular the product over any set of primes `p > log x` is
`1 + O_n(1 / log x)`.

## Main definitions

* `TauCeti.totientMeanFactor n p`: the local factor `γ_n(p)`.

## Main results

* `TauCeti.totientMeanFactor_eq_zpow`: `γ_n(p) = 1 - 1/p + p ^ (n - 1) / (p - 1) ^ n`, with an
  integer exponent `n - 1`.
* `TauCeti.one_le_totientMeanFactor`, `TauCeti.totientMeanFactor_le`: the local bounds
  `1 ≤ γ_n(p)` for `p ≥ 1` and `γ_n(p) ≤ 1 + (2 ^ n - 1) / (p (p - 1))` for `p ≥ 2`.
* `TauCeti.totientMeanFactor_apply_two`: `γ_n(2) = (2 ^ n + 1) / 2`, the case of equality in the
  upper bound.
* `TauCeti.sum_totientMeanFactor_sub_one_le`: `∑_{k ∈ s} (γ_n(k) - 1) ≤ 4 (2 ^ n - 1) / (m + 1)`
  for a finite set `s` of natural numbers `k > m`.
* `TauCeti.multipliable_totientMeanFactor`, `TauCeti.one_le_tprod_totientMeanFactor`: the product
  of `γ_n(k)` over any set of natural numbers converges and is at least `1`, with no condition on
  the set.
* `TauCeti.tsum_totientMeanFactor_sub_one_le`, `TauCeti.tprod_totientMeanFactor_le_exp`: for a
  set `S` of natural numbers `k > m`, `∑_{k ∈ S} (γ_n(k) - 1) ≤ 4 (2 ^ n - 1) / (m + 1)` and
  `∏_{k ∈ S} γ_n(k) ≤ exp (4 (2 ^ n - 1) / (m + 1))`; these upper bounds need every element of
  `S` to exceed `m`.
* `TauCeti.abs_tprod_totientMeanFactor_sub_one_le`: `|∏_{k ∈ S} γ_n(k) - 1| ≤ C_n / y` for every
  set `S` of natural numbers `k > y > 0`, with `C_n = 4 (2 ^ n - 1) exp (4 (2 ^ n - 1))`.
* `TauCeti.abs_tprod_primes_totientMeanFactor_sub_one_le`: the case of the primes `p > log x` in
  an arbitrary set `T`.

## References

* A. N. Skorobogatov and E. Sofos, *Schinzel Hypothesis on average and rational points*,
  Invent. Math. 231 (2023), 673–739: equation (2.5) for the definition, and Lemma 4.5 for the
  truncation, whose proof is followed here with the linear bound
  `(1 + ψ) ^ n ≤ 1 + (2 ^ n - 1) ψ` on `[0, 1]`, sharp at both endpoints, in place of
  `(1 + ψ) ^ n ≤ 1 + n ψ + n 2 ^ n ψ ^ 2`.
-/

public section

open Finset

namespace TauCeti

/-- The local factor `γ_n(p) = 1 - 1/p + (1 + 1/(p - 1)) ^ n / p`: the average over the residues
`m` modulo a prime `p` of `(p / (p - 1)) ^ n` if `p ∣ m` and of `1` otherwise. It is defined for
real `p`; at `p = 0` and `p = 1` its value is `1`. -/
noncomputable def totientMeanFactor (n : ℕ) (p : ℝ) : ℝ :=
  1 - p⁻¹ + (1 + (p - 1)⁻¹) ^ n / p

/-- The defining formula of `totientMeanFactor`. -/
theorem totientMeanFactor_def (n : ℕ) (p : ℝ) :
    totientMeanFactor n p = 1 - p⁻¹ + (1 + (p - 1)⁻¹) ^ n / p :=
  (rfl)

/-- `γ_n(p) = 1 + ((1 + 1/(p - 1)) ^ n - 1) / p`. -/
theorem totientMeanFactor_eq_one_add (n : ℕ) (p : ℝ) :
    totientMeanFactor n p = 1 + ((1 + (p - 1)⁻¹) ^ n - 1) / p := by
  rw [totientMeanFactor_def]
  ring

/-- `γ_0(p) = 1`. -/
@[simp]
theorem totientMeanFactor_zero (p : ℝ) : totientMeanFactor 0 p = 1 := by
  simp [totientMeanFactor_eq_one_add]

/-- With Lean's convention `0⁻¹ = 0`, the value of `γ_n` at `0` is `1`. -/
@[simp]
theorem totientMeanFactor_apply_zero (n : ℕ) : totientMeanFactor n 0 = 1 := by
  simp [totientMeanFactor_eq_one_add]

/-- With Lean's convention `0⁻¹ = 0`, the value of `γ_n` at `1` is `1`. -/
@[simp]
theorem totientMeanFactor_apply_one (n : ℕ) : totientMeanFactor n 1 = 1 := by
  simp [totientMeanFactor_eq_one_add]

/-- The value at `2` is `γ_n(2) = (2 ^ n + 1) / 2`. This is not a simp lemma: at `n = 0` and
`n = 1` it would compete with `totientMeanFactor_zero` and `totientMeanFactor_one`. -/
theorem totientMeanFactor_apply_two (n : ℕ) : totientMeanFactor n 2 = (2 ^ n + 1) / 2 := by
  rw [totientMeanFactor_def]
  norm_num
  ring

/-- `γ_1(p) = 1 + 1 / (p (p - 1))`. -/
@[simp]
theorem totientMeanFactor_one (p : ℝ) : totientMeanFactor 1 p = 1 + (p * (p - 1))⁻¹ := by
  simp [totientMeanFactor_eq_one_add, div_eq_mul_inv, mul_comm]

/-- `γ_n(p) = 1 - 1/p + p ^ (n - 1) / (p - 1) ^ n` for `p ≠ 0, 1`, where the exponent `n - 1` is
an integer. -/
theorem totientMeanFactor_eq_zpow {p : ℝ} (hp0 : p ≠ 0) (hp1 : p ≠ 1) (n : ℕ) :
    totientMeanFactor n p = 1 - p⁻¹ + p ^ ((n : ℤ) - 1) / (p - 1) ^ n := by
  have hp1' : p - 1 ≠ 0 := sub_ne_zero.2 hp1
  have h : 1 + (p - 1)⁻¹ = p / (p - 1) := by
    field_simp
    ring
  rw [totientMeanFactor_def, h, zpow_sub_one₀ hp0, zpow_natCast]
  simp only [div_eq_mul_inv]
  ring

/-- `1 ≤ γ_n(p)` for `p ≥ 1`. -/
theorem one_le_totientMeanFactor {p : ℝ} (hp : 1 ≤ p) (n : ℕ) : 1 ≤ totientMeanFactor n p := by
  have h : 1 ≤ (1 + (p - 1)⁻¹) ^ n :=
    one_le_pow₀ (le_add_of_nonneg_right (inv_nonneg.2 (sub_nonneg.2 hp)))
  rw [totientMeanFactor_eq_one_add]
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.2 h) (zero_le_one.trans hp))

/-- `γ_n(p) ≤ 1 + (2 ^ n - 1) / (p (p - 1))` for `p ≥ 2`, with equality at `p = 2`. -/
theorem totientMeanFactor_le {p : ℝ} (hp : 2 ≤ p) (n : ℕ) :
    totientMeanFactor n p ≤ 1 + (2 ^ n - 1) / (p * (p - 1)) := by
  have hp1 : 0 < p - 1 := by linarith
  have h := one_add_pow_add_le_one_add_two_pow_mul (inv_nonneg.2 hp1.le)
    (inv_le_one_of_one_le₀ (by linarith : 1 ≤ p - 1)) n
  have key : ((1 + (p - 1)⁻¹) ^ n - 1) / p ≤ (2 ^ n - 1) / (p * (p - 1)) :=
    calc ((1 + (p - 1)⁻¹) ^ n - 1) / p ≤ (2 ^ n - 1) * (p - 1)⁻¹ / p := by gcongr; linarith
      _ = (2 ^ n - 1) / (p * (p - 1)) := by
          simp only [div_eq_mul_inv, mul_inv]
          ring
  rw [totientMeanFactor_eq_one_add]
  linarith

/-- `1 ≤ γ_n(k)` for every natural number `k`. -/
theorem one_le_totientMeanFactor_natCast (n k : ℕ) : 1 ≤ totientMeanFactor n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact one_le_totientMeanFactor (mod_cast hk) n

/-- `γ_n(k) - 1 ≤ 2 (2 ^ n - 1) / k ^ 2` for every natural number `k`. -/
theorem totientMeanFactor_natCast_sub_one_le (n k : ℕ) :
    totientMeanFactor n k - 1 ≤ 2 * (2 ^ n - 1) * ((k : ℝ) ^ 2)⁻¹ := by
  have hK : (0 : ℝ) ≤ 2 ^ n - 1 := sub_nonneg.2 (one_le_pow₀ one_le_two)
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp
    · simpa using hK
  · have hk2 : (2 : ℝ) ≤ k := mod_cast hk
    have h := totientMeanFactor_le hk2 n
    have hle : (2 ^ n - 1) / ((k : ℝ) * (k - 1)) ≤ 2 * (2 ^ n - 1) * ((k : ℝ) ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv, div_le_div_iff₀ (by nlinarith) (by positivity)]
      nlinarith [mul_nonneg hK (mul_nonneg (by linarith : (0 : ℝ) ≤ k)
        (by linarith : (0 : ℝ) ≤ k - 2))]
    linarith

/-- For a finite set `s` of natural numbers `k > m`,
`∑_{k ∈ s} (γ_n(k) - 1) ≤ 4 (2 ^ n - 1) / (m + 1)`. -/
theorem sum_totientMeanFactor_sub_one_le (n : ℕ) {m : ℕ} {s : Finset ℕ} (hs : ∀ k ∈ s, m < k) :
    ∑ k ∈ s, (totientMeanFactor n k - 1) ≤ 4 * (2 ^ n - 1) / (m + 1) := by
  have hK : (0 : ℝ) ≤ 2 * (2 ^ n - 1) :=
    mul_nonneg zero_le_two (sub_nonneg.2 (one_le_pow₀ one_le_two))
  calc ∑ k ∈ s, (totientMeanFactor n k - 1)
      ≤ ∑ k ∈ s, 2 * (2 ^ n - 1) * ((k : ℝ) ^ 2)⁻¹ :=
        sum_le_sum fun k _ ↦ totientMeanFactor_natCast_sub_one_le n k
    _ = 2 * (2 ^ n - 1) * ∑ k ∈ s, ((k : ℝ) ^ 2)⁻¹ := (mul_sum _ _ _).symm
    _ ≤ 2 * (2 ^ n - 1) * (2 / (m + 1)) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_le_two_div_of_forall_lt hs) hK
    _ = 4 * (2 ^ n - 1) / (m + 1) := by ring

/-- The series `∑_k (γ_n(k) - 1)` over the natural numbers converges. -/
theorem summable_totientMeanFactor_sub_one (n : ℕ) :
    Summable fun k : ℕ ↦ totientMeanFactor n k - 1 :=
  Summable.of_nonneg_of_le (fun k ↦ sub_nonneg.2 (one_le_totientMeanFactor_natCast n k))
    (fun k ↦ totientMeanFactor_natCast_sub_one_le n k)
    ((Real.summable_nat_pow_inv.2 one_lt_two).mul_left _)

/-- The product of the factors `γ_n(k)` over any set of natural numbers converges. -/
theorem multipliable_totientMeanFactor (n : ℕ) (S : Set ℕ) :
    Multipliable fun k : S ↦ totientMeanFactor n k := by
  have h := Real.multipliable_one_add_of_summable
    ((summable_totientMeanFactor_sub_one n).subtype (· ∈ S))
  simpa only [Function.comp_def, add_sub_cancel] using h

/-- The product of the factors `γ_n(k)` over any set of natural numbers is at least `1`. -/
theorem one_le_tprod_totientMeanFactor (n : ℕ) (S : Set ℕ) :
    1 ≤ ∏' k : S, totientMeanFactor n k :=
  le_hasProd_of_le_prod (multipliable_totientMeanFactor n S).hasProd fun _ ↦
    one_le_prod₀ fun k _ ↦ one_le_totientMeanFactor_natCast n k

/-- `γ_n(k) - 1` is nonnegative, so it is its own norm. -/
private theorem norm_totientMeanFactor_natCast_sub_one (n k : ℕ) :
    ‖totientMeanFactor n k - 1‖ = totientMeanFactor n k - 1 :=
  Real.norm_of_nonneg (sub_nonneg.2 (one_le_totientMeanFactor_natCast n k))

/-- For a set `S` of natural numbers `k > m`,
`∑_{k ∈ S} (γ_n(k) - 1) ≤ 4 (2 ^ n - 1) / (m + 1)`. -/
theorem tsum_totientMeanFactor_sub_one_le (n : ℕ) {m : ℕ} {S : Set ℕ} (hS : ∀ k ∈ S, m < k) :
    ∑' k : S, (totientMeanFactor n k - 1) ≤ 4 * (2 ^ n - 1) / (m + 1) := by
  refine Real.tsum_le_of_sum_le
    (fun k ↦ sub_nonneg.2 (one_le_totientMeanFactor_natCast n k)) fun t ↦ ?_
  have h := sum_totientMeanFactor_sub_one_le n
    (s := t.map (Function.Embedding.subtype (· ∈ S)))
    fun k hk ↦ hS k (t.property_of_mem_map_subtype hk)
  simpa only [sum_map, Function.Embedding.subtype_apply] using h

/-- For a set `S` of natural numbers `k > m`,
`∏_{k ∈ S} γ_n(k) ≤ exp (4 (2 ^ n - 1) / (m + 1))`. -/
theorem tprod_totientMeanFactor_le_exp (n : ℕ) {m : ℕ} {S : Set ℕ} (hS : ∀ k ∈ S, m < k) :
    ∏' k : S, totientMeanFactor n k ≤ Real.exp (4 * (2 ^ n - 1) / (m + 1)) := by
  have h := norm_tprod_one_add_le_exp_tsum (f := fun k : S ↦ totientMeanFactor n k - 1)
    ((summable_totientMeanFactor_sub_one n).subtype (· ∈ S)).norm
  simp only [add_sub_cancel, norm_totientMeanFactor_natCast_sub_one] at h
  exact (Real.le_norm_self _).trans
    (h.trans (Real.exp_le_exp.2 (tsum_totientMeanFactor_sub_one_le n hS)))

/-- **Truncation of the Euler product of `γ_n`.** For a real `y > 0` and any set `S` of natural
numbers `k > y`, `|∏_{k ∈ S} γ_n(k) - 1| ≤ 4 (2 ^ n - 1) exp (4 (2 ^ n - 1)) / y`. The constant
depends only on `n`. -/
theorem abs_tprod_totientMeanFactor_sub_one_le (n : ℕ) {y : ℝ} (hy : 0 < y) {S : Set ℕ}
    (hS : ∀ k ∈ S, y < k) :
    |∏' k : S, totientMeanFactor n k - 1| ≤
      4 * (2 ^ n - 1) * Real.exp (4 * (2 ^ n - 1)) / y := by
  have hK : (0 : ℝ) ≤ 4 * (2 ^ n - 1) :=
    mul_nonneg zero_le_four (sub_nonneg.2 (one_le_pow₀ one_le_two))
  have h1 := norm_tprod_one_add_sub_one_le (f := fun k : S ↦ totientMeanFactor n k - 1)
    ((summable_totientMeanFactor_sub_one n).subtype (· ∈ S)).norm
  simp only [add_sub_cancel, norm_totientMeanFactor_natCast_sub_one] at h1
  rw [Real.norm_eq_abs] at h1
  have h2 := tsum_totientMeanFactor_sub_one_le n fun k hk ↦ (Nat.floor_lt hy.le).2 (hS k hk)
  have ht0 : 0 ≤ 4 * (2 ^ n - 1) / ((⌊y⌋₊ : ℝ) + 1) := div_nonneg hK (by positivity)
  have hty : 4 * (2 ^ n - 1) / ((⌊y⌋₊ : ℝ) + 1) ≤ 4 * (2 ^ n - 1) / y :=
    div_le_div_of_nonneg_left hK hy (Nat.lt_floor_add_one y).le
  have ht1 : 4 * (2 ^ n - 1) / ((⌊y⌋₊ : ℝ) + 1) ≤ 4 * (2 ^ n - 1) :=
    div_le_self hK (le_add_of_nonneg_left (Nat.cast_nonneg _))
  have h3 := abs_exp_sub_one_le_mul_exp ((abs_of_nonneg ht0).trans_le hty)
    ((abs_of_nonneg ht0).trans_le ht1)
  calc |∏' k : S, totientMeanFactor n k - 1|
      ≤ Real.exp (∑' k : S, (totientMeanFactor n k - 1)) - 1 := h1
    _ ≤ Real.exp (4 * (2 ^ n - 1) / ((⌊y⌋₊ : ℝ) + 1)) - 1 :=
        sub_le_sub_right (Real.exp_le_exp.2 h2) 1
    _ ≤ |Real.exp (4 * (2 ^ n - 1) / ((⌊y⌋₊ : ℝ) + 1)) - 1| := le_abs_self _
    _ ≤ 4 * (2 ^ n - 1) / y * Real.exp (4 * (2 ^ n - 1)) := h3
    _ = 4 * (2 ^ n - 1) * Real.exp (4 * (2 ^ n - 1)) / y := by ring

/-- **Truncation of the Euler product of `γ_n` over primes.** For a real `x > 1` and any set `T`
of natural numbers, the product of `γ_n(p)` over the primes `p > log x` in `T` differs from `1`
by at most `4 (2 ^ n - 1) exp (4 (2 ^ n - 1)) / log x`. -/
theorem abs_tprod_primes_totientMeanFactor_sub_one_le (n : ℕ) {x : ℝ} (hx : 1 < x) (T : Set ℕ) :
    |∏' p : {p : ℕ | p.Prime ∧ Real.log x < p ∧ p ∈ T}, totientMeanFactor n p - 1| ≤
      4 * (2 ^ n - 1) * Real.exp (4 * (2 ^ n - 1)) / Real.log x :=
  abs_tprod_totientMeanFactor_sub_one_le n (Real.log_pos hx) fun _ hp ↦ hp.2.1

/-! ### Examples -/

example : totientMeanFactor 1 2 = 3 / 2 := by norm_num

example : totientMeanFactor 2 3 = 17 / 12 := by
  rw [totientMeanFactor_def]
  norm_num

/-- At `p = 2` the upper bound `totientMeanFactor_le` is an equality. -/
example (n : ℕ) : totientMeanFactor n 2 = 1 + (2 ^ n - 1) / (2 * (2 - 1)) := by
  rw [totientMeanFactor_apply_two]
  ring

example (S : Set ℕ) : ∏' k : S, totientMeanFactor 0 k = 1 := by simp

end TauCeti
