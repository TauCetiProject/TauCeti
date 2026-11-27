/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import TauCeti.NumberTheory.Harmonic.Remainder

/-!
# The average order of the divisor function

Write `τ(n) = σ₀(n)` for the number of divisors of `n`. This file proves Dirichlet's theorem that
`τ(n)` is `log n` on average, in the form

  `∑_{n ≤ x} τ(n) = x log x + (2γ - 1) x + O(√x)`,

where `γ` is the Euler–Mascheroni constant, with the explicit error `6 √x` for every real
`x ≥ 0`.

The proof is Dirichlet's hyperbola method. The sum counts the pairs `(a, b)` of positive integers
with `a b ≤ N`, and such a pair has `a ≤ M` or `b ≤ M` for `M = ⌊√N⌋`. Counting the pairs with
`a ≤ M`, those with `b ≤ M`, and the `M²` pairs with both, gives the exact identity
`∑_{n ≤ N} τ(n) + M² = 2 ∑_{a ≤ M} ⌊N / a⌋`. Replacing `⌊N / a⌋` by `x / a` costs at most `M`, and
the harmonic sum `∑_{a ≤ M} 1 / a` is `log M + γ` up to `1 / (2M)`
(`TauCeti.harmonic_sub_log_sub_eulerMascheroniConstant_le`).

## Main results

* `ArithmeticFunction.sum_Ioc_sigma_zero_add_sqrt_sq`: the hyperbola identity
  `∑_{n ≤ N} τ(n) + ⌊√N⌋² = 2 ∑_{a ≤ ⌊√N⌋} ⌊N / a⌋`, and
  `ArithmeticFunction.sum_Ioc_sigma_zero_natFloor_add_sq`, the same with a real cutoff.
* `ArithmeticFunction.abs_sum_Ioc_sigma_zero_sub_le`:
  `|∑_{n ≤ x} τ(n) - (x log x + (2γ - 1) x)| ≤ 6 √x` for `x ≥ 0`.
* `ArithmeticFunction.isBigO_sum_Ioc_sigma_zero_sub`: the error is `O(√x)` as `x → ∞`.

## References

* D. Koukoulopoulos, *The Distribution of Prime Numbers*, Graduate Studies in Mathematics 203,
  AMS (2019), Theorem 3.3.
-/

public section

open Finset Real
open scoped ArithmeticFunction.sigma

namespace ArithmeticFunction

/-- For `a` above `√N`, the multiples `a b ≤ N` have `b ≤ √N`, so they are counted by `N / a`. -/
private theorem card_filter_mul_le_of_sqrt_lt {N a : ℕ} (ha : N.sqrt < a) :
    #{b ∈ Ioc 0 N.sqrt | a * b ≤ N} = N / a := by
  have ha0 : 0 < a := Nat.zero_lt_of_lt ha
  have h : {b ∈ Ioc 0 N.sqrt | a * b ≤ N} = Ioc 0 (N / a) := by
    ext b
    simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le ha0, mul_comm a b]
    refine ⟨fun ⟨⟨hb0, _⟩, h⟩ ↦ ⟨hb0, h⟩, fun ⟨hb0, h⟩ ↦ ⟨⟨hb0, ?_⟩, h⟩⟩
    by_contra hb
    exact absurd ((Nat.mul_le_mul (Nat.succ_le_of_lt (not_le.1 hb)) (Nat.succ_le_of_lt ha)).trans h)
      (not_le.2 (Nat.lt_succ_sqrt N))
  rw [h, Nat.card_Ioc, Nat.sub_zero]

/-- For `b ≥ 1`, the `a` in `(√N, N]` with `a b ≤ N` are those in `(√N, N / b]`. -/
private theorem card_filter_mul_le_of_pos {N b : ℕ} (hb : 0 < b) :
    #{a ∈ Ioc N.sqrt N | a * b ≤ N} = N / b - N.sqrt := by
  have h : {a ∈ Ioc N.sqrt N | a * b ≤ N} = Ioc N.sqrt (N / b) := by
    ext a
    simp only [mem_filter, mem_Ioc, Nat.le_div_iff_mul_le hb]
    exact ⟨fun ⟨⟨h₁, _⟩, h⟩ ↦ ⟨h₁, h⟩,
      fun ⟨h₁, h⟩ ↦ ⟨⟨h₁, (Nat.le_mul_of_pos_right a hb).trans h⟩, h⟩⟩
  rw [h, Nat.card_Ioc]

/-- **Dirichlet's hyperbola identity** for the divisor function:
`∑_{n ≤ N} τ(n) + M² = 2 ∑_{a ≤ M} ⌊N / a⌋`, where `M = ⌊√N⌋`. -/
theorem sum_Ioc_sigma_zero_add_sqrt_sq (N : ℕ) :
    ∑ n ∈ Ioc 0 N, σ 0 n + N.sqrt ^ 2 = 2 * ∑ a ∈ Ioc 0 N.sqrt, N / a := by
  have hswap : ∑ a ∈ Ioc N.sqrt N, N / a = ∑ b ∈ Ioc 0 N.sqrt, (N / b - N.sqrt) :=
    calc ∑ a ∈ Ioc N.sqrt N, N / a
        = ∑ a ∈ Ioc N.sqrt N, ∑ b ∈ Ioc 0 N.sqrt, if a * b ≤ N then 1 else 0 :=
          sum_congr rfl fun a ha ↦ by
            rw [← card_filter, card_filter_mul_le_of_sqrt_lt (mem_Ioc.1 ha).1]
      _ = ∑ b ∈ Ioc 0 N.sqrt, ∑ a ∈ Ioc N.sqrt N, if a * b ≤ N then 1 else 0 := sum_comm
      _ = ∑ b ∈ Ioc 0 N.sqrt, (N / b - N.sqrt) :=
          sum_congr rfl fun b hb ↦ by
            rw [← card_filter, card_filter_mul_le_of_pos (mem_Ioc.1 hb).1]
  have hge : ∀ b ∈ Ioc 0 N.sqrt, N.sqrt ≤ N / b := fun b hb ↦ by
    rw [Nat.le_div_iff_mul_le (mem_Ioc.1 hb).1]
    exact (Nat.mul_le_mul_left _ (mem_Ioc.1 hb).2).trans (Nat.sqrt_le N)
  have hsq : N.sqrt ^ 2 = ∑ _b ∈ Ioc 0 N.sqrt, N.sqrt := by simp [sq]
  rw [sum_Ioc_sigma0_eq_sum_div, ← sum_Ioc_consecutive (fun a ↦ N / a) (Nat.zero_le _)
    (Nat.sqrt_le_self N), hswap, hsq, add_assoc, ← sum_add_distrib, two_mul]
  exact congrArg _ (sum_congr rfl fun b hb ↦ Nat.sub_add_cancel (hge b hb))

/-! ### The average order -/

private theorem natCast_sqrt_floor_le (x : ℝ) : ((⌊x⌋₊.sqrt : ℕ) : ℝ) ≤ √x := by
  rcases le_or_gt 0 x with hx | hx
  · exact nat_sqrt_le_real_sqrt.trans (sqrt_le_sqrt (Nat.floor_le hx))
  · simp [Nat.floor_of_nonpos hx.le, sqrt_eq_zero_of_nonpos hx.le]

private theorem sqrt_lt_natCast_sqrt_floor_add_one (x : ℝ) : √x < (⌊x⌋₊.sqrt : ℕ) + 1 := by
  rw [sqrt_lt' (by positivity)]
  have h : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ ((⌊x⌋₊.sqrt + 1) ^ 2 : ℕ) :=
    Nat.cast_le.2 (Nat.succ_le_of_lt (Nat.lt_succ_sqrt' _))
  push_cast at h
  linarith [Nat.lt_floor_add_one x]

private theorem natFloor_sqrt (x : ℝ) : ⌊√x⌋₊ = ⌊x⌋₊.sqrt :=
  (Nat.floor_eq_iff (sqrt_nonneg x)).2
    ⟨natCast_sqrt_floor_le x, sqrt_lt_natCast_sqrt_floor_add_one x⟩

/-- **Dirichlet's hyperbola identity** for the divisor function, with a real cutoff:
`∑_{n ≤ x} τ(n) + ⌊√x⌋² = 2 ∑_{a ≤ √x} ⌊x / a⌋`. -/
theorem sum_Ioc_sigma_zero_natFloor_add_sq (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, σ 0 n + ⌊√x⌋₊ ^ 2 = 2 * ∑ a ∈ Ioc 0 ⌊√x⌋₊, ⌊x / a⌋₊ := by
  simp only [natFloor_sqrt, Nat.floor_div_natCast]
  exact sum_Ioc_sigma_zero_add_sqrt_sq _

private theorem harmonic_eq_sum_Ioc_inv (M : ℕ) :
    (harmonic M : ℝ) = ∑ a ∈ Ioc 0 M, (a : ℝ)⁻¹ := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rfl

/-- `∑_{a ≤ M} ⌊x / a⌋ ≤ x H_M`, where `H_M` is the `M`-th harmonic number. -/
private theorem sum_Ioc_natCast_floor_div_le {x : ℝ} (hx : 0 ≤ x) (M : ℕ) :
    ∑ a ∈ Ioc 0 M, ((⌊x⌋₊ / a : ℕ) : ℝ) ≤ x * harmonic M := by
  rw [harmonic_eq_sum_Ioc_inv, mul_sum]
  refine sum_le_sum fun a _ ↦ Nat.cast_div_le.trans ?_
  rw [← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right (Nat.floor_le hx) (Nat.cast_nonneg a)

/-- `x H_M - M ≤ ∑_{a ≤ M} ⌊x / a⌋`, where `H_M` is the `M`-th harmonic number. -/
private theorem sub_le_sum_Ioc_natCast_floor_div (x : ℝ) (M : ℕ) :
    x * harmonic M - M ≤ ∑ a ∈ Ioc 0 M, ((⌊x⌋₊ / a : ℕ) : ℝ) := by
  have hcard : (M : ℝ) = ∑ _a ∈ Ioc 0 M, (1 : ℝ) := by simp
  rw [harmonic_eq_sum_Ioc_inv, mul_sum, hcard, ← sum_sub_distrib]
  refine sum_le_sum fun a _ ↦ ?_
  rw [← Nat.floor_div_natCast, ← div_eq_mul_inv]
  linarith [Nat.lt_floor_add_one (x / a)]

/-- For `M = ⌊√⌊x⌋⌋`, `log √x - 1 / M ≤ log M`. For `x < 1`, where `M = 0`, this reads
`log √x ≤ 0`. -/
private theorem log_sqrt_sub_le (x : ℝ) :
    log √x - 1 / (⌊x⌋₊.sqrt : ℕ) ≤ log (⌊x⌋₊.sqrt : ℕ) := by
  rcases lt_or_ge x 1 with hx | hx
  · have hM : ⌊x⌋₊.sqrt = 0 := by rw [Nat.floor_eq_zero.2 hx, Nat.sqrt_zero]
    have hs : √x ≤ 1 := (sqrt_le_left zero_le_one).2 (by simpa using hx.le)
    simpa [hM] using log_nonpos (sqrt_nonneg x) hs
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hM : (0 : ℝ) < (⌊x⌋₊.sqrt : ℕ) := by
    exact_mod_cast Nat.sqrt_pos.2 (Nat.floor_pos.2 hx)
  have hsM := sqrt_lt_natCast_sqrt_floor_add_one x
  have h := log_le_sub_one_of_pos (div_pos (sqrt_pos.2 hx0) hM)
  rw [log_div (sqrt_pos.2 hx0).ne' hM.ne'] at h
  have h' : √x / (⌊x⌋₊.sqrt : ℕ) - 1 ≤ 1 / (⌊x⌋₊.sqrt : ℕ) := by
    rw [div_sub_one hM.ne', div_le_div_iff_of_pos_right hM]
    linarith
  linarith

/-- For `0 ≤ x < 1` the main term `x log x + (2γ - 1) x` is at most `6 √x` in absolute value. -/
private theorem abs_mul_log_add_le_of_lt_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    |x * log x + (2 * eulerMascheroniConstant - 1) * x| ≤ 6 * √x := by
  rcases hx.eq_or_lt with rfl | hx0
  · simp
  have hs : 0 < √x := sqrt_pos.2 hx0
  have hs1 : √x < 1 := (sqrt_lt' zero_lt_one).2 (by simpa using hx1)
  have hxs : x = √x * √x := (mul_self_sqrt hx).symm
  have hlog : log x = 2 * log √x := by rw [log_sqrt hx]; ring
  have hlog_le : log √x ≤ 0 := log_nonpos hs.le hs1.le
  have hlog_ge : √x * log √x ≥ √x - 1 := by
    have h := log_le_sub_one_of_pos (inv_pos.2 hs)
    rw [log_inv] at h
    have h' := mul_le_mul_of_nonneg_left h hs.le
    rw [mul_sub, mul_inv_cancel₀ hs.ne'] at h'
    linarith
  have hγ₁ := one_half_lt_eulerMascheroniConstant
  have hγ₂ := eulerMascheroniConstant_lt_two_thirds
  have hprod : x * log x = 2 * √x * (√x * log √x) := by rw [hlog]; nlinarith [hxs]
  rw [hprod, abs_le]
  constructor <;> nlinarith [mul_nonneg hs.le hs.le, mul_nonpos_of_nonneg_of_nonpos hs.le hlog_le]

/-- **Dirichlet's theorem on the average order of the divisor function**, with an explicit error:
`|∑_{n ≤ x} τ(n) - (x log x + (2γ - 1) x)| ≤ 6 √x` for every real `x ≥ 0`, where `γ` is the
Euler–Mascheroni constant. -/
theorem abs_sum_Ioc_sigma_zero_sub_le {x : ℝ} (hx : 0 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) - (x * log x + (2 * eulerMascheroniConstant - 1) * x)| ≤
      6 * √x := by
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [Nat.floor_eq_zero.2 hx1, Ioc_self, sum_empty, zero_sub, abs_neg]
    exact abs_mul_log_add_le_of_lt_one hx hx1
  -- Notation: `N = ⌊x⌋₊`, `M = ⌊√N⌋`, and `H` the `M`-th harmonic number.
  have hM : 0 < ⌊x⌋₊.sqrt := Nat.sqrt_pos.2 (Nat.floor_pos.2 hx1)
  have hM1 : (1 : ℝ) ≤ (⌊x⌋₊.sqrt : ℕ) := by exact_mod_cast hM
  have hMs := natCast_sqrt_floor_le x
  have hsM := sqrt_lt_natCast_sqrt_floor_add_one x
  have hxs : x = √x * √x := (mul_self_sqrt hx).symm
  -- The hyperbola identity, with the terms `⌊N / a⌋` compared with `x / a`.
  have hid : ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) + (⌊x⌋₊.sqrt : ℕ) ^ 2 =
      2 * ∑ a ∈ Ioc 0 ⌊x⌋₊.sqrt, ((⌊x⌋₊ / a : ℕ) : ℝ) := by
    exact_mod_cast sum_Ioc_sigma_zero_add_sqrt_sq ⌊x⌋₊
  have hup := sum_Ioc_natCast_floor_div_le hx ⌊x⌋₊.sqrt
  have hlo := sub_le_sum_Ioc_natCast_floor_div x ⌊x⌋₊.sqrt
  -- The harmonic number and the logarithm of `M`.
  have hh_up := TauCeti.harmonic_sub_log_sub_eulerMascheroniConstant_le ⌊x⌋₊.sqrt
  have hh_lo : 0 ≤ (harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) - eulerMascheroniConstant :=
    le_trans (by positivity)
      (TauCeti.one_div_two_mul_add_le_harmonic_sub_log_sub_eulerMascheroniConstant hM.ne')
  have hlogx : log x = 2 * log √x := by rw [log_sqrt hx]; ring
  have hL_up : log (⌊x⌋₊.sqrt : ℕ) ≤ log √x := log_le_log (by linarith) hMs
  have hL_lo := log_sqrt_sub_le x
  -- The sizes of `x / M` and `x - M²`.
  have hxM : x / (⌊x⌋₊.sqrt : ℕ) ≤ 2 * √x := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sqrt_nonneg x]
  have hsub_up : x - (⌊x⌋₊.sqrt : ℕ) ^ 2 ≤ 2 * √x := by nlinarith [sqrt_nonneg x]
  have hsub_lo : 0 ≤ x - (⌊x⌋₊.sqrt : ℕ) ^ 2 := by nlinarith [sqrt_nonneg x]
  have hxh_up : x * ((harmonic ⌊x⌋₊.sqrt : ℝ) - log (⌊x⌋₊.sqrt : ℕ) - eulerMascheroniConstant) ≤
      x / (⌊x⌋₊.sqrt : ℕ) / 2 := by
    refine (mul_le_mul_of_nonneg_left hh_up hx).trans (le_of_eq ?_)
    field_simp
  have hxh_lo := mul_nonneg hx hh_lo
  have hxL_up := mul_le_mul_of_nonneg_left hL_up hx
  have hxL_lo := mul_le_mul_of_nonneg_left hL_lo hx
  rw [mul_sub, mul_one_div] at hxL_lo
  rw [hlogx, abs_le]
  constructor <;> nlinarith [sqrt_nonneg x]

/-- **Dirichlet's theorem on the average order of the divisor function**:
`∑_{n ≤ x} τ(n) = x log x + (2γ - 1) x + O(√x)` as `x → ∞`. -/
theorem isBigO_sum_Ioc_sigma_zero_sub :
    (fun x : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, (σ 0 n : ℝ) -
      (x * log x + (2 * eulerMascheroniConstant - 1) * x)) =O[Filter.atTop] fun x ↦ √x :=
  Asymptotics.IsBigO.of_bound 6 <| (Filter.eventually_ge_atTop 0).mono fun x hx ↦ by
    rw [norm_eq_abs, norm_eq_abs, abs_of_nonneg (sqrt_nonneg x)]
    exact abs_sum_Ioc_sigma_zero_sub_le hx

end ArithmeticFunction
