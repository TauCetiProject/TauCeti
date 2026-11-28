/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Floor.Semiring
public import TauCeti.NumberTheory.ArithmeticFunction.VonMangoldt.Even

/-!
# The truncated von Mangoldt function

Möbius inversion writes the von Mangoldt function as `Λ(n) = -∑_{d ∣ n} μ(d) log d`. Cutting the
sum off at a real `z` gives the *truncated von Mangoldt function*

  `Λ_z(n) = -∑_{1 ≤ d ≤ z, d ∣ n} μ(d) log d`,

defined for every integer `n`; at `n = 0` every positive `d ≤ z` occurs. It agrees with the even
extension `TauCeti.evenVonMangoldt` of `Λ` once `z ≥ |n|` and `n ≠ 0`, and the difference
`E_z(n) = Λ(|n|) - Λ_z(n)` is the *truncation error*. Both are even functions of `n`. For
`n ≠ 0` the error is the tail of the Möbius sum, `E_z(n) = -∑_{d ∣ n, d > z} μ(d) log d`. They are
used to replace `Λ` by a short divisor sum in sums over the values of integer polynomials, as in
Skorobogatov and Sofos, *Schinzel Hypothesis on average and rational points*, Invent. Math. 231
(2023), §3.1, p. 691, where both are defined for natural numbers.

## Main definitions

* `TauCeti.truncatedVonMangoldt z n`: the truncated von Mangoldt function `Λ_z(n)`.
* `TauCeti.vonMangoldtTruncationError z n`: the truncation error `E_z(n)`.

## Main results

* `TauCeti.truncatedVonMangoldt_eq_neg_sum_divisors`: for `n ≠ 0`,
  `Λ_z(n) = -∑_{d ∣ |n|, d ≤ z} μ(d) log d`.
* `TauCeti.truncatedVonMangoldt_eq_evenVonMangoldt_of_natAbs_le`: `Λ_z(n) = Λ(|n|)` for `n ≠ 0`
  and `|n| ≤ z`.
* `TauCeti.truncatedVonMangoldt_apply_zero`: `Λ_z(0) = -∑_{1 ≤ d ≤ z} μ(d) log d`.
* `TauCeti.truncatedVonMangoldt_eq_zero_of_lt_two`: `Λ_z = 0` for `z < 2`.
* `TauCeti.vonMangoldtTruncationError_eq_neg_sum_divisors`: for `n ≠ 0`,
  `E_z(n) = -∑_{d ∣ |n|, d > z} μ(d) log d`.
* `TauCeti.vonMangoldtTruncationError_eq_zero_of_natAbs_le`: `E_z(n) = 0` for `n ≠ 0` and
  `|n| ≤ z`.
-/

public section

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

namespace TauCeti

variable {z : ℝ} {n : ℤ}

/-- The truncated von Mangoldt function `Λ_z(n) = -∑_{1 ≤ d ≤ z, d ∣ n} μ(d) log d`, for a real
cutoff `z` and an integer `n`. At `n = 0` the sum is over all `1 ≤ d ≤ z`. -/
noncomputable def truncatedVonMangoldt (z : ℝ) (n : ℤ) : ℝ :=
  -∑ d ∈ Ioc 0 ⌊z⌋₊ with ((d : ℕ) : ℤ) ∣ n, (μ d : ℝ) * Real.log d

/-- The defining formula of the truncated von Mangoldt function. -/
theorem truncatedVonMangoldt_def (z : ℝ) (n : ℤ) :
    truncatedVonMangoldt z n =
      -∑ d ∈ Ioc 0 ⌊z⌋₊ with ((d : ℕ) : ℤ) ∣ n, (μ d : ℝ) * Real.log d :=
  (rfl)

/-- The truncated von Mangoldt function is even. -/
@[simp]
theorem truncatedVonMangoldt_neg (z : ℝ) (n : ℤ) :
    truncatedVonMangoldt z (-n) = truncatedVonMangoldt z n := by
  simp only [truncatedVonMangoldt_def, dvd_neg]

/-- At `n = 0` every positive `d ≤ z` divides `n`:
`Λ_z(0) = -∑_{1 ≤ d ≤ z} μ(d) log d`. -/
theorem truncatedVonMangoldt_apply_zero (z : ℝ) :
    truncatedVonMangoldt z 0 = -∑ d ∈ Ioc 0 ⌊z⌋₊, (μ d : ℝ) * Real.log d := by
  simp only [truncatedVonMangoldt_def, dvd_zero, filter_true]

/-- For `z < 2` the only term is `d = 1`, so the truncated von Mangoldt function vanishes. -/
theorem truncatedVonMangoldt_eq_zero_of_lt_two (hz : z < 2) (n : ℤ) :
    truncatedVonMangoldt z n = 0 := by
  have hfloor : ⌊z⌋₊ < 2 := (Nat.floor_lt' two_ne_zero).2 (by simpa using hz)
  rw [truncatedVonMangoldt_def, neg_eq_zero]
  refine sum_eq_zero fun d hd ↦ ?_
  obtain rfl : d = 1 := by
    have := mem_Ioc.1 (mem_filter.1 hd).1
    omega
  simp

/-- For `n ≠ 0` the truncated von Mangoldt function is a sum over the divisors `d ≤ z` of `|n|`:
`Λ_z(n) = -∑_{d ∣ |n|, d ≤ z} μ(d) log d`. -/
theorem truncatedVonMangoldt_eq_neg_sum_divisors (z : ℝ) (hn : n ≠ 0) :
    truncatedVonMangoldt z n =
      -∑ d ∈ n.natAbs.divisors with ((d : ℕ) : ℝ) ≤ z, (μ d : ℝ) * Real.log d := by
  have hset : {d ∈ Ioc 0 ⌊z⌋₊ | ((d : ℕ) : ℤ) ∣ n} =
      {d ∈ n.natAbs.divisors | ((d : ℕ) : ℝ) ≤ z} := by
    ext d
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors, Int.natCast_dvd]
    constructor
    · rintro ⟨⟨hd0, hdz⟩, hdvd⟩
      exact ⟨⟨hdvd, Int.natAbs_ne_zero.2 hn⟩, (Nat.le_floor_iff' hd0.ne').1 hdz⟩
    · rintro ⟨⟨hdvd, -⟩, hdz⟩
      have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Int.natAbs_pos.2 hn)
      exact ⟨⟨hd0, (Nat.le_floor_iff' hd0.ne').2 hdz⟩, hdvd⟩
  rw [truncatedVonMangoldt_def, hset]

/-- For `n ≠ 0` and `|n| ≤ z` the cutoff is not felt: `Λ_z(n) = Λ(|n|)`. -/
theorem truncatedVonMangoldt_eq_evenVonMangoldt_of_natAbs_le (hn : n ≠ 0)
    (hz : (n.natAbs : ℝ) ≤ z) : truncatedVonMangoldt z n = evenVonMangoldt n := by
  have hsum := sum_moebius_mul_log_eq (n := n.natAbs)
  simp only [log_apply] at hsum
  rw [truncatedVonMangoldt_eq_neg_sum_divisors z hn, filter_true_of_mem fun d hd ↦
    (Nat.cast_le.2 (Nat.le_of_dvd (Int.natAbs_pos.2 hn) (Nat.dvd_of_mem_divisors hd))).trans hz,
    hsum, neg_neg, evenVonMangoldt_def]

/-- At a prime `p` of `ℤ` with `|p| ≤ z`, the truncated von Mangoldt function is `log |p|`,
written `Real.log p`. -/
theorem truncatedVonMangoldt_apply_prime_eq_log_of_le {p : ℤ} (hp : Prime p)
    (hz : (p.natAbs : ℝ) ≤ z) : truncatedVonMangoldt z p = Real.log p := by
  rw [truncatedVonMangoldt_eq_evenVonMangoldt_of_natAbs_le hp.ne_zero hz,
    evenVonMangoldt_apply_prime hp]

/-- At a prime `p` of `ℤ` with `|p| > z`, the only divisor of `|p|` up to `z` is `1`, so the
truncated von Mangoldt function vanishes. -/
theorem truncatedVonMangoldt_apply_prime_eq_zero_of_lt {p : ℤ} (hp : Prime p)
    (hz : z < p.natAbs) : truncatedVonMangoldt z p = 0 := by
  rw [truncatedVonMangoldt_eq_neg_sum_divisors z hp.ne_zero, neg_eq_zero]
  refine sum_eq_zero fun d hd ↦ ?_
  obtain ⟨hd, hdz⟩ := mem_filter.1 hd
  rcases (Nat.dvd_prime (Int.prime_iff_natAbs_prime.1 hp)).1 (Nat.dvd_of_mem_divisors hd) with
    rfl | rfl
  · simp
  · exact absurd hdz (not_le.2 hz)

/-- The truncation error `E_z(n) = Λ(|n|) - Λ_z(n)` of the von Mangoldt function. -/
noncomputable def vonMangoldtTruncationError (z : ℝ) (n : ℤ) : ℝ :=
  evenVonMangoldt n - truncatedVonMangoldt z n

/-- The defining formula of the truncation error. -/
theorem vonMangoldtTruncationError_def (z : ℝ) (n : ℤ) :
    vonMangoldtTruncationError z n = evenVonMangoldt n - truncatedVonMangoldt z n :=
  (rfl)

/-- The truncation error is even. -/
@[simp]
theorem vonMangoldtTruncationError_neg (z : ℝ) (n : ℤ) :
    vonMangoldtTruncationError z (-n) = vonMangoldtTruncationError z n := by
  rw [vonMangoldtTruncationError_def, vonMangoldtTruncationError_def, evenVonMangoldt_neg,
    truncatedVonMangoldt_neg]

/-- At `n = 0` the truncation error is `∑_{1 ≤ d ≤ z} μ(d) log d`. -/
theorem vonMangoldtTruncationError_apply_zero (z : ℝ) :
    vonMangoldtTruncationError z 0 = ∑ d ∈ Ioc 0 ⌊z⌋₊, (μ d : ℝ) * Real.log d := by
  rw [vonMangoldtTruncationError_def, evenVonMangoldt_zero, truncatedVonMangoldt_apply_zero,
    zero_sub, neg_neg]

/-- For `n ≠ 0` the truncation error is the part of the Möbius sum with `d > z`:
`E_z(n) = -∑_{d ∣ |n|, d > z} μ(d) log d`. -/
theorem vonMangoldtTruncationError_eq_neg_sum_divisors (z : ℝ) (hn : n ≠ 0) :
    vonMangoldtTruncationError z n =
      -∑ d ∈ n.natAbs.divisors with z < ((d : ℕ) : ℝ), (μ d : ℝ) * Real.log d := by
  have hsum := sum_moebius_mul_log_eq (n := n.natAbs)
  simp only [log_apply] at hsum
  rw [← sum_filter_add_sum_filter_not n.natAbs.divisors (fun d : ℕ ↦ (d : ℝ) ≤ z)] at hsum
  simp only [not_le] at hsum
  rw [vonMangoldtTruncationError_def, truncatedVonMangoldt_eq_neg_sum_divisors z hn,
    evenVonMangoldt_def]
  linarith

/-- For `n ≠ 0` and `|n| ≤ z` there is no truncation error. -/
theorem vonMangoldtTruncationError_eq_zero_of_natAbs_le (hn : n ≠ 0) (hz : (n.natAbs : ℝ) ≤ z) :
    vonMangoldtTruncationError z n = 0 := by
  rw [vonMangoldtTruncationError_def, truncatedVonMangoldt_eq_evenVonMangoldt_of_natAbs_le hn hz,
    sub_self]

/-- At a prime `p` of `ℤ` with `|p| > z`, the truncation error is `log |p|`, written
`Real.log p`. -/
theorem vonMangoldtTruncationError_apply_prime_eq_log_of_lt {p : ℤ} (hp : Prime p)
    (hz : z < p.natAbs) : vonMangoldtTruncationError z p = Real.log p := by
  rw [vonMangoldtTruncationError_def, truncatedVonMangoldt_apply_prime_eq_zero_of_lt hp hz,
    sub_zero, evenVonMangoldt_apply_prime hp]

/-! ### Examples -/

/-- The prime evaluations at a natural prime `p ≤ z`. -/
example {p : ℕ} (hp : p.Prime) (hz : (p : ℝ) ≤ z) : truncatedVonMangoldt z p = Real.log p := by
  simpa using truncatedVonMangoldt_apply_prime_eq_log_of_le (Nat.prime_iff_prime_int.1 hp)
    (by simpa using hz)

/-- The prime evaluations at a natural prime `p > z`. -/
example {p : ℕ} (hp : p.Prime) (hz : z < p) :
    truncatedVonMangoldt z p = 0 ∧ vonMangoldtTruncationError z p = Real.log p := by
  have hp' := Nat.prime_iff_prime_int.1 hp
  exact ⟨truncatedVonMangoldt_apply_prime_eq_zero_of_lt hp' (by simpa using hz),
    by simpa using vonMangoldtTruncationError_apply_prime_eq_log_of_lt hp' (by simpa using hz)⟩

example (n : ℤ) : truncatedVonMangoldt 1 n = 0 :=
  truncatedVonMangoldt_eq_zero_of_lt_two one_lt_two n

example : truncatedVonMangoldt 2 0 = Real.log 2 := by
  rw [truncatedVonMangoldt_apply_zero, Nat.floor_ofNat]
  simp [sum_Ioc_succ_top, moebius_apply_prime Nat.prime_two]

example : vonMangoldtTruncationError 2 0 = -Real.log 2 := by
  rw [vonMangoldtTruncationError_apply_zero, Nat.floor_ofNat]
  simp [sum_Ioc_succ_top, moebius_apply_prime Nat.prime_two]

end TauCeti
