/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Dvd
public import Mathlib.Data.Nat.Choose.Sum

/-!
# Binomial coefficients of a prime divided by the prime

For a prime `p` and `0 < i < p`, the prime `p` divides `p.choose i`. Weighting the quotients
`p.choose i / p` by `i` or by `p - i` gives the binomial coefficients of `p - 1`, so the
corresponding weighted sums of the terms of `(a + c) ^ p` are binomial expansions of
`(a + c) ^ (p - 1)` with one endpoint term removed.

## Main results

* `Nat.Prime.choose_div_mul_eq`: if `p * m = p.choose i * t` with `0 < i < p`, then
  `p.choose i / p * t = m`.
* `Nat.Prime.sum_choose_div_mul_left`: `∑_{0 < i < p} (p.choose i / p * i) a ^ (i - 1) c ^ (p - i)`
  is `(a + c) ^ (p - 1) - a ^ (p - 1)`.
* `Nat.Prime.sum_choose_div_mul_right`:
  `∑_{0 < i < p} (p.choose i / p * (p - i)) a ^ i c ^ (p - i - 1)` is
  `(a + c) ^ (p - 1) - c ^ (p - 1)`.
-/

public section

namespace Nat.Prime

variable {p : ℕ}

/-- If `p` is prime, `0 < i < p` and `p * m = p.choose i * t`, then `p.choose i / p * t = m`. -/
theorem choose_div_mul_eq (hp : p.Prime) {i m t : ℕ} (hi : i ∈ Finset.Ioo 0 p)
    (h : p * m = p.choose i * t) : p.choose i / p * t = m := by
  obtain ⟨u, hu⟩ := hp.dvd_choose_self (Finset.mem_Ioo.mp hi).1.ne' (Finset.mem_Ioo.mp hi).2
  rw [hu, Nat.mul_div_cancel_left _ hp.pos]
  rw [hu, mul_assoc] at h
  exact (Nat.eq_of_mul_eq_mul_left hp.pos h).symm

/-- For a prime `p`, `∑_{0 < i < p} (p.choose i / p * i) a ^ (i - 1) c ^ (p - i)` is
`(a + c) ^ (p - 1) - a ^ (p - 1)`. -/
theorem sum_choose_div_mul_left (hp : p.Prime) {R : Type*} [CommRing R] (a c : R) :
    ∑ i ∈ Finset.Ioo 0 p, ((p.choose i / p * i : ℕ) : R) * (a ^ (i - 1) * c ^ (p - i)) =
      (a + c) ^ (p - 1) - a ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_le).symm⟩
  rw [← Finset.Ico_add_one_left_eq_Ioo, ← Finset.sum_Ico_add', ← Finset.range_eq_Ico,
    add_pow, Finset.sum_range_succ, eq_sub_iff_add_eq]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one, mul_one,
    add_left_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j + 1 ∈ Finset.Ioo 0 (q + 1) := by simp at hj ⊢; omega
  rw [hp.choose_div_mul_eq hj' (Nat.add_one_mul_choose_eq q j), Nat.add_sub_add_right]
  ring

/-- For a prime `p`, `∑_{0 < i < p} (p.choose i / p * (p - i)) a ^ i c ^ (p - i - 1)` is
`(a + c) ^ (p - 1) - c ^ (p - 1)`. -/
theorem sum_choose_div_mul_right (hp : p.Prime) {R : Type*} [CommRing R] (a c : R) :
    ∑ i ∈ Finset.Ioo 0 p, ((p.choose i / p * (p - i) : ℕ) : R) * (a ^ i * c ^ (p - i - 1)) =
      (a + c) ^ (p - 1) - c ^ (p - 1) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, (Nat.sub_add_cancel hp.one_le).symm⟩
  rw [← Finset.Ico_add_one_left_eq_Ioo, ← Finset.sum_Ico_add', ← Finset.range_eq_Ico,
    add_pow, Finset.sum_range_succ', eq_sub_iff_add_eq]
  simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero, Nat.choose_zero_right, Nat.cast_one,
    one_mul, mul_one, add_left_inj]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j + 1 ∈ Finset.Ioo 0 (q + 1) := by simp at hj ⊢; omega
  rw [hp.choose_div_mul_eq hj' ((mul_comm _ _).trans (Nat.choose_mul_succ_eq q (j + 1))),
    Nat.add_sub_add_right, Nat.sub_sub]
  ring

end Nat.Prime
