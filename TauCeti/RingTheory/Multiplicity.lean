/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Multiplicity

/-!
# Divisibility of a power by a power of a prime

The multiplicity of a prime `p` in `x ^ n` is `n` times its multiplicity in `x`
(`emultiplicity_pow`). This file records the resulting divisibility statement: a bound on the
power of `p` dividing `x ^ n` gives a bound on the power of `p` dividing `x`.

## Main results

* `Prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow`: for a prime `p`, if `p ^ (n * k + 1)` divides
  `x ^ n` then `p ^ (k + 1)` divides `x`.
-/

public section

variable {α : Type*} [CommMonoidWithZero α] [IsCancelMulZero α]

/-- For a prime `p`, if `p ^ (n * k + 1)` divides `x ^ n` then `p ^ (k + 1)` divides `x`: the
multiplicity of `p` in `x ^ n` is `n` times that in `x`. -/
theorem Prime.pow_succ_dvd_of_pow_mul_add_one_dvd_pow {p x : α} (hp : Prime p) {n k : ℕ}
    (h : p ^ (n * k + 1) ∣ x ^ n) : p ^ (k + 1) ∣ x := by
  rw [pow_dvd_iff_le_emultiplicity, emultiplicity_pow hp] at h
  rw [pow_dvd_iff_le_emultiplicity]
  generalize emultiplicity p x = a at h ⊢
  induction a using ENat.recTopCoe with
  | top => exact le_top
  | coe m =>
    norm_cast at h ⊢
    exact Nat.lt_of_mul_lt_mul_left (a := n) (by omega)
