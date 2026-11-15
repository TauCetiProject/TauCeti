/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Compatibility of the complex roots of unity `exp(2πi / m)`

Mathlib's `Complex.isPrimitiveRoot_exp` says that `exp(2πi / m)` is a primitive `m`-th root of
unity. This file records that these roots are compatible along the power maps: for `n ∣ m` with
`m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`.

## Main results

* `TauCeti.exp_two_pi_I_div_pow_div`: `exp(2πi / m) ^ (m / n) = exp(2πi / n)` for `n ∣ m`,
  `m ≠ 0`.
* `Complex.exp_two_pi_I_mul_div`: `exp(2πi k / n) = exp(2πi / n) ^ k`.
* `Complex.eq_of_exp_two_pi_I_mul_div_eq` and `Complex.nodup_map_exp_two_pi_I_mul_div`: injectivity
  of `e ↦ exp(2πi e / h)` on `{e : ℕ | e < h}` and duplicate-freeness of its multiset image.
-/

public section

open Complex Real

namespace TauCeti

/-- The complex numbers `exp(2πi / m)` are compatible along the power maps: for `n ∣ m` with
`m ≠ 0`, `exp(2πi / m) ^ (m / n) = exp(2πi / n)`. -/
theorem exp_two_pi_I_div_pow_div {m n : ℕ} (hm : m ≠ 0) (h : n ∣ m) :
    exp (2 * π * I / m) ^ (m / n) = exp (2 * π * I / n) := by
  obtain ⟨k, rfl⟩ := h
  have hn : n ≠ 0 := left_ne_zero_of_mul hm
  have hk : k ≠ 0 := right_ne_zero_of_mul hm
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn), ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

end TauCeti

namespace Complex

/-- For natural numbers `k` and `n`, `exp(2πi k / n)` is the `k`-th power of `exp(2πi / n)`. -/
theorem exp_two_pi_I_mul_div (k n : ℕ) :
    exp (2 * Real.pi * I * (k / n)) = exp (2 * Real.pi * I / n) ^ k := by
  rw [← exp_nat_mul]
  congr 1
  ring

/-- The map `e ↦ exp(2πi e / h)` is injective on `{e : ℕ | e < h}`. -/
theorem eq_of_exp_two_pi_I_mul_div_eq {a b h : ℕ} (ha : a < h) (hb : b < h)
    (hab : exp (2 * Real.pi * I * (a / h)) = exp (2 * Real.pi * I * (b / h))) : a = b := by
  rw [exp_two_pi_I_mul_div, exp_two_pi_I_mul_div] at hab
  exact (isPrimitiveRoot_exp h ((Nat.zero_le a).trans_lt ha).ne').pow_inj ha hb hab

/-- Mapping a duplicate-free multiset of natural numbers `< h` along `e ↦ exp(2πi e / h)` produces a
duplicate-free multiset. -/
theorem nodup_map_exp_two_pi_I_mul_div {s : Multiset ℕ} {h : ℕ} (hs : s.Nodup)
    (hlt : ∀ e ∈ s, e < h) :
    (s.map fun e : ℕ => exp (2 * Real.pi * I * (e / h))).Nodup :=
  hs.map_on fun _ ha _ hb => eq_of_exp_two_pi_I_mul_div_eq (hlt _ ha) (hlt _ hb)

end Complex
