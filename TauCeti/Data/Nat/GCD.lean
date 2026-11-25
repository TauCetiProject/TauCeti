/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Data.Nat.GCD.Basic

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Coprimality, divisibility and nonzero least common multiples

Shifting an inner summand by `m` preserves coprimality with `m` (`Nat.coprime_add_self_add_right`).
For `q ≠ 0` and `N ≠ 0`, the natural numbers `q` and `q ^ N - 1` are coprime, because any common
divisor of `q` and `q ^ N - 1` also divides `q ^ N - (q ^ N - 1) = 1`. This is the coprimality
needed to view `q` as a unit of `ZMod (q ^ N - 1)`.

The least common multiple of two nonzero naturals is nonzero, also as a `NeZero` instance.

If a nonzero `m` does not divide some `b`, then `m ≠ 1`, so `2 ≤ m`. Conversely, if `b` is prime to
`m ≥ 2`, then `m ∤ b`, since a divisor of `b` prime to `b` is `1`.

If the products of two finite families of naturals are coprime and one entry of the first family is
zero, the second family is constantly `1`: a zero entry makes the first product `0`, and `0` is
coprime only to `1`.

## Main results

* `Nat.coprime_add_self_add_right`: shifting an inner summand by `m` preserves coprimality with `m`.
* `Nat.coprime_pow_sub_one`: `q` is coprime to `q ^ N - 1`.
* `Nat.neZero_lcm`: `NeZero (lcm m n)` for nonzero `m` and `n`.
* `Nat.Coprime.eq_one_of_exists_eq_zero`: coprime products and a zero entry in one family force the
  other family to be `1`.
* `Nat.gcd_mul_right_div_gcd`: `m.gcd (n * k) = m.gcd n * (m / m.gcd n).gcd k`.
* `Nat.two_le_of_not_dvd`: if a nonzero `m` does not divide `b`, then `2 ≤ m`.
* `Nat.Coprime.not_dvd_of_two_le`: if `b` is prime to `m ≥ 2`, then `m ∤ b`.
-/

public section

namespace Nat

/-- The least common multiple of two nonzero natural numbers is nonzero. -/
instance neZero_lcm (m n : ℕ) [NeZero m] [NeZero n] : NeZero (lcm m n) :=
  ⟨lcm_ne_zero (NeZero.ne m) (NeZero.ne n)⟩

/-- Shifting an inner summand by `m` preserves coprimality with `m`. -/
@[simp]
theorem coprime_add_self_add_right {m n k : ℕ} : Coprime m (n + m + k) ↔ Coprime m (n + k) := by
  rw [Nat.add_right_comm n m k, coprime_add_self_right]

/-- If `q ≠ 0` and `N ≠ 0`, then `q` is coprime to `q ^ N - 1`. -/
theorem coprime_pow_sub_one {q N : ℕ} (hq : q ≠ 0) (hN : N ≠ 0) : q.Coprime (q ^ N - 1) :=
  .of_dvd_left (dvd_pow_self q hN) <|
    (coprime_self_sub_right (one_le_pow N q (Nat.pos_of_ne_zero hq))).2 (coprime_one_right _)

/-- If the products of two finite families of naturals are coprime and some entry of the first
family is zero, then the second family is constantly `1`: a zero entry makes the first product
`0`, and `Nat.Coprime 0 m` holds only for `m = 1`. -/
theorem Coprime.eq_one_of_exists_eq_zero {ι : Type*} [Fintype ι] {x y : ι → ℕ}
    (hc : Nat.Coprime (∏ i, x i) (∏ i, y i)) (hx : ∃ i, x i = 0) : y = 1 := by
  obtain ⟨i, hi⟩ := hx
  have hx0 : (∏ i, x i) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  have hy1 : (∏ i, y i) = 1 := (Nat.coprime_zero_left _).mp (hx0 ▸ hc)
  exact funext fun j ↦ Nat.dvd_one.mp (hy1 ▸ Finset.dvd_prod_of_mem y (Finset.mem_univ j))

/-- Factoring `m.gcd n` out of `m.gcd (n * k)`: the remaining common divisor with `k` is the gcd
with `m / m.gcd n`. -/
theorem gcd_mul_right_div_gcd (m n k : ℕ) :
    m.gcd (n * k) = m.gcd n * (m / m.gcd n).gcd k := by
  rcases Nat.eq_zero_or_pos (m.gcd n) with hg0 | hg
  · obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hg0
    simp
  have hm : m.gcd n * (m / m.gcd n) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m n)
  have hn : m.gcd n * (n / m.gcd n) = n := Nat.mul_div_cancel' (Nat.gcd_dvd_right m n)
  have hcop : Nat.Coprime (n / m.gcd n) (m / m.gcd n) := (Nat.coprime_div_gcd_div_gcd hg).symm
  calc m.gcd (n * k)
      = (m.gcd n * (m / m.gcd n)).gcd (m.gcd n * ((n / m.gcd n) * k)) := by
          rw [hm, ← mul_assoc, hn]
    _ = m.gcd n * (m / m.gcd n).gcd ((n / m.gcd n) * k) :=
          Nat.gcd_mul_left (m.gcd n) (m / m.gcd n) ((n / m.gcd n) * k)
    _ = m.gcd n * (m / m.gcd n).gcd k := by
          rw [hcop.gcd_mul_left_cancel_right k]

/-- If a nonzero `m` does not divide `b`, then `2 ≤ m`. -/
theorem two_le_of_not_dvd {m b : ℕ} [NeZero m] (hb : ¬m ∣ b) : 2 ≤ m :=
  (Nat.two_le_iff m).2 ⟨NeZero.ne m, by rintro rfl; exact hb (one_dvd b)⟩

/-- If `b` is prime to `m ≥ 2`, then `m ∤ b`. -/
theorem Coprime.not_dvd_of_two_le {m b : ℕ} (hb : b.Coprime m) (hm : 2 ≤ m) : ¬m ∣ b :=
  fun h ↦ by have := (Nat.coprime_comm.mp hb).eq_one_of_dvd h; lia

end Nat
