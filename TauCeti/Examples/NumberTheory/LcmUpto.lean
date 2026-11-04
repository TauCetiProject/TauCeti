/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LcmUpto
import Mathlib.Data.ZMod.Basic

/-!
# Examples of `Nat.lcmUpto` and powersmoothness

Concrete computations for `Nat.lcmUpto`:

* `Nat.lcmUpto 0 = Nat.lcmUpto 1 = 1` and `Nat.lcmUpto 10 = 2520 = 2 ^ 3 * 3 ^ 2 * 5 * 7`.
* Prime-divisor smoothness (`16 ∈ Nat.smoothNumbers 11`) is strictly weaker than
  `10`-powersmoothness (`¬ 16 ∣ Nat.lcmUpto 10`), whereas squarefree `11`-smooth integers such as
  `30` divide both `primorial 10` and `Nat.lcmUpto 10`.
* Step behavior across `7, 8, 9, 10`: `Nat.lcmUpto` jumps by `2` at `8 = 2 ^ 3` and by `3` at
  `9 = 3 ^ 2`, then stays constant at `10`.
* In `ZMod 12` every element is annihilated by `(10 : ℕ).lcmUpto`, whereas `(1 : ZMod 16)` of
  additive order `16` is not.
-/

public section

-- Small bounds and the prime-power decomposition M(10) = 2520 = 8 * 9 * 5 * 7.
example : Nat.lcmUpto 0 = 1 ∧ Nat.lcmUpto 1 = 1 :=
  ⟨Nat.lcmUpto_zero, Nat.lcmUpto_one⟩

example : Nat.lcmUpto 10 = 2520 ∧ 2520 = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
  decide

-- Prime-power divisibility cuts off between 2^3 = 8 ≤ 10 and 2^4 = 16 > 10.
example : 2 ^ 3 ∣ Nat.lcmUpto 10 ∧ ¬ 2 ^ 4 ∣ Nat.lcmUpto 10 := by
  rw [Nat.prime_two.pow_dvd_lcmUpto_iff (by decide),
    Nat.prime_two.pow_dvd_lcmUpto_iff (by decide)]
  omega

-- 16 has all prime divisors at most 10, yet does not divide M(10) = 2520.
example : 16 ∈ Nat.smoothNumbers 11 ∧ ¬ 16 ∣ Nat.lcmUpto 10 := by
  refine ⟨?_, ?_⟩
  · have h2 : 2 ∈ Nat.smoothNumbers 11 := Nat.mem_smoothNumbers_of_lt (by decide) (by decide)
    exact Nat.mul_mem_smoothNumbers (Nat.mul_mem_smoothNumbers h2 h2)
      (Nat.mul_mem_smoothNumbers h2 h2)
  · have h16 : IsPrimePow (16 : ℕ) :=
      Nat.prime_two.prime.isPrimePow.pow (k := 4) (by decide)
    rw [h16.dvd_lcmUpto_iff]
    omega

-- For squarefree numbers, 11-smoothness and divisibility of M(10) (or 10#) agree.
example : 30 ∣ Nat.lcmUpto 10 ∧ 30 ∣ primorial 10 := by
  have hsq : Squarefree (30 : ℕ) := by
    rintro d hd
    have hle : d * d ≤ 30 := Nat.le_of_dvd (by decide) hd
    have hd5 : d ≤ 5 := by nlinarith
    interval_cases d <;> simp_all
  have hsm : 30 ∈ Nat.smoothNumbers 11 := by
    have h2 : 2 ∈ Nat.smoothNumbers 11 := Nat.mem_smoothNumbers_of_lt (by decide) (by decide)
    have h3 : 3 ∈ Nat.smoothNumbers 11 := Nat.mem_smoothNumbers_of_lt (by decide) (by decide)
    have h5 : 5 ∈ Nat.smoothNumbers 11 := Nat.mem_smoothNumbers_of_lt (by decide) (by decide)
    exact Nat.mul_mem_smoothNumbers (Nat.mul_mem_smoothNumbers h2 h3) h5
  exact ⟨hsq.dvd_lcmUpto_iff_mem_smoothNumbers_succ.mpr hsm, hsq.dvd_primorial_iff.mpr hsm⟩

-- lcmUpto jumps at prime powers (8 = 2^3, 9 = 3^2) and is stationary at 10.
example : Nat.lcmUpto 8 = 2 * Nat.lcmUpto 7 ∧
    Nat.lcmUpto 9 = 3 * Nat.lcmUpto 8 ∧
    Nat.lcmUpto 10 = Nat.lcmUpto 9 := by
  refine ⟨Nat.prime_two.lcmUpto_pow (k := 3) (by decide),
    Nat.prime_three.lcmUpto_pow (k := 2) (by decide),
    Nat.lcmUpto_succ_of_not_isPrimePow (n := 9) ?_⟩
  intro h10
  obtain ⟨p, k, hp, _, hpk⟩ := (isPrimePow_nat_iff 10).mp h10
  have hp2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (by rw [hpk]; decide)
  have hp5 : 5 ∣ p := (by decide : Nat.Prime 5).dvd_of_dvd_pow (by rw [hpk]; decide)
  have h2eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hp2
  have h5eq := (Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) hp).mp hp5
  omega

-- Every element of ZMod 12 is annihilated by M(10), because the prime-power divisors of 12
-- (namely 2, 4, 3) are all at most 10.
example (x : ZMod 12) : (10 : ℕ).lcmUpto • x = 0 := by
  apply TauCeti.lcmUpto_nsmul_eq_zero_of_isPrimePow_dvd_card_le
  rw [Nat.card_zmod 12]
  intro q hq hq12
  have hle : q ≤ 12 := Nat.le_of_dvd (by decide) hq12
  rcases eq_or_ne q 12 with rfl | hne12
  · obtain ⟨p, k, hp, _, hpk⟩ := (isPrimePow_nat_iff 12).mp hq
    have hp2 : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow (by rw [hpk]; decide)
    have hp3 : 3 ∣ p := Nat.prime_three.dvd_of_dvd_pow (by rw [hpk]; decide)
    have h2eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hp2
    have h3eq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hp3
    omega
  · rcases eq_or_ne q 11 with rfl | hne11
    · exact absurd hq12 (by decide)
    · omega

-- Conversely, 1 ∈ ZMod 16 has additive order 16 > 10, so M(10) does not annihilate it.
example : (10 : ℕ).lcmUpto • (1 : ZMod 16) ≠ 0 := by
  rw [Ne, TauCeti.lcmUpto_nsmul_eq_zero_iff]
  intro h
  have h16 : IsPrimePow (16 : ℕ) :=
    Nat.prime_two.prime.isPrimePow.pow (k := 4) (by decide)
  rw [ZMod.addOrderOf_one 16] at h
  exact absurd (h 16 h16 dvd_rfl) (by omega)
