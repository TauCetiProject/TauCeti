/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LcmUpto

/-!
# Examples of `Nat.lcmUpto` and powersmoothness

Concrete computations for `Nat.lcmUpto`:

* `Nat.lcmUpto 0 = Nat.lcmUpto 1 = 1`, `Nat.lcmUpto 2 = 2`, and
  `Nat.lcmUpto 10 = 2520 = 2 ^ 3 * 3 ^ 2 * 5 * 7`.
* Prime-power divisibility cuts off between `2 ^ 3 = 8 ≤ 10` and `2 ^ 4 = 16 > 10`.
* Bounding only the prime divisors (`∀ p, p.Prime → p ∣ 16 → p ≤ 10`) is strictly weaker than
  `10`-powersmoothness (`¬ 16 ∣ Nat.lcmUpto 10`).
* Composite integers exceeding the bound still divide `Nat.lcmUpto 10` when each `p`-primary part
  `ordProj[p] d` is at most `10`, such as `12 = 4 * 3`.
-/

public section

-- Small bounds and the prime-power decomposition M(10) = 2520 = 8 * 9 * 5 * 7.
example : Nat.lcmUpto 0 = 1 ∧ Nat.lcmUpto 1 = 1 ∧ Nat.lcmUpto 2 = 2 :=
  ⟨Nat.lcmUpto_zero, Nat.lcmUpto_one, Nat.lcmUpto_two⟩

example : Nat.lcmUpto 10 = 2520 ∧ 2520 = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by
  decide

-- Prime-power divisibility cuts off between 2^3 = 8 ≤ 10 and 2^4 = 16 > 10.
example : 2 ^ 3 ∣ Nat.lcmUpto 10 ∧ ¬ 2 ^ 4 ∣ Nat.lcmUpto 10 := by
  rw [Nat.prime_two.pow_dvd_lcmUpto_iff (by decide),
    Nat.prime_two.pow_dvd_lcmUpto_iff (by decide)]
  omega

-- 16 has all prime divisors at most 10 (each dividing M(10)), yet does not divide M(10) = 2520.
example : (∀ p : ℕ, p.Prime → p ∣ 16 → p ≤ 10 ∧ p ∣ Nat.lcmUpto 10) ∧
    ¬ 16 ∣ Nat.lcmUpto 10 := by
  refine ⟨fun p hp hp16 ↦ ?_, ?_⟩
  · have h16 : (16 : ℕ) = 2 ^ 4 := by decide
    rw [h16] at hp16
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hp16)
    subst hp2
    exact ⟨by decide, Nat.prime_two.dvd_lcmUpto_iff.mpr (by decide)⟩
  · rw [(by decide : IsPrimePow 16).dvd_lcmUpto_iff]
    omega

-- 12 exceeds 10, yet divides M(10) because every prime-power divisor (and hence every p-primary
-- part ordProj[p] 12) is at most 10.
example : 12 ∣ Nat.lcmUpto 10 ∧ ∀ p : ℕ, p.Prime → p ∣ 12 → ordProj[p] 12 ≤ 10 := by
  have h12 : 12 ∣ Nat.lcmUpto 10 := by
    rw [Nat.dvd_lcmUpto_iff]
    intro q hq hq12
    have hle : q ≤ 12 := Nat.le_of_dvd (by decide) hq12
    have hne11 : q ≠ 11 := fun h ↦ (by decide : ¬ 11 ∣ 12) (h ▸ hq12)
    have hne12 : q ≠ 12 := fun h ↦ (by decide : ¬ IsPrimePow 12) (h ▸ hq)
    omega
  exact ⟨h12, (Nat.dvd_lcmUpto_iff_ordProj_le.mp h12).2⟩
