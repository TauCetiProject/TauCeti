/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AbsoluteRamificationIndex

/-!
# Factorial valuations in mixed-characteristic local fields

Let `K` be a finite extension of `ℚ_[p]`, and write `e` for its absolute ramification index.
The normalized valuation on `K` restricts to `e` times the normalized valuation on `ℚ_[p]`.
Consequently the valuation in `K` of a natural number `n` is

`e * padicValNat p n`.

Applying Legendre's formula gives the exact valuation of `n !` and the strict estimate

`(p - 1) * v_K(n !) < e * n`

for positive `n`.  If a depth `i` satisfies `(p - 1) * i > e`, this implies
`v_K(n !) < n * i`.  This is the coefficient estimate used to construct the exponential on
deep units: for an element of valuation at least `i`, the `n`-th term `x ^ n / n !` has positive
valuation, with a margin that grows linearly in `n`.

## Main results

* `TauCeti.sub_one_mul_natCastValuation_factorial`: Legendre's formula after base change.
* `TauCeti.sub_one_mul_natCastValuation_factorial_lt_of_ne_zero`: the strict factorial estimate.
* `TauCeti.natCastValuation_factorial_lt_mul_of_absoluteRamificationIndex_lt_of_ne_zero`: the
  estimate at a depth in the exponential's convergence range.

## References

* J.-P. Serre, *Local Fields*, Chapter II, §5.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section
noncomputable section

open ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable (K : Type*) [Field K]
variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable (p : ℕ) [Fact p.Prime] [FinitePadicExtension K p]

/-- Legendre's formula for the normalized valuation of a factorial in a finite extension of
`ℚ_[p]`. -/
theorem sub_one_mul_natCastValuation_factorial (n : ℕ) :
    (p - 1) * natCastValuation K n.factorial
        (by
          simpa only [map_natCast] using
            (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
              (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) :
                (n.factorial : ℚ_[p]) ≠ 0)) =
      absoluteRamificationIndex K p * (n - (p.digits n).sum) := by
  rw [natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p n.factorial
    (Nat.factorial_ne_zero n), ← Nat.mul_assoc, Nat.mul_comm (p - 1), Nat.mul_assoc,
    sub_one_mul_padicValNat_factorial]

/-- The normalized valuation of `n !` satisfies the strict Legendre bound after base change to a
finite extension of `ℚ_[p]`. -/
theorem sub_one_mul_natCastValuation_factorial_lt_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * natCastValuation K n.factorial
        (by
          simpa only [map_natCast] using
            (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
              (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) :
                (n.factorial : ℚ_[p]) ≠ 0)) <
      absoluteRamificationIndex K p * n := by
  rw [natCastValuation_eq_absoluteRamificationIndex_mul_padicValNat K p n.factorial
    (Nat.factorial_ne_zero n), ← Nat.mul_assoc, Nat.mul_comm (p - 1), Nat.mul_assoc]
  exact Nat.mul_lt_mul_of_pos_left
    (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
    (absoluteRamificationIndex_pos K p)

/-- At every depth `i` in the exponential convergence range `(p - 1) * i > e`, the valuation of
`n !` is strictly smaller than `n * i` for positive `n`. -/
theorem natCastValuation_factorial_lt_mul_of_absoluteRamificationIndex_lt_of_ne_zero
    {i n : ℕ} (hi : absoluteRamificationIndex K p < (p - 1) * i) (hn : n ≠ 0) :
    natCastValuation K n.factorial
        (by
          simpa only [map_natCast] using
            (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
              (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) :
                (n.factorial : ℚ_[p]) ≠ 0)) < n * i := by
  have hp : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  apply (Nat.mul_lt_mul_left hp).mp
  calc
    (p - 1) * natCastValuation K n.factorial
          (by
            simpa only [map_natCast] using
              (map_ne_zero_iff (algebraMap ℚ_[p] K) (algebraMap ℚ_[p] K).injective).mpr
                (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n) :
                  (n.factorial : ℚ_[p]) ≠ 0))
        < absoluteRamificationIndex K p * n :=
      sub_one_mul_natCastValuation_factorial_lt_of_ne_zero K p hn
    _ < ((p - 1) * i) * n := Nat.mul_lt_mul_of_pos_right hi (Nat.pos_of_ne_zero hn)
    _ = (p - 1) * (n * i) := by ac_rfl

end TauCeti
