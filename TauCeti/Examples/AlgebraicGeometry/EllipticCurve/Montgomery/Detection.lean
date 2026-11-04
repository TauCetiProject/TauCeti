/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Detection

/-!
# Examples of Montgomery stage-1 detection

The raw pair `(21, 25)` modulo `35` represents infinity modulo `5`, but not modulo `7`.
The distinguished point of order two over `ZMod 5` is annihilated by the multiplier `2`,
so stage-1 detection certifies a proper factor. The examples also separate the inconclusive
gcds `1` and `n` from proper factors, and record a proper gcd for a prime-power modulus,
which reduction modulo distinct primes cannot detect.
-/

public section

namespace TauCeti.Montgomery

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The reduced pair is genuinely nonzero and represents infinity.
example : (Pair.mk 21 25 : Pair (ZMod 35)).map
    (ZMod.castHom (by norm_num : 5 ∣ 35) (ZMod 5)) = ⟨1, 0⟩ := by
  ext <;> simp only [Pair.map_x, Pair.map_z] <;> decide

-- The point order, not just its prime factors, divides the multiplier.
example : 5 ∣ Nat.gcd (25 : ZMod 35).val 35 := by
  apply prime_dvd_gcd_of_addOrderOf_dvd (n := 35) (p := 5) (A := 0) (B := 1) (m := 2)
    (by decide) (twoTorsionPoint 0 (by decide)) ⟨21, 25⟩
  · simp
  · rw [two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide

-- Nonvanishing at 7 upgrades prime detection to a proper factor certificate.
example : 1 < Nat.gcd (25 : ZMod 35).val 35 ∧ Nat.gcd (25 : ZMod 35).val 35 < 35 := by
  refine one_lt_gcd_and_gcd_lt_of_addOrderOf_dvd
    (n := 35) (p := 5) (A := 0) (B := 1) (m := 2)
    (by decide) (twoTorsionPoint 0 (by decide)) ⟨21, 25⟩
    (by simp) ?_ (q := 7) (by decide) ?_
  · rw [two_nsmul, twoTorsionPoint_add_self, coordinates_zero, Pair.cross_def]
    simp only [Pair.map_x, Pair.map_z]
    decide
  · decide

-- The three gcd outcomes: no factor, a proper factor, and total annihilation.
example : Nat.gcd (1 : ZMod 35).val 35 = 1 ∧
    Nat.gcd (25 : ZMod 35).val 35 = 5 ∧ Nat.gcd (0 : ZMod 35).val 35 = 35 := by
  decide

-- Proper prime-power gcds do not require two distinct prime divisors.
example : Nat.gcd (3 : ZMod 9).val 9 = 3 ∧
    ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (3 : ZMod 9) =
      ZMod.castHom (by norm_num : 3 ∣ 9) (ZMod 3) (0 : ZMod 9) := by
  decide

-- The gcd/reduction bridge also includes modulus zero and negative integers.
example : 5 ∣ Nat.gcd (-15 : ZMod 0).val 0 := by
  rw [ZMod.dvd_gcd_val_iff_castHom_eq_zero _ (dvd_zero 5)]
  decide

end TauCeti.Montgomery
