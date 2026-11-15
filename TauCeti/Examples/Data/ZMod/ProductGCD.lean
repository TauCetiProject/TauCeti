/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Data.ZMod.ProductGCD

/-!
# Examples of product gcds

These examples distinguish a proper product gcd, a product that hides proper leaf gcds,
and a zero leaf that gives no proper factor. Empty products, modulus one, prime powers, and
negative integers at modulus zero exercise the boundary cases of the product-gcd API.
-/

namespace TauCeti

-- The product is zero modulo 15 although both leaf gcds are proper.
example : Nat.gcd ([3, 5] : List (ZMod 15)).prod.val 15 = 15 ∧
    Nat.gcd (3 : ZMod 15).val 15 = 3 ∧ Nat.gcd (5 : ZMod 15).val 15 = 5 := by
  decide

-- Prime divisibility can be checked at the leaves instead of multiplying them.
example : 5 ∣ Nat.gcd ([1, 5] : List (ZMod 15)).prod.val 15 := by
  apply (List.prime_dvd_gcd_val_prod_iff _ (by decide)).mpr
  decide

-- A prime present in one leaf and a prime absent from all leaves certify properness.
example : 1 < Nat.gcd ([1, 5] : List (ZMod 15)).prod.val 15 ∧
    Nat.gcd ([1, 5] : List (ZMod 15)).prod.val 15 < 15 := by
  apply List.one_lt_gcd_val_prod_and_lt (p := 5) (q := 3) <;>
    decide

-- A single zero leaf gives the whole modulus, not a proper factor.
example : Nat.gcd ([0] : List (ZMod 15)).prod.val 15 = 15 ∧
    ¬∃ t ∈ ([0] : List (ZMod 15)), 1 < Nat.gcd t.val 15 ∧ Nat.gcd t.val 15 < 15 := by
  decide

-- The empty product gcd has no prime divisor, even one not dividing the modulus.
example {n p : ℕ} (hp : p.Prime) :
    ¬p ∣ Nat.gcd ([] : List (ZMod n)).prod.val n := by
  rw [List.prime_dvd_gcd_val_prod_iff _ hp]
  simp

-- Modulus one is harmless even though its empty product is zero as a residue.
example : Nat.gcd ([] : List (ZMod 1)).prod.val 1 = 1 := by
  rw [List.gcd_val_prod]
  decide

-- Two leaves can supply distinct copies of the same prime: the criterion does not claim
-- to detect multiplicities, and the product gcd need not equal any leaf gcd.
example : Nat.gcd ([3, 3] : List (ZMod 9)).prod.val 9 = 9 ∧
    ∀ t ∈ ([3, 3] : List (ZMod 9)), Nat.gcd t.val 9 = 3 := by
  decide

-- Reduction before multiplication preserves the gcd, not the product of representatives.
example : Nat.gcd ([8, 8] : List (ZMod 15)).prod.val 15 = Nat.gcd (8 * 8) 15 := by
  exact (List.gcd_val_prod ([8, 8] : List (ZMod 15))).trans (by decide)

-- At modulus zero the representatives are absolute values, including for negative leaves.
example : Nat.gcd ([-3, 5] : List (ZMod 0)).prod.val 0 = 15 := by
  rw [List.gcd_val_prod]
  decide

end TauCeti
