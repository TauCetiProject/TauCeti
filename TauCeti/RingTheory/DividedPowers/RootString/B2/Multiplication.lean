/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.B2.Basic

/-!
# Multiplication coefficients for positive type-B₂ monomials

For the positive Chevalley relations `[x,y] = z`, `[x,z] = 2w`, with the other
brackets zero, this file computes the product of two ordered monomials
`y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ x⁽ᵈ⁾`. The coefficients are explicit natural numbers, so the
formula gives integral multiplication without inverting the structure constant two.
No linear independence of the root vectors or their ordered monomials is assumed.

The formula reuses `B2.dividedPower_mul_orderedMonomial` to move the first
monomial's last factor through the second monomial. The remaining three factors
commute, and their divided powers combine by the same-root binomial rule.
The two summation indices record the two nonsimple roots released while crossing
`y`, and the additional `w` factors released while crossing `z`, respectively.

This is an identity in an associative rational algebra. It does not interpret
factorial division over a positive-characteristic coefficient ring or assert an
integral PBW basis.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative.B2

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w : A}

private theorem prefix_mul_orderedMonomial
    (hyz : Commute y z) (hyw : Commute y w) (hzw : Commute z w)
    (a b c e f g h : ℕ) :
    (dividedPower a y * dividedPower b z * dividedPower c w) *
        orderedMonomial x y z w e f g h =
      (Nat.choose (a + e) a * Nat.choose (b + f) b * Nat.choose (c + g) c) •
        orderedMonomial x y z w (a + e) (b + f) (c + g) h := by
  have hzy := commute_dividedPower_dividedPower hyz.symm b e
  have hwy := commute_dividedPower_dividedPower hyw.symm c e
  have hwz := commute_dividedPower_dividedPower hzw.symm c f
  rw [orderedMonomial_def]
  simp only [mul_assoc]
  rw [hwy.left_comm, hzy.left_comm, hwz.left_comm,
    ← mul_assoc (dividedPower a y), mul_dividedPower,
    ← mul_assoc (dividedPower b z), mul_dividedPower,
    ← mul_assoc (dividedPower c w), mul_dividedPower]
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, orderedMonomial_def, mul_assoc]
  congr 1
  ac_rfl

/-- **Explicit integral multiplication in the positive type-B₂ algebra.**
The five coefficients from short-root insertion are multiplied by the three binomial
coefficients that combine the commuting `y`, `z`, and `w` factors. The four displayed
relations imply the other two commutation relations, so no additional hypotheses on
`y,w` or `z,w` are needed. -/
theorem orderedMonomial_mul_orderedMonomial
    (hxy : x * y = y * x + z) (hxz : x * z = z * x + 2 • w)
    (hxw : Commute x w) (hyz : Commute y z)
    (a b c d e f g h : ℕ) :
    orderedMonomial x y z w a b c d * orderedMonomial x y z w e f g h =
      ∑ p ∈ chainLeTwoIndex d e,
        ∑ k ∈ range (min (d - p.1 - 2 * p.2) f + 1),
          ((2 ^ k * Nat.choose (p.1 + (f - k)) p.1 *
            Nat.choose (p.2 + k) p.2 * Nat.choose (p.2 + k + g) (p.2 + k) *
            Nat.choose (d - p.1 - 2 * p.2 - k + h) (d - p.1 - 2 * p.2 - k)) *
            (Nat.choose (a + (e - p.1 - p.2)) a *
              Nat.choose (b + (p.1 + (f - k))) b * Nat.choose (c + (p.2 + k + g)) c)) •
          orderedMonomial x y z w (a + (e - p.1 - p.2)) (b + (p.1 + (f - k)))
            (c + (p.2 + k + g)) (d - p.1 - 2 * p.2 - k + h) := by
  classical
  have hxzQ : x * z = z * x + (2 : ℚ) • w := by
    simpa only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat] using hxz
  have hunit : IsUnit (2 : ℚ) := isUnit_iff_ne_zero.mpr (by norm_num)
  have hyw := hyz.of_commutator_eq_of_commutator_eq_smul_left hxy hxzQ hunit
  have hzw := hxw.of_commutator_eq_of_commutator_eq_smul hxy hxzQ hyz hunit
  -- Keep the first three factors together while collecting the last one.
  conv_lhs => rw [orderedMonomial_def x y z w a b c d]
  rw [mul_assoc, dividedPower_mul_orderedMonomial hxy hxz hxw hyz]
  simp only [mul_sum, mul_smul_comm]
  refine sum_congr rfl fun p _ => sum_congr rfl fun k _ => ?_
  rw [prefix_mul_orderedMonomial hyz hyw hzw, smul_smul]

end TauCeti.Associative.B2
