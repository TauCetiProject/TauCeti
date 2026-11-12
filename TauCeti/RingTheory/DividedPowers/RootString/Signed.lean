/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.Basic

/-!
# Integral coefficients for signed length-two root strings

For root vectors `x`, `y`, `z`, `w` in the directions `α`, `β`, `α + β`, `2α + β`,
suppose `[x,y] = c z` and `[x,[x,y]] = 2 d w`, with integer constants `c`, `d`.
The coefficient of `y⁽ⁿ⁻ᵇ⁻ᵏ⁾ z⁽ᵇ⁾ w⁽ᵏ⁾ x⁽ᵐ⁻ᵇ⁻²ᵏ⁾` in the straightening of
`x⁽ᵐ⁾ y⁽ⁿ⁾` is `c^b d^k`.

This makes the signs and integer coefficients explicit in the length-two Chevalley
straightening rule. The construction uses the coefficient-one identity
`TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq_two_nsmul`
with root vectors `c z` and `d w`, followed by integer homogeneity of divided powers.
Neither constant is inverted, and neither needs to be a unit or nonzero. The identities
are in a rational algebra; using them after specialization requires an integral form,
not factorial division in positive characteristic.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z w : A} {c d : ℤ}

/-- **Signed integral straightening for a length-two root string.** If `[x,y] = c z`
and `[x,[x,y]] = 2 d w`, with `x` commuting with `w` and `y` commuting with `z`,
then the coefficient of the term with `z`-degree `b` and `w`-degree `k` is `c^b d^k`.
The second commutator is specified directly, so no division by `c` is required. -/
theorem dividedPower_mul_dividedPower_of_commutator_eq_of_iterated_commutator_eq
    (hxy : x * y = y * x + c • z)
    (hxxy : x * (x * y - y * x) = (x * y - y * x) * x + (2 * d) • w)
    (hxw : Commute x w) (hyz : Commute y z) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ chainLeTwoIndex m n,
        (c ^ p.1 * d ^ p.2) •
          (dividedPower (n - p.1 - p.2) y * dividedPower p.1 z *
            dividedPower p.2 w * dividedPower (m - p.1 - 2 * p.2) x) := by
  have hxz : x * (c • z) = (c • z) * x + 2 • (d • w) := by
    simpa only [hxy, add_sub_cancel_left, two_mul, add_smul, two_smul] using hxxy
  rw [dividedPower_mul_dividedPower_of_commutator_eq_two_nsmul hxy hxz
    (hxw.smul_right d) (hyz.smul_right c)]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc, smul_smul,
    mul_comm (d ^ p.2) (c ^ p.1)]

end TauCeti.Associative
