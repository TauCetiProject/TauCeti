/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.NormalOrdering

/-!
# Integral multiplication in a five-dimensional Heisenberg algebra

This file computes the product of two ordered divided-power monomials in two pairs of
root vectors sharing a central commutator direction. The pairs commute with each other,
while `v * y = y * v + k • s` and `w * z = z * w + l • s`, for integers `k, l`.
The order is `y, v, z, w, s`. The multiplication coefficients are integers, including
when either commutator constant is not a unit.

For the positive type-G₂ root vectors, take `y, v, z, w, s` at the roots
`β, 3α + β, α + β, 2α + β, 3α + 2β`, with `α` short. Under the normalization
of `TauCeti.RingTheory.DividedPowers.RootString.G2.Basic`, namely
`y * v = v * y + s` and `w * z = z * w + 3 • s`, we have `k = -1` and `l = 3`.
In general their values are `k = ±1` and `l = ±3`, depending on the root-vector signs.
These five roots form a parabolic nilradical. Their multiplication table
is the tail calculation needed when collecting the short simple-root factor in the
six-root positive algebra. The result is an identity in a rational algebra with
integral coefficients, not a definition by factorial division in positive characteristic.

## Main result

* `TauCeti.Associative.dividedPower_quintuple_mul_of_central_commutators`:
  the explicit finite double sum for arbitrary ordered monomial products.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

/-- Multiply two ordered divided-power monomials in two commuting pairs with a common
central commutator direction. All coefficients are integral; neither commutator constant
needs to be invertible. No linear independence or nilpotence assumption is required. -/
theorem dividedPower_quintuple_mul_of_central_commutators {y v z w s : A} {k l : ℤ}
    (hvy : v * y = y * v + k • s) (hwz : w * z = z * w + l • s)
    (hyz : Commute y z) (hyw : Commute y w) (hvz : Commute v z) (hvw : Commute v w)
    (hys : Commute y s) (hvs : Commute v s) (hzs : Commute z s) (hws : Commute w s)
    (a b c d e a' b' c' d' e' : ℕ) :
    (dividedPower a y * dividedPower b v * dividedPower c z * dividedPower d w *
        dividedPower e s) *
      (dividedPower a' y * dividedPower b' v * dividedPower c' z * dividedPower d' w *
        dividedPower e' s) =
      ∑ i ∈ range (min b a' + 1), ∑ j ∈ range (min d c' + 1),
        (k ^ i * l ^ j *
          ((a + (a' - i)).choose a : ℤ) * ((b - i + b').choose (b - i) : ℤ) *
          ((c + (c' - j)).choose c : ℤ) * ((d - j + d').choose (d - j) : ℤ) *
          ((j + e).choose j : ℤ) * ((i + j + e).choose i : ℤ) *
          ((i + j + e + e').choose (i + j + e) : ℤ)) •
        (dividedPower (a + (a' - i)) y * dividedPower (b - i + b') v *
          dividedPower (c + (c' - j)) z * dividedPower (d - j + d') w *
          dividedPower (i + j + e + e') s) := by
  have hfirst := dividedPower_mul_dividedPower_of_commutator_eq hvy
    (hvs.smul_right k) (hys.smul_right k) b a'
  have hsecond := dividedPower_mul_dividedPower_of_commutator_eq hwz
    (hws.smul_right l) (hzs.smul_right l) d c'
  have hsv (r t : ℕ) := (commute_dividedPower_dividedPower hvs.symm r t).left_comm
  have hsz (r t : ℕ) := (commute_dividedPower_dividedPower hzs.symm r t).left_comm
  have hsw (r t : ℕ) := (commute_dividedPower_dividedPower hws.symm r t).left_comm
  have hmerge (u : A) (m n : ℕ) (t : A) :
      dividedPower m u * (dividedPower n u * t) =
        ((m + n).choose m : ℤ) • (dividedPower (m + n) u * t) := by
    rw [← mul_assoc, mul_dividedPower, smul_mul_assoc, Nat.cast_smul_eq_nsmul]
  -- Separate the two commuting pairs before straightening either one.
  calc
    _ = (dividedPower a y * (dividedPower b v * dividedPower a' y) * dividedPower b' v) *
        (dividedPower c z * (dividedPower d w * dividedPower c' z) * dividedPower d' w) *
        (dividedPower e s * dividedPower e' s) := by
      simp only [mul_assoc,
        (commute_dividedPower_dividedPower hys.symm e a').left_comm,
        (commute_dividedPower_dividedPower hvs.symm e b').left_comm,
        (commute_dividedPower_dividedPower hzs.symm e c').left_comm,
        (commute_dividedPower_dividedPower hws.symm e d').left_comm,
        (commute_dividedPower_dividedPower hyw.symm d a').left_comm,
        (commute_dividedPower_dividedPower hyz.symm c a').left_comm,
        (commute_dividedPower_dividedPower hvw.symm d b').left_comm,
        (commute_dividedPower_dividedPower hvz.symm c b').left_comm]
    _ = _ := by
      rw [hfirst, hsecond]
      simp only [mul_sum, sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
      -- Move the two released central powers to the right, then merge equal-root factors.
      simp only [dividedPower_zsmul, mul_smul_comm, smul_mul_assoc, smul_smul,
        mul_assoc, hsv, hsz, hsw]
      simp only [hmerge, mul_smul_comm, smul_smul]
      rw [mul_dividedPower]
      simp only [← Nat.cast_smul_eq_nsmul ℤ, mul_smul_comm, smul_smul, add_assoc]
      congr 1
      ring

end TauCeti.Associative
