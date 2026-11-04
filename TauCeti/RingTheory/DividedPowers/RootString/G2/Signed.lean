/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2.Basic

/-!
# Integral structure constants in G₂ straightening

The coefficient-one G₂ rule normalizes the four nonsimple root vectors. To use a specified
Chevalley basis instead, `dividedPower_mul_dividedPower_of_g2_zsmul` keeps the integer constants
in the four brackets visible. Its coefficients are products of integer powers, with no
inversion of a structure constant. In particular it tracks the sign of the highest-root term,
which comes from the bracket between the middle two root vectors, not just the simple-root
string.

The identity is in an associative rational algebra; specialization to other characteristics
requires an integral form containing the displayed divided powers.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

variable {A : Type*} [Ring A] [Algebra ℚ A] {x y z w v s : A}

/-- G₂ divided-power straightening with the four integer structure constants retained.
If the brackets of `(x,y)`, `(x,z)`, `(x,w)`, and `(w,z)` are respectively
`a • z`, `2 • (b • w)`, `3 • (c • v)`, and `3 • (d • s)`, and if `x` commutes with
`v` and `s`, `y` with `z`, `w` with `v`, and `s` with `z`, `w`, and `v`, then
`dividedPower m x * dividedPower n y` expands over `chainG2Index m n`. The coefficient
of the term with nonsimple-root exponents `(i,j,k,l)` is
`a^i (a*b)^j (a*b*c)^k (a^2*b*d)^l`.
The constants may be negative or zero; no independence or nilpotence is required. -/
theorem dividedPower_mul_dividedPower_of_g2_zsmul (a b c d : ℤ)
    (hxy : x * y = y * x + a • z) (hxz : x * z = z * x + 2 • (b • w))
    (hxw : x * w = w * x + 3 • (c • v)) (hwz : w * z = z * w + 3 • (d • s))
    (hxv : Commute x v) (hxs : Commute x s) (hyz : Commute y z) (hwv : Commute w v)
    (hzs : Commute z s) (hws : Commute w s) (hvs : Commute v s) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ chainG2Index m n,
        (a ^ p.1 * (a * b) ^ p.2.1 * (a * b * c) ^ p.2.2.1 *
          (a ^ 2 * b * d) ^ p.2.2.2) •
        (dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) y * dividedPower p.1 z *
          dividedPower p.2.1 w * dividedPower p.2.2.1 v * dividedPower p.2.2.2 s *
          dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) x) := by
  -- Apply dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul to rescaled vectors,
  -- using integer homogeneity of divided powers.
  have hxz' : x * (a • z) = (a • z) * x + 2 • ((a * b) • w) := by
    simp only [mul_smul_comm, smul_mul_assoc, hxz, smul_add,
      ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    congr 2
    ring
  have hxw' : x * ((a * b) • w) = ((a * b) • w) * x +
      3 • ((a * b * c) • v) := by
    simp only [mul_smul_comm, smul_mul_assoc, hxw, smul_add,
      ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    congr 2
    ring
  have hwz' : ((a * b) • w) * (a • z) = (a • z) * ((a * b) • w) +
      3 • ((a ^ 2 * b * d) • s) := by
    simp only [smul_mul_smul, hwz, smul_add, ← Nat.cast_smul_eq_nsmul ℤ, smul_smul]
    congr 2 <;> ring
  rw [dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul hxy hxz' hxw' hwz'
    (hxv.smul_right (a * b * c)) (hxs.smul_right (a ^ 2 * b * d)) (hyz.smul_right a)
    ((hwv.smul_left (a * b)).smul_right (a * b * c))
    ((hzs.smul_left a).smul_right (a ^ 2 * b * d))
    ((hws.smul_left (a * b)).smul_right (a ^ 2 * b * d))
    ((hvs.smul_left (a * b * c)).smul_right (a ^ 2 * b * d))]
  simp only [dividedPower_zsmul, smul_mul_assoc, mul_smul_comm, smul_smul]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  congr 1
  ring

end TauCeti.Associative
