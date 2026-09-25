/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.Ring.Commutator

/-!
# Polynomial evaluation across a semiconjugacy relation

If `a * x = x * (a + c)` and `c` commutes with `x`, then moving a polynomial in `a` past
`x ^ n` shifts its argument by `n • c`:

```text
p(a) xⁿ = xⁿ p(a + n c).
```

The reverse reordering shifts by `-n c`.  The main application is to the generalized binomial
coefficients `Ring.choose a m`: these are the Cartan generators of a Kostant integral form, while
the powers are the numerators of its root-vector divided powers.

The first result, `SemiconjBy.smeval_right`, is the general mechanism.  It says that polynomial
evaluation preserves both right-hand entries of `SemiconjBy`.  The remaining results specialize
it to an additive shift and then to `Ring.choose`.

## Main results

* `SemiconjBy.smeval_right`: simultaneous polynomial evaluation preserves semiconjugacy.
* `Polynomial.smeval_mul_pow_eq_pow_mul_smeval` and
  `Polynomial.pow_mul_smeval_eq_smeval_mul_pow`: the corresponding polynomial
  reordering identities.
* `TauCeti.ringChoose_mul_pow` and `TauCeti.pow_mul_ringChoose`: their two
  binomial-coefficient forms.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace SemiconjBy

universe u v

variable {R : Type u} {A : Type v}
variable [Semiring R] [Semiring A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Polynomial evaluation preserves the two right-hand entries of a semiconjugacy relation.

This generalizes Mathlib's `Polynomial.smeval_commute_left` from `Commute` to `SemiconjBy`,
following its proof. -/
theorem smeval_right {a x y : A} (h : SemiconjBy a x y) (p : Polynomial R) :
    SemiconjBy a (Polynomial.smeval p x) (Polynomial.smeval p y) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.smeval_add] using hp.add_right hq
  | monomial n r =>
      simpa only [Polynomial.smeval_monomial] using (h.pow_right n).smul_right r

end SemiconjBy

namespace TauCeti

universe u v

variable {A : Type u}

section Semiring

variable [Semiring A]

/-- A polynomial in `a` can be moved to the right across `x ^ n` by shifting its argument by
`n • c`. -/
theorem _root_.Polynomial.smeval_mul_pow_eq_pow_mul_smeval
    {R : Type v} [Semiring R] [Module R A]
    [IsScalarTower R A A]
    [SMulCommClass R A A] (p : _root_.Polynomial R) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    _root_.Polynomial.smeval p a * x ^ n =
      x ^ n * _root_.Polynomial.smeval p (a + n • c) := by
  have hs : SemiconjBy (x ^ n) (a + n • c) a :=
    (Associative.mul_pow_eq_pow_mul_add_nsmul h hc n).symm
  exact (hs.smeval_right p).eq.symm

end Semiring

section Ring

variable [Ring A]

/-- A polynomial in `a` can be moved to the left across `x ^ n` by shifting its argument by
`-n • c`. -/
theorem _root_.Polynomial.pow_mul_smeval_eq_smeval_mul_pow
    {R : Type v} [Semiring R] [Module R A]
    [IsScalarTower R A A]
    [SMulCommClass R A A] (p : _root_.Polynomial R) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    x ^ n * _root_.Polynomial.smeval p a =
      _root_.Polynomial.smeval p (a - n • c) * x ^ n := by
  have hs : SemiconjBy x (a + c) a := h.symm
  have hshift : (a - n • c) * x = x * ((a - n • c) + c) := by
    simpa only [add_sub_right_comm] using (hs.sub_right (hc.smul_left n).symm).eq.symm
  simpa only [sub_add_cancel] using
    (p.smeval_mul_pow_eq_pow_mul_smeval hshift hc n).symm

attribute [local instance] BinomialRing.toIsAddTorsionFree

/-- A generalized binomial coefficient in `a` can be moved to the right across `x ^ n` by
shifting its argument by `n • c`. -/
theorem ringChoose_mul_pow [BinomialRing A] (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    Ring.choose a m * x ^ n = x ^ n * Ring.choose (a + n • c) m := by
  apply nsmul_right_injective m.factorial_ne_zero
  dsimp only
  rw [← smul_mul_assoc, ← mul_smul_comm,
    ← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  exact Polynomial.smeval_mul_pow_eq_pow_mul_smeval (descPochhammer ℤ m) h hc n

/-- A generalized binomial coefficient in `a` can be moved to the left across `x ^ n` by
shifting its argument by `-n • c`. -/
theorem pow_mul_ringChoose [BinomialRing A] (m : ℕ) {a x c : A}
    (h : a * x = x * (a + c)) (hc : Commute c x) (n : ℕ) :
    x ^ n * Ring.choose a m = Ring.choose (a - n • c) m * x ^ n := by
  apply nsmul_right_injective m.factorial_ne_zero
  dsimp only
  rw [← mul_smul_comm, ← smul_mul_assoc,
    ← Ring.descPochhammer_eq_factorial_smul_choose,
    ← Ring.descPochhammer_eq_factorial_smul_choose]
  exact Polynomial.pow_mul_smeval_eq_smeval_mul_pow (descPochhammer ℤ m) h hc n

end Ring

end TauCeti
