/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.Ring

/-!
# Integer casts in a ring of positive characteristic, read modulo the characteristic

In a ring of characteristic `p` the cast of an integer depends only on its residue modulo `p`,
which is `CharP.intCast_eq_intCast`. An explicitly tabulated integral computation is often carried
out on a product of two entries and compared against a residue, so the form actually used is that
of a product: the casts of two integers multiply to the cast of any integer congruent to their
product.

## Main results

* `CharP.intCast_mul_eq_intCast_of_modEq`: the product of two integer casts, read modulo the
  characteristic.
* `CharP.intCast_mul_mul_mul_eq_intCast_mul`: the same, with the two casts separated by ring
  factors that the congruence leaves untouched.
-/

public section

namespace CharP

/-- **The product of two integer casts is the cast of any integer congruent to their product**,
modulo the characteristic. -/
theorem intCast_mul_eq_intCast_of_modEq {R : Type*} [NonAssocRing R] (p : ℕ) [CharP R p]
    {a b c : ℤ} (h : a * b ≡ c [ZMOD p]) : (a : R) * (b : R) = (c : R) := by
  rw [← Int.cast_mul (α := R) a b]
  exact (CharP.intCast_eq_intCast R p).mpr h

/-- **Two integer casts separated by ring factors, read modulo the characteristic.** Only the two
integer coefficients are combined; the two ring factors are carried along unchanged. This is the
shape in which a weighted entry of an explicitly tabulated matrix is evaluated. -/
theorem intCast_mul_mul_mul_eq_intCast_mul {R : Type*} [CommRing R] (p : ℕ) [CharP R p]
    {a b c : ℤ} (x y : R) (h : a * b ≡ c [ZMOD p]) :
    (a : R) * (x * (b : R) * y) = (c : R) * (x * y) := by
  calc (a : R) * (x * (b : R) * y) = ((a : R) * (b : R)) * (x * y) := by ring
    _ = (c : R) * (x * y) := by rw [intCast_mul_eq_intCast_of_modEq p h]

end CharP
