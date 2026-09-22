/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import TauCeti.FieldTheory.FunctionField.Place.Basic

/-!
# Orders of Frobenius powers at a place

Let `F / k` be a field extension of exponential characteristic `p`, and let `P` be a place of
`F / k`.  Every element in the image of the `n`-fold Frobenius has order at `P` divisible by
`p ^ n`: if `z = y ^ (p ^ n)`, then

`ord_P(z) = p ^ n * ord_P(y)`.

Consequently an element whose order at one place is not divisible by `p` cannot be a `p`-th
power.  It is also transcendental over the constant field, since algebraic elements have order
zero at every place.  These are the valuation-theoretic inputs to the separating-element
criterion in positive characteristic: over a perfect constant field, an element of a function
field with order prime to the characteristic is separating.

## Main results

* `TauCeti.Place.ord_iterateFrobenius`: the order of an iterated Frobenius image.
* `TauCeti.Place.ord_frobenius`: the one-step form.
* `TauCeti.Place.intCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius`: membership in the
  `p ^ n`-power subfield forces divisibility of the order by `p ^ n`.
* `TauCeti.Place.not_mem_fieldRange_frobenius_of_not_dvd_ord`: a non-`p`-divisible order
  obstructs membership in the Frobenius image.
* `TauCeti.Place.transcendental_of_not_dvd_ord`: the same order condition makes the element
  transcendental over the constant field.

## References

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

namespace TauCeti.Place

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable (P : Place k F) (p : ℕ) [ExpChar F p]

/-- The order at a place of an `n`-fold Frobenius image is multiplied by `p ^ n`. -/
@[simp]
theorem ord_iterateFrobenius (n : ℕ) (z : F) :
    P.ord (iterateFrobenius F p n z) = (p ^ n : ℤ) * P.ord z := by
  rw [iterateFrobenius_def, P.ord_pow]
  norm_num

/-- The order at a place of a Frobenius image is multiplied by the exponential characteristic. -/
@[simp]
theorem ord_frobenius (z : F) : P.ord (frobenius F p z) = (p : ℤ) * P.ord z := by
  rw [frobenius_def, P.ord_pow]

/-- Membership in the image of the `n`-fold Frobenius forces the order at every place to be
divisible by `p ^ n`. -/
theorem intCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius (n : ℕ) {z : F}
    (hz : z ∈ RingHom.fieldRange (iterateFrobenius F p n)) :
    (p ^ n : ℤ) ∣ P.ord z := by
  obtain ⟨y, rfl⟩ := hz
  rw [ord_iterateFrobenius]
  exact dvd_mul_right _ _

/-- Membership in the Frobenius image forces the order at every place to be divisible by the
exponential characteristic. -/
theorem intCast_dvd_ord_of_mem_fieldRange_frobenius {z : F}
    (hz : z ∈ RingHom.fieldRange (frobenius F p)) : (p : ℤ) ∣ P.ord z := by
  obtain ⟨y, rfl⟩ := hz
  rw [ord_frobenius]
  exact dvd_mul_right _ _

/-- If the order of an element at one place is not divisible by the exponential characteristic,
then that element is not in the image of Frobenius, hence is not a `p`-th power. -/
theorem not_mem_fieldRange_frobenius_of_not_dvd_ord {z : F}
    (hz : ¬ (p : ℤ) ∣ P.ord z) : z ∉ RingHom.fieldRange (frobenius F p) :=
  fun h ↦ hz (P.intCast_dvd_ord_of_mem_fieldRange_frobenius p h)

/-- If the order of an element at one place is not divisible by `p ^ n`, then that element is not
in the image of the `n`-fold Frobenius. -/
theorem not_mem_fieldRange_iterateFrobenius_of_not_dvd_ord (n : ℕ) {z : F}
    (hz : ¬ (p ^ n : ℤ) ∣ P.ord z) :
    z ∉ RingHom.fieldRange (iterateFrobenius F p n) :=
  fun h ↦ hz (P.intCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius p n h)

omit [ExpChar F p] in
/-- An element whose order at one place is not divisible by `p` is transcendental over the
constant field.  Indeed, every algebraic element has order zero, which is divisible by every
integer. -/
theorem transcendental_of_not_dvd_ord {z : F} (hz : ¬ (p : ℤ) ∣ P.ord z) :
    Transcendental k z := by
  apply P.transcendental_of_ord_ne_zero
  intro hzero
  apply hz
  rw [hzero]
  exact dvd_zero _

end TauCeti.Place

end
