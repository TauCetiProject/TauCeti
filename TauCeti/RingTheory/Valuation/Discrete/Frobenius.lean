/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import TauCeti.RingTheory.Valuation.Discrete.Order

/-!
# Orders of Frobenius powers under a discrete valuation

Let `R` be a commutative ring of exponential characteristic `p`, and let `v : Valuation R ℤᵐ⁰`.
Every element in the image of the `n`-fold Frobenius has order under `v` divisible by `p ^ n`: if
`z = y ^ (p ^ n)`, then

`ord_v(z) = p ^ n * ord_v(y)`.

The order has its junk value zero on the valuation support, where these divisibility assertions
remain valid.

Consequently, an element whose order under a discrete valuation is not divisible by `p ^ n`
cannot lie in the image of the `n`-fold Frobenius. Applied to the valuation of a function-field
place, this is the valuation-theoretic input to the separating-element criterion in positive
characteristic. Since `z ^ p - b ^ p = (z - b) ^ p`, a difference of `p`-th powers also has order
divisible by `p`; this is what rules out `p`-th roots of constants in the completion at a place
with inseparable residue field.

## Main results

* `Valuation.ord_iterateFrobenius`: the order of an iterated Frobenius image.
* `Valuation.natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius`: membership in the
  `p ^ n`-power subfield forces divisibility of the order by `p ^ n`.
* `Valuation.not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord`: the
  contrapositive, eliminating membership in the `p ^ n`-power subfield.
* `Valuation.natCast_dvd_ord_pow_sub_pow`: a difference of `p`-th powers has order divisible by
  `p`.

## References

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

open scoped WithZero

namespace Valuation

universe u

section CommRing

variable {R : Type u} [CommRing R]
variable (v : _root_.Valuation R ℤᵐ⁰) (p : ℕ) [ExpChar R p]

/-- The order under a discrete valuation of an `n`-fold Frobenius image is multiplied by
`p ^ n`. -/
@[simp]
theorem ord_iterateFrobenius (n : ℕ) (z : R) :
    _root_.Valuation.ord v (iterateFrobenius R p n z) =
      (p ^ n : ℤ) * _root_.Valuation.ord v z := by
  simp [iterateFrobenius_def]

/-- The order of a difference of `p`-th powers under a discrete valuation is divisible by `p`. -/
theorem natCast_dvd_ord_pow_sub_pow (z b : R) :
    (p : ℤ) ∣ _root_.Valuation.ord v (z ^ p - b ^ p) := by
  rw [← sub_pow_expChar, _root_.Valuation.ord_pow]
  exact dvd_mul_right _ _

end CommRing

section Field

variable {F : Type u} [Field F]
variable (v : _root_.Valuation F ℤᵐ⁰) (p : ℕ) [ExpChar F p]

/-- Membership in the image of the `n`-fold Frobenius forces the order under every discrete
valuation to be divisible by `p ^ n`. -/
theorem natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius (n : ℕ) {z : F}
    (hz : z ∈ RingHom.fieldRange (iterateFrobenius F p n)) :
    (p ^ n : ℤ) ∣ _root_.Valuation.ord v z := by
  obtain ⟨y, rfl⟩ := hz
  rw [ord_iterateFrobenius]
  exact dvd_mul_right _ _

/-- An element whose order under a discrete valuation is not divisible by `p ^ n` does not lie
in the image of the `n`-fold Frobenius. -/
theorem not_mem_fieldRange_iterateFrobenius_of_not_natCast_pow_dvd_ord (n : ℕ) {z : F}
    (hz : ¬(p ^ n : ℤ) ∣ _root_.Valuation.ord v z) :
    z ∉ RingHom.fieldRange (iterateFrobenius F p n) := fun h =>
  hz (natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius v p n h)

end Field

end Valuation

end
