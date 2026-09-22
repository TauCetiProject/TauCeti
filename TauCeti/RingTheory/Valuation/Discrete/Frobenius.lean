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

Let `F` be a field of exponential characteristic `p`, and let `v : Valuation F ℤᵐ⁰`. Every
element in the image of the `n`-fold Frobenius has order under `v` divisible by `p ^ n`: if
`z = y ^ (p ^ n)`, then

`ord_v(z) = p ^ n * ord_v(y)`.

Consequently, an element whose order under a discrete valuation is not divisible by `p ^ n`
cannot lie in the image of the `n`-fold Frobenius. Applied to the valuation of a function-field
place, this is the valuation-theoretic input to the separating-element criterion in positive
characteristic.

## Main results

* `TauCeti.Valuation.ord_iterateFrobenius`: the order of an iterated Frobenius image.
* `TauCeti.Valuation.natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius`: membership in the
  `p ^ n`-power subfield forces divisibility of the order by `p ^ n`.

## References

H. Stichtenoth, *Algebraic Function Fields and Codes*, second edition, Proposition 3.10.2.
-/

public section

open scoped WithZero

namespace TauCeti.Valuation

universe u

variable {F : Type u} [Field F]
variable (v : _root_.Valuation F ℤᵐ⁰) (p : ℕ) [ExpChar F p]

/-- The order under a discrete valuation of an `n`-fold Frobenius image is multiplied by
`p ^ n`. -/
@[simp]
theorem ord_iterateFrobenius (n : ℕ) (z : F) :
    _root_.Valuation.ord v (iterateFrobenius F p n z) =
      (p ^ n : ℤ) * _root_.Valuation.ord v z := by
  rw [iterateFrobenius_def, _root_.Valuation.ord_pow]
  norm_num

/-- Membership in the image of the `n`-fold Frobenius forces the order under every discrete
valuation to be divisible by `p ^ n`. -/
theorem natCast_pow_dvd_ord_of_mem_fieldRange_iterateFrobenius (n : ℕ) {z : F}
    (hz : z ∈ RingHom.fieldRange (iterateFrobenius F p n)) :
    (p ^ n : ℤ) ∣ _root_.Valuation.ord v z := by
  obtain ⟨y, rfl⟩ := hz
  rw [ord_iterateFrobenius]
  exact dvd_mul_right _ _

end TauCeti.Valuation

end
