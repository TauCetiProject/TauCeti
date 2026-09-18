/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Discriminant

/-!
# The discriminant of a regular real quadratic form

Over `ℝ` the square class of a nonzero number is its sign, so the discriminant of a regular form
only records the sign of the product of the weights of a diagonalization.  By Sylvester's law of
inertia that sign is `(-1)^q`, where `q = sigNeg Q` is the negative index of inertia.  This is the
determinant-sign formula `sign (det Q) = (-1)^q`, stated in the square-class group.

In particular the discriminant of a regular real form is determined by its signature, and it is
trivial exactly when the negative index is even.

## Main results

* `QuadraticForm.discr_formClass_eq_sigNeg_nsmul`: the discriminant of a regular real form is
  `sigNeg Q • [-1]`.
* `QuadraticForm.discr_formClass_eq_zero_iff_even_sigNeg`: it is trivial exactly when `sigNeg Q`
  is even.
* `TauCeti.discr_formClass_realSignatureForm`: the normal form of signature `(p, q)` has
  discriminant `q • [-1]`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §3.
-/

public section

open QuadraticMap QuadraticForm TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

namespace QuadraticForm

/-- **The determinant-sign formula.** The discriminant of a regular real quadratic form is the
class of `(-1)^q`, where `q` is its negative index of inertia. -/
theorem discr_formClass_eq_sigNeg_nsmul (Q : _root_.QuadraticForm ℝ M) (hQ : Q.Nondegenerate) :
    RegularFormClass.discr (formClass Q hQ) = sigNeg Q • squareClass (-1 : ℝˣ) := by
  obtain ⟨⟨n, w⟩, hp⟩ := exists_presentedForm_equivalent Q hQ
  rw [discr_formClass Q hQ ⟨n, w⟩ hp, squareClass_prod, sum_squareClass_eq_ncard_nsmul,
    sigNeg_of_equiv_weightedSumSquares (by rwa [← presentedForm_eq_weightedSumSquares_coe])]

/-- The discriminant of a regular real quadratic form is trivial exactly when its negative index
of inertia is even. -/
@[simp]
theorem discr_formClass_eq_zero_iff_even_sigNeg (Q : _root_.QuadraticForm ℝ M)
    (hQ : Q.Nondegenerate) :
    RegularFormClass.discr (formClass Q hQ) = 0 ↔ Even (sigNeg Q) := by
  rw [discr_formClass_eq_sigNeg_nsmul, nsmul_squareClass_neg_one_eq_zero_iff_even]

end QuadraticForm

namespace TauCeti

/-- The normal form `p⟨1⟩ ⊥ q⟨-1⟩` of signature `(p, q)` has discriminant `q • [-1]`. -/
@[simp]
theorem discr_formClass_realSignatureForm (p q : ℕ) :
    RegularFormClass.discr
        (formClass (realSignatureForm p q) (nondegenerate_realSignatureForm p q)) =
      q • squareClass (-1 : ℝˣ) := by
  rw [discr_formClass_eq_sigNeg_nsmul, sigNeg_realSignatureForm]

end TauCeti
