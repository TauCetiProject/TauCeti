/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsRealClosed.Real
public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Real
public import TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Signature

/-!
# The discriminant of a regular real quadratic form

Over any ordered real closed field the discriminant of a regular form `Q` is `sigNeg Q • [-1]`,
where `sigNeg Q` is its negative index of inertia (`QuadraticForm.discr_formClass_eq_sigNeg_nsmul`
in `TauCeti.LinearAlgebra.QuadraticForm.RegularFormClass.Signature`). Over `ℝ` the square class of
`-1` has order `2`, so the discriminant of a regular real form is trivial precisely when `sigNeg Q`
is even.

## Main results

* `QuadraticForm.discr_formClass_eq_zero_iff_even_sigNeg`: the discriminant of a regular real form
  is trivial exactly when `sigNeg Q` is even.
* `TauCeti.discr_formClass_realSignatureForm`: the normal form of signature `(p, q)` has
  discriminant `q • [-1]`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter II, §3.
-/

public section

open QuadraticMap QuadraticForm TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℝ M] [FiniteDimensional ℝ M]

namespace QuadraticForm

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
