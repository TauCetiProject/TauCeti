/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.FreeBaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.Radical

/-!
# The geometric radical of a quadratic form

A quadratic form over a field is nondegenerate exactly when its radical vanishes after
extension to a perfect field, such as an algebraic closure. Testing the radical over the
ground field can miss singular vectors. Over an imperfect field of characteristic two,
`x² + t y²` has trivial radical when `t` is a nonsquare, but acquires a radical line
after adjoining a square root of `t`.

## References

* SGA 7 II, Exposé XII, §1.1, for the geometric criterion for ordinary quadratic forms.
-/

public section

namespace QuadraticForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

variable (L : Type*) [Field L] [Algebra K L]

/-- A quadratic form is nondegenerate exactly when its radical vanishes over a
perfect extension, in particular over an algebraic closure. -/
theorem nondegenerate_iff_radical_freeBaseChange_eq_bot [PerfectField L] (Q : QuadraticForm K V) :
    Q.Nondegenerate ↔ (Q.freeBaseChange L).radical = ⊥ :=
  (Q.nondegenerate_freeBaseChange_iff L).symm.trans
    (nondegenerate_iff_radical_eq_bot_of_perfectField _)

end QuadraticForm
