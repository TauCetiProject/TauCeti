/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Coprimality of translates of a polynomial

Mathlib's `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` says that `X - C a` and `X - C b` are
coprime when `a - b` is a unit. Substituting any polynomial `p` for `X` shows that `p - C a` and
`p - C b` are coprime as well (`Polynomial.isCoprime_sub_C_of_isUnit_sub`), for example the
binomials `X ^ n - C a` and `X ^ n - C b`.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If `a - b` is a unit, the translates `p - C a` and `p - C b` of a polynomial are coprime. -/
theorem isCoprime_sub_C_of_isUnit_sub (p : R[X]) {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (p - C a) (p - C b) := by
  simpa using (isCoprime_X_sub_C_of_isUnit_sub h).map (aeval p).toRingHom

end Polynomial
