/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Coprimality of polynomial factors with unit-separated parameters

Mathlib's `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` says that `X - C a` and `X - C b` are
coprime when `a - b` is a unit. Substituting any polynomial `p` for `X` shows that `p - C a` and
`p - C b` are coprime as well (`Polynomial.isCoprime_sub_C_of_isUnit_sub`), for example the
binomials `X ^ n - C a` and `X ^ n - C b`.

The normalised linear factors `1 - C a * X` and `1 - C b * X` are also coprime when
`a - b` is a unit, even when neither parameter is a unit.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- If `a - b` is a unit, the translates `p - C a` and `p - C b` of a polynomial are coprime. -/
theorem isCoprime_sub_C_of_isUnit_sub (p : R[X]) {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (p - C a) (p - C b) := by
  simpa using (isCoprime_X_sub_C_of_isUnit_sub h).map (aeval p).toRingHom

/-- Normalised linear factors are coprime if the difference of their parameters is a unit.
Neither parameter itself needs to be a unit. -/
theorem isCoprime_one_sub_C_mul_X_of_isUnit_sub {a b : R} (hab : IsUnit (a - b)) :
    IsCoprime (1 - C a * X) (1 - C b * X) := by
  obtain ⟨c, hc⟩ := hab
  refine ⟨C (-(c⁻¹ : Rˣ) * b), C ((c⁻¹ : Rˣ) * a), ?_⟩
  have h : (c⁻¹ : Rˣ) * (a - b) = (1 : R) := by rw [← hc]; simp
  calc
    C (-(c⁻¹ : Rˣ) * b) * (1 - C a * X) +
        C ((c⁻¹ : Rˣ) * a) * (1 - C b * X) = C ((c⁻¹ : Rˣ) * (a - b)) := by
      simp only [map_mul, map_neg, map_sub]
      ring
    _ = 1 := by rw [h, map_one]

end Polynomial
