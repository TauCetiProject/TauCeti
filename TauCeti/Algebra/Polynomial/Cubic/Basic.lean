/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant

/-!
# Cubic normal forms and the elementary symmetric functions of the roots of a split cubic

A polynomial of degree at most three is `C a * X ^ 3 + C b * X ^ 2 + C c * X + C d` for its own
coefficients; this is the inverse half of Mathlib's `Cubic.equiv`, stated for the polynomial
itself rather than its degree-bounded subtype.

A product `(X - a)(X - b)(X - c)` of three monic linear factors determines the elementary
symmetric functions of `a, b, c`: by Vieta's formulas they are, up to sign, its coefficients.
This file records the resulting comparison of two such factorisations over any commutative ring,
using Mathlib's expansion `Cubic.prod_X_sub_C_eq`.

## Main results

* `Polynomial.eq_cubic_of_natDegree_le_three` and `Polynomial.Monic.eq_X_pow_three_add`: the normal
  form `a * X ^ 3 + b * X ^ 2 + c * X + d` of a polynomial of degree at most three, and
  `X ^ 3 + a * X ^ 2 + b * X + c` of a monic cubic.
* `TauCeti.Polynomial.add_add_eq_and_mul_add_mul_add_mul_eq`: if
  `(X - a)(X - b)(X - c) = (X - a')(X - b')(X - c')`, then `a + b + c = a' + b' + c'` and
  `ab + ac + bc = a'b' + a'c' + b'c'`.
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- A polynomial of degree at most three is `C a * X ^ 3 + C b * X ^ 2 + C c * X + C d` for its own
coefficients `a`, `b`, `c`, `d`. -/
theorem eq_cubic_of_natDegree_le_three {p : R[X]} (h : p.natDegree ≤ 3) :
    p = C (p.coeff 3) * X ^ 3 + C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) :=
  (congrArg Subtype.val (Cubic.equiv.apply_symm_apply ⟨p, natDegree_le_iff_degree_le.mp h⟩)).symm

/-- A monic polynomial of degree three is `X ^ 3 + C a * X ^ 2 + C b * X + C c` for its own
coefficients `a`, `b`, `c`. -/
theorem Monic.eq_X_pow_three_add {g : R[X]} (hmonic : g.Monic) (hdeg : g.natDegree = 3) :
    g = X ^ 3 + C (g.coeff 2) * X ^ 2 + C (g.coeff 1) * X + C (g.coeff 0) := by
  have h := eq_cubic_of_natDegree_le_three hdeg.le
  rwa [show g.coeff 3 = 1 from hdeg ▸ hmonic.coeff_natDegree, C_1, one_mul] at h

end Polynomial

namespace TauCeti.Polynomial

variable {R : Type*} [CommRing R]

/-- Equal products of three monic linear factors have the same first and second elementary
symmetric functions of their roots. -/
theorem add_add_eq_and_mul_add_mul_add_mul_eq {a b c a' b' c' : R}
    (h : (X - C a) * (X - C b) * (X - C c) = (X - C a') * (X - C b') * (X - C c')) :
    a + b + c = a' + b' + c' ∧ a * b + a * c + b * c = a' * b' + a' * c' + b' * c' := by
  rw [Cubic.prod_X_sub_C_eq, Cubic.prod_X_sub_C_eq, Cubic.toPoly_injective] at h
  simp only [Cubic.mk.injEq, true_and, neg_inj] at h
  exact ⟨h.1, h.2.1⟩

end TauCeti.Polynomial
