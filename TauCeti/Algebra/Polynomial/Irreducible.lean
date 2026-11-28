/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import TauCeti.Algebra.Group.Irreducible.Defs
import Mathlib.Algebra.Polynomial.Div

/-!
# Irreducible polynomials over a nontrivial ring

Basic lemmas about irreducible polynomials over a semiring:

* `Irreducible.nontrivial_coeff`: if `D[X]` has an irreducible element, then `D` is not the zero
  ring, since over the zero ring every polynomial is a unit.
* `Polynomial.Monic.eq_X_of_irreducible_of_coeff_zero_eq_zero`: a monic irreducible polynomial
  over a nontrivial semiring with vanishing constant term is `X`.
-/

public section

open Polynomial

namespace Irreducible

/-- If `D[X]` has an irreducible element then `D` is not the zero ring. -/
theorem nontrivial_coeff {D : Type*} [Semiring D] {q : D[X]} (hq : Irreducible q) :
    Nontrivial D :=
  Polynomial.nontrivial_iff.1 hq.nontrivial

end Irreducible

namespace Polynomial

/-- A monic irreducible polynomial over a nontrivial semiring with vanishing constant term is
`X`. -/
theorem Monic.eq_X_of_irreducible_of_coeff_zero_eq_zero {R : Type*} [Semiring R] [Nontrivial R]
    {p : R[X]} (hm : p.Monic) (hp : Irreducible p) (ha0 : p.coeff 0 = 0) : p = X := by
  obtain ⟨q, hq⟩ := X_dvd_iff.mpr ha0
  have hqu : IsUnit q := (hp.isUnit_or_isUnit hq).resolve_left not_isUnit_X
  have hqm : q.Monic := monic_X.of_mul_monic_left (hq ▸ hm)
  rw [hq, hqm.eq_one_of_isUnit hqu, mul_one]

end Polynomial
