/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Basic
-- Proof-only: the degree of a place is divisible by the degree of the constant field.
import TauCeti.FieldTheory.FunctionField.Place.ConstantField

/-!
# Divisors of degree one and the constant field

The degree of every divisor of a function field `F / k` is a multiple of the degree of the field of
constants `algebraicClosure k F`, because that field sits inside the residue field of every place.
Hence a divisor of degree one forces the constant field to be exact. No function-field hypothesis
is needed.

## Main results

* `TauCeti.isIntegrallyClosedIn_of_exists_divisor_degree_eq_one`: a divisor of degree one forces
  the field of constants to be exact.
-/

public section

namespace TauCeti

open AlgebraicGeometry

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- **A divisor of degree one forces exact constants**: the degree of every divisor is a multiple
of the degree of the field of constants `algebraicClosure k F`, because that field sits inside
the residue field of every place.  No function-field hypothesis is needed. -/
theorem isIntegrallyClosedIn_of_exists_divisor_degree_eq_one
    (hdegree : ∃ D : Divisor k F, Divisor.degree D = 1) : IsIntegrallyClosedIn k F := by
  obtain ⟨D, hD⟩ := hdegree
  rw [isIntegrallyClosedIn_iff_finrank_algebraicClosure_eq_one]
  have hdvd : (Module.finrank k (algebraicClosure k F) : ℤ) ∣ Divisor.degree D := by
    rw [Divisor.degree_eq_sum_support]
    exact Finset.dvd_sum fun P _ ↦
      Dvd.dvd.mul_left (Int.natCast_dvd_natCast.mpr P.finrank_algebraicClosure_dvd_degree) _
  rw [hD] at hdvd
  exact_mod_cast Int.eq_one_of_dvd_one (Int.natCast_nonneg _) hdvd

end TauCeti
