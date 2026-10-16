/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Degree of a normalized polynomial

Over a domain `R` with a `NormalizationMonoid`, `normalize p` is `p` times a unit, so it has the
same degree as `p`. Mathlib states this (`Polynomial.degree_normalize`,
`Polynomial.natDegree_normalize`) only over a field; here it is proved for any such domain, for
instance for `ℤ[X]`.
-/

public section

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [NormalizationMonoid R]

/-- Normalizing a polynomial over a domain preserves its degree. This generalizes Mathlib's
`Polynomial.degree_normalize` from fields to any domain with a `NormalizationMonoid`. -/
@[simp]
theorem _root_.Polynomial.degree_normalize' (p : R[X]) : (normalize p).degree = p.degree :=
  degree_eq_degree_of_associated (normalize_associated p)

/-- Normalizing a polynomial over a domain preserves its natural degree. This generalizes
Mathlib's `Polynomial.natDegree_normalize` from fields to any domain with a
`NormalizationMonoid`. -/
@[simp]
theorem _root_.Polynomial.natDegree_normalize' (p : R[X]) :
    (normalize p).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq (degree_normalize' p)

end TauCeti
