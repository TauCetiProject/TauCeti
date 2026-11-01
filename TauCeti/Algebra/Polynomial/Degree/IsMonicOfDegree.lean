/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic polynomials of given degree under coefficient maps

A ring homomorphism into a nontrivial semiring sends a monic polynomial of degree `n` to a
monic polynomial of degree `n`.
-/

public section

namespace Polynomial

variable {R S : Type*} [Semiring R] [Semiring S] [Nontrivial S]

/-- Mapping the coefficients into a nontrivial semiring preserves being monic of degree `n`. -/
theorem IsMonicOfDegree.map {p : R[X]} {n : ℕ} (hp : p.IsMonicOfDegree n) (f : R →+* S) :
    (p.map f).IsMonicOfDegree n :=
  ⟨(hp.monic.natDegree_map f).trans hp.natDegree_eq, hp.monic.map f⟩

end Polynomial
