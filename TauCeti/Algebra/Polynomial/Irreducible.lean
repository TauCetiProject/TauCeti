/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Group.Irreducible.Defs

/-!
# Irreducible polynomials over a nontrivial ring

If the polynomial ring `D[X]` has an irreducible element, then `D` is not the zero ring, since
over the zero ring every polynomial is a unit.
-/

public section

open Polynomial

namespace Irreducible

/-- If `D[X]` has an irreducible element then `D` is not the zero ring. -/
theorem nontrivial_coeff {D : Type*} [Semiring D] {q : D[X]} (hq : Irreducible q) :
    Nontrivial D := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hq.not_isUnit (isUnit_of_subsingleton q)

end Irreducible
