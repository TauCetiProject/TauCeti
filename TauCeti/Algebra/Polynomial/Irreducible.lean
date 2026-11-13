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

/-- A monoid with an irreducible element is nontrivial, since `1` is not irreducible. -/
theorem nontrivial {M : Type*} [Monoid M] {p : M} (hp : Irreducible p) : Nontrivial M :=
  nontrivial_of_ne p 1 hp.ne_one

/-- If `D[X]` has an irreducible element then `D` is not the zero ring. -/
theorem nontrivial_coeff {D : Type*} [Semiring D] {q : D[X]} (hq : Irreducible q) :
    Nontrivial D :=
  Polynomial.nontrivial_iff.1 hq.nontrivial

end Irreducible
