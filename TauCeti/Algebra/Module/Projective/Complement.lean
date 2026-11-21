/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Projection

/-!
# Complements of submodules of projective modules

A submodule with a complement in a projective module is projective: the inclusion is split by the
projection onto it.

## Main results

* `Module.Projective.of_isCompl`: a submodule with a complement in a projective module is
  projective.
-/

public section

/-- A submodule with a complement in a projective module is projective: the inclusion is split by
the projection onto it. -/
theorem Module.Projective.of_isCompl {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Module.Projective R M] {T T' : Submodule R M} (hcompl : IsCompl T T') :
    Module.Projective R T :=
  Module.Projective.of_split T.subtype (T.projectionOnto T' hcompl) (by ext x; simp)
