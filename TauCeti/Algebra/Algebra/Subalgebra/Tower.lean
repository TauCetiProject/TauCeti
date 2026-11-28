/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Tower

/-!
# Subalgebras in towers of algebras

This file supplements `Mathlib.Algebra.Algebra.Subalgebra.Tower` with monotonicity of
`Subalgebra.restrictScalars`.

## Main results

* `Subalgebra.restrictScalars_mono`: restricting scalars preserves inclusion of subalgebras.
-/

public section

namespace Subalgebra

variable (R : Type*) {S A : Type*} [CommSemiring R] [CommSemiring S] [Semiring A]
  [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- Restricting scalars is monotone with respect to subalgebra inclusion. -/
@[gcongr, mono]
theorem restrictScalars_mono {U V : Subalgebra S A} (hUV : U ≤ V) :
    U.restrictScalars R ≤ V.restrictScalars R :=
  fun _ hx ↦ (mem_restrictScalars R).mpr (hUV ((mem_restrictScalars R).mp hx))

end Subalgebra
