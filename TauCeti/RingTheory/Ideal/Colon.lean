/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.Ideal.Colon

/-!
# Colon ideals and restriction of scalars

For an `R`-algebra `S`, the ideal `(N : x)` of a submodule `N` of an `S`-module commutes with
restricting scalars to `R`.

## Main results

* `Submodule.comap_colon_singleton`: the ideal `(N : x)` of `R` is the preimage of the ideal
  `(N : x)` of `S`.
-/

public section

variable {R S M : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [AddCommMonoid M]
  [Module R M] [Module S M] [IsScalarTower R S M]

/-- For a submodule `N` of an `S`-module `M` and `x ∈ M`, the ideal `(N : x)` of `R` is the
preimage of the ideal `(N : x)` of `S`. -/
theorem Submodule.comap_colon_singleton (N : Submodule S M) (x : M) :
    (N.colon {x}).comap (algebraMap R S) = (N.restrictScalars R).colon {x} := by
  ext r
  simp [Submodule.mem_colon_singleton]
