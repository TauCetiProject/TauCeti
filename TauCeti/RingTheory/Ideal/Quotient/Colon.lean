/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Annihilators of residue classes

For an ideal `I` of a commutative ring `R` and `c : R`, the annihilator of the class of `c` in
`R ⧸ I`, written as the colon ideal `(⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I c}`, is
the ideal quotient `(I : c) = {r | r * c ∈ I}`. This is the form in which associated primes of
`R ⧸ I` appear (`isAssociatedPrime_iff`).

## Main results

* `TauCeti.Ideal.Quotient.mem_colon_singleton_mk`: `r` annihilates the class of `c` in
  `R ⧸ I` exactly when `r * c ∈ I`.
-/

public section

open Ideal.Quotient

namespace TauCeti.Ideal.Quotient

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- An element `r` annihilates the class of `c` in `R ⧸ I` exactly when `r * c ∈ I`. -/
theorem mem_colon_singleton_mk {c r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ I)).colon {mk I c} ↔ r * c ∈ I := by
  rw [Submodule.mem_colon_singleton, Algebra.smul_def, algebraMap_eq, ← map_mul, Submodule.mem_bot,
    eq_zero_iff_mem]

end TauCeti.Ideal.Quotient
