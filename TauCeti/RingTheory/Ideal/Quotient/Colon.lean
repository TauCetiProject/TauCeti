/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Annihilators of residue classes

For a two-sided ideal `I` of a ring `R` and `c : R`, the annihilator of the class of `c` in the
`R`-module `R ⧸ I`, written as the colon ideal
`(⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I c}`, is `{r | r * c ∈ I}`; for commutative
`R` this is the ideal quotient `(I : c)`. This is the form in which associated primes of `R ⧸ I`
appear (`isAssociatedPrime_iff`).

## Main results

* `TauCeti.Ideal.Quotient.mem_colon_singleton_mk`: `r` annihilates the class of `c` in
  `R ⧸ I` exactly when `r * c ∈ I`.
-/

public section

open Ideal.Quotient

namespace TauCeti.Ideal.Quotient

variable {R : Type*} [Ring R] {I : Ideal R} [I.IsTwoSided]

/-- An element `r` annihilates the class of `c` in `R ⧸ I` exactly when `r * c ∈ I`. -/
theorem mem_colon_singleton_mk {c r : R} :
    r ∈ (⊥ : Submodule R (R ⧸ I)).colon {mk I c} ↔ r * c ∈ I := by
  -- `R ⧸ I` is an `R`-module as a submodule quotient, so `r • mk I c = mk I (r * c)` is
  -- `Submodule.Quotient.mk_smul` once `mk I` is written as `Submodule.Quotient.mk`.
  rw [Submodule.mem_colon_singleton, ← mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
    Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]

end TauCeti.Ideal.Quotient
