/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Quotients of a ring that are linearly isomorphic to the ring

For an ideal `I` of a commutative ring `R`, the quotient `R ⧸ I` is isomorphic to `R` as an
`R`-module exactly when `I = ⊥`: linearly isomorphic modules have the same annihilator, and the
annihilator of `R ⧸ I` is `I` while that of `R` is `⊥`. For instance `R ⧸ 2R` is not isomorphic to
`R` unless `2 = 0` in `R`.

## Main statements

* `Ideal.nonempty_quotient_linearEquiv_self_iff`: `Nonempty ((R ⧸ I) ≃ₗ[R] R) ↔ I = ⊥`.
-/

public section

namespace Ideal

variable {R : Type*} [CommRing R] {I : Ideal R}

/-- **A quotient of a ring is isomorphic to the ring as a module only for the zero ideal.** For an
ideal `I` of a commutative ring `R`, `R ⧸ I ≃ₗ[R] R` exactly when `I = ⊥`: the two modules would
have the same annihilator, which is `I` for `R ⧸ I` and `⊥` for `R`. -/
theorem nonempty_quotient_linearEquiv_self_iff : Nonempty ((R ⧸ I) ≃ₗ[R] R) ↔ I = ⊥ :=
  ⟨fun ⟨e⟩ ↦ by
    rw [← I.annihilator_quotient, e.annihilator_eq, Module.annihilator_eq_bot]
    infer_instance,
  fun hI ↦ ⟨Submodule.quotEquivOfEqBot I hI⟩⟩

end Ideal
