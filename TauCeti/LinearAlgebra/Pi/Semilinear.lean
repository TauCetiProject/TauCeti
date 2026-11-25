/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Ring.Equiv

/-!
# Coordinatewise semilinear equivalences

A ring equivalence induces a semilinear equivalence on coordinate spaces by acting
on each coordinate.
-/

public section

attribute [local instance] RingHomInvPair.of_ringEquiv

namespace RingEquiv

variable {R S : Type*} [Semiring R] [Semiring S]

/-- Apply a ring equivalence to each coordinate as a semilinear equivalence. -/
def piSemilinearEquiv (σ : R ≃+* S) (ι : Type*) :
    (ι → R) ≃ₛₗ[(σ : R →+* S)] (ι → S) where
  toAddEquiv := AddEquiv.piCongrRight fun _ => σ.toAddEquiv
  map_smul' a x := funext fun i => σ.map_mul a (x i)

@[simp]
theorem piSemilinearEquiv_apply (σ : R ≃+* S) {ι : Type*} (x : ι → R) :
    σ.piSemilinearEquiv ι x = σ ∘ x := (rfl)

@[simp]
theorem piSemilinearEquiv_symm (σ : R ≃+* S) (ι : Type*) :
    (σ.piSemilinearEquiv ι).symm = σ.symm.piSemilinearEquiv ι := (rfl)

end RingEquiv
