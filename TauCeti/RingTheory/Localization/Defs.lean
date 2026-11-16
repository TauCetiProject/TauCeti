/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Defs

/-!
# Injectivity of ring homomorphisms lifted out of a localization

For a localization `S` of a commutative semiring `R` at a submonoid `M`, a ring homomorphism
`g : R →+* P` that maps `M` into the units of `P` extends to `IsLocalization.lift hg : S →+* P`.
Complementing Mathlib's `IsLocalization.lift_injective_iff` and `IsLocalization.eq_of_eq`, this file
records that `IsLocalization.lift hg` is injective whenever `g` is injective
(`IsLocalization.lift_injective_of_injective`).
-/

public section

namespace IsLocalization

variable {R : Type*} [CommSemiring R] {M : Submonoid R} {S : Type*} [CommSemiring S]
  [Algebra R S] [IsLocalization M S] {P : Type*} [CommSemiring P] {g : R →+* P}

/-- If an injective ring homomorphism `g : R →+* P` sends every element of `M` to a unit, then its
lift `S →+* P` out of a localization `S` of `R` at `M` is injective. -/
theorem lift_injective_of_injective (hg : ∀ y : M, IsUnit (g y)) (hinj : Function.Injective g) :
    Function.Injective (lift (M := M) (S := S) hg) :=
  (lift_injective_iff hg).mpr fun _ _ ↦
    ⟨eq_of_eq (S := S) hg, fun h ↦ congrArg (algebraMap R S) (hinj h)⟩

end IsLocalization
