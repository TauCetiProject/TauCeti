/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The opposite of a commutative principal ideal ring

Records `IsPrincipalIdealRing Rᵐᵒᵖ` for a commutative principal ideal semiring `R` via
`RingEquiv.toOpposite`, used by right-module results such as `TauCeti.KZero.rankEquivPID`.
-/

public section

/-- The opposite of a commutative principal ideal semiring is a principal ideal ring. -/
instance MulOpposite.isPrincipalIdealRing {R : Type*} [CommSemiring R] [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing Rᵐᵒᵖ :=
  IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite R) (RingEquiv.toOpposite R).surjective
