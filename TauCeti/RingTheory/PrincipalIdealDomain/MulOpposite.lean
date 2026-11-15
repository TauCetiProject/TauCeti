/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The opposite of a commutative principal ideal ring

Right modules over a ring `R` are modules over `Rᵐᵒᵖ`, so right-module results such as
`TauCeti.AlgebraicK0.finrankEquivPID` ask for `IsPrincipalIdealRing Rᵐᵒᵖ`. For a commutative
semiring, `RingEquiv.toOpposite` identifies `R` with `Rᵐᵒᵖ`, and this file records the resulting
instance so that `IsPrincipalIdealRing Rᵐᵒᵖ` is synthesized automatically for commutative
principal ideal rings.
-/

public section

/-- The opposite of a commutative principal ideal semiring is a principal ideal ring. -/
instance MulOpposite.isPrincipalIdealRing {R : Type*} [CommSemiring R] [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing Rᵐᵒᵖ :=
  IsPrincipalIdealRing.of_surjective (RingEquiv.toOpposite R) (RingEquiv.toOpposite R).surjective
