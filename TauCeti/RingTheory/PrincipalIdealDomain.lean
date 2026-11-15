/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Principal ideal ring instance for `ULift`

Transporting `IsPrincipalIdealRing` along the surjective ring equivalence
`ULift.ringEquiv.symm : R ≃+* ULift R` equips universe-lifted principal ideal rings (in particular
`ULift ℤ`) with an `IsPrincipalIdealRing` instance.
-/

public section

universe u v

namespace ULift

instance instIsPrincipalIdealRing {R : Type u} [Semiring R] [IsPrincipalIdealRing R] :
    IsPrincipalIdealRing (ULift.{v} R) :=
  IsPrincipalIdealRing.of_surjective (ULift.ringEquiv.symm : R ≃+* ULift.{v} R)
    ULift.ringEquiv.symm.surjective

end ULift
