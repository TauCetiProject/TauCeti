/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The opposite of a commutative Noetherian ring

Right modules over a ring `A` are left modules over `Aᵐᵒᵖ`, so categories of finitely generated
right modules, such as `FGModuleCat Aᵐᵒᵖ`, need `IsNoetherianRing Aᵐᵒᵖ` to be abelian. For a
commutative ring this is no extra condition: `RingEquiv.toOpposite` identifies `A` with `Aᵐᵒᵖ`.
This file records that as an instance, so that right-module constructions apply to commutative
Noetherian rings without a separate hypothesis.
-/

public section

namespace TauCeti

/-- The opposite of a commutative Noetherian ring is Noetherian. -/
instance IsNoetherianRing.mulOpposite (A : Type*) [CommSemiring A] [IsNoetherianRing A] :
    IsNoetherianRing Aᵐᵒᵖ :=
  isNoetherianRing_of_ringEquiv A (RingEquiv.toOpposite A)

end TauCeti
