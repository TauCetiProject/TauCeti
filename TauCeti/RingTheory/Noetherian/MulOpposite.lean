/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# The opposite of a commutative Noetherian ring

Right modules over a ring `A` are modules over `Aᵐᵒᵖ`, so categories of finitely generated right
modules ask for `IsNoetherianRing Aᵐᵒᵖ`. For a commutative ring, `RingEquiv.toOpposite`
identifies `A` with `Aᵐᵒᵖ`, and this file records the resulting instance, so that the right
Noetherian hypothesis is found automatically for commutative Noetherian rings.
-/

public section

/-- The opposite of a commutative Noetherian semiring is Noetherian. -/
instance MulOpposite.isNoetherianRing {R : Type*} [CommSemiring R] [IsNoetherianRing R] :
    IsNoetherianRing Rᵐᵒᵖ :=
  isNoetherianRing_of_ringEquiv R (RingEquiv.toOpposite R)
