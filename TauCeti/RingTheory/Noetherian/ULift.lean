/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Universe lifts of Noetherian rings

`ULift.ringEquiv` identifies a semiring `R` with its universe lift `ULift R`, so the lift of a
Noetherian semiring is Noetherian. This file records the resulting instance, so that for example
the hypothesis `IsNoetherianRing (ULift ℤ)` needed over `Spec (ULift ℤ)`, the terminal scheme, is
found automatically.
-/

public section

universe u v

/-- The universe lift of a Noetherian semiring is Noetherian. -/
instance ULift.isNoetherianRing {R : Type u} [Semiring R] [IsNoetherianRing R] :
    IsNoetherianRing (ULift.{v} R) :=
  isNoetherianRing_of_ringEquiv R ULift.ringEquiv.symm
