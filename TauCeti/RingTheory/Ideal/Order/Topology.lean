/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import TauCeti.RingTheory.Ideal.Order.Basic

/-!
# Local order at the closed point of a local ring

In a local ring `R`, `IsLocalRing.closedPoint R` is the prime `maximalIdeal R` in
`PrimeSpectrum R`. This file records the topological specialization
`Ideal.orderAt_closedPoint`, identifying the order of an ideal at `IsLocalRing.closedPoint R` with
its `localOrder`.
-/

public section

namespace Ideal

open IsLocalRing

/-- In a local ring, the order at the closed point agrees with the local order. -/
@[simp]
theorem orderAt_closedPoint {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) :
    I.orderAt (IsLocalRing.closedPoint R) = I.localOrder := by
  let e : R ≃ₐ[R] Localization.AtPrime (IsLocalRing.closedPoint R).asIdeal :=
    IsLocalization.atUnits R (IsLocalRing.closedPoint R).asIdeal.primeCompl
      fun x hx ↦ notMem_maximalIdeal.mp hx
  have he : (e.toRingEquiv : R →+* Localization.AtPrime (IsLocalRing.closedPoint R).asIdeal) =
      algebraMap R _ :=
    RingHom.ext e.commutes
  rw [orderAt_def, ← he]
  exact localOrder_map_equiv I e.toRingEquiv

end Ideal
