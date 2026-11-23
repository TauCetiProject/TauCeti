/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.LocalRing
public import TauCeti.RingTheory.RegularLocalRing.Basic

/-!
# Completion of a discrete valuation ring

Completing a discrete valuation ring at its maximal ideal preserves regularity and dimension one,
so the completion is again a discrete valuation ring.
-/

public section

open IsLocalRing

namespace TauCeti.AdicCompletion

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The maximal-ideal completion of a discrete valuation ring is a discrete valuation ring. -/
instance : IsDiscreteValuationRing (AdicCompletion (maximalIdeal R) R) :=
  IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.mpr
    ((ringKrullDim_eq le_rfl).trans (IsDiscreteValuationRing.ringKrullDim_eq_one R))

end TauCeti.AdicCompletion
