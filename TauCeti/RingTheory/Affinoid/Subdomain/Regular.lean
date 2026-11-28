/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.RingTheory.Affinoid.Subdomain.Basic

import TauCeti.RingTheory.AdicCompletion.LocalRing
import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Affinoid.Subdomain.Completion

/-!
# Regularity at classical points under affinoid restriction

`TauCeti.IsAffinoidSubdomainMap.isRegularLocalRing_iff` compares the localizations at corresponding
maximal ideals of an affinoid algebra and an affinoid subdomain. It combines
`TauCeti.IsAffinoidSubdomainMap.completionMaximalAlgEquiv` with invariance of regularity under
completion. Thus a classical point is singular in the ambient affinoid exactly when it is
singular in the subdomain.
-/

public section

namespace TauCeti.IsAffinoidSubdomainMap

universe u

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}

/-- The localizations of an affinoid algebra and a subdomain at corresponding maximal ideals
are regular simultaneously. See Conrad, *Irreducible components of rigid spaces*, §1.2. -/
theorem isRegularLocalRing_iff (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A)
    {y : MaximalSpectrum B} :
    IsRegularLocalRing (Localization.AtPrime y.asIdeal) ↔
      IsRegularLocalRing
        (Localization.AtPrime (h.isAffinoidAlgebra.maximalSpectrumComap φ y).asIdeal) := by
  have := hA.isNoetherianRing
  have := h.isAffinoidAlgebra.isNoetherianRing
  let x : MaximalSpectrum A := h.isAffinoidAlgebra.maximalSpectrumComap φ y
  have hAmbient : IsRegularLocalRing (AdicCompletion x.asIdeal A) ↔
      IsRegularLocalRing (Localization.AtPrime x.asIdeal) := by
    exact AdicCompletion.isRegularLocalRing_iff_of_isMaximal x.asIdeal _
  have hSubdomain : IsRegularLocalRing (AdicCompletion (x.asIdeal.map φ) B) ↔
      IsRegularLocalRing (Localization.AtPrime y.asIdeal) := by
    rw [h.map_maximalSpectrumComap_asIdeal hA y]
    exact AdicCompletion.isRegularLocalRing_iff_of_isMaximal y.asIdeal _
  have hCompletion : IsRegularLocalRing (AdicCompletion x.asIdeal A) ↔
      IsRegularLocalRing (AdicCompletion (x.asIdeal.map φ) B) := by
    have hx : x ∈ U := h.range_maximalSpectrumComap_subset ⟨y, rfl⟩
    let e := (h.completionMaximalAlgEquiv hA hx).toRingEquiv
    exact ⟨fun _ ↦ IsRegularLocalRing.of_ringEquiv e,
      fun _ ↦ IsRegularLocalRing.of_ringEquiv e.symm⟩
  exact hSubdomain.symm.trans (hCompletion.symm.trans hAmbient)

end TauCeti.IsAffinoidSubdomainMap
