/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.Stalk

import TauCeti.RingTheory.AdicCompletion.LocalRing

/-!
# Regularity of the analytic stalk at a classical point

`TauCeti.AffinoidSubdomain.isRegularLocalRing_stalk_iff` characterizes regularity of the analytic
stalk of a rigid affinoid by regularity of the algebraic localization. It uses
`TauCeti.AffinoidSubdomain.completionRingEquiv` and invariance of regularity under completion.
-/

public section

namespace TauCeti.AffinoidSubdomain

/-- At a classical point of a rigid affinoid, the analytic stalk is regular if and only if
the algebraic localization is regular. See Conrad, *Irreducible components of rigid spaces*,
§1.2. -/
theorem isRegularLocalRing_stalk_iff (K : Type*) [NontriviallyNormedField K]
    [IsUltrametricDist K] [CompleteSpace K] {A : Type*} [CommRing A] [Algebra K A]
    [hA : Fact (IsAffinoidAlgebra K A)] {x : MaximalSpectrum A} :
    IsRegularLocalRing (stalk K x) ↔ IsRegularLocalRing (Localization.AtPrime x.asIdeal) := by
  have := hA.out.isNoetherianRing
  have hAmbient : IsRegularLocalRing (AdicCompletion x.asIdeal A) ↔
      IsRegularLocalRing (Localization.AtPrime x.asIdeal) := by
    exact AdicCompletion.isRegularLocalRing_iff_of_isMaximal x.asIdeal _
  have hStalk : IsRegularLocalRing
      (AdicCompletion (IsLocalRing.maximalIdeal (stalk K x)) (stalk K x)) ↔
      IsRegularLocalRing (stalk K x) := by
    exact AdicCompletion.isRegularLocalRing_iff le_rfl
  have hCompletion : IsRegularLocalRing (AdicCompletion x.asIdeal A) ↔
      IsRegularLocalRing
        (AdicCompletion (IsLocalRing.maximalIdeal (stalk K x)) (stalk K x)) := by
    let e := completionRingEquiv K x
    exact ⟨fun _ ↦ IsRegularLocalRing.of_ringEquiv e,
      fun _ ↦ IsRegularLocalRing.of_ringEquiv e.symm⟩
  exact hStalk.symm.trans (hCompletion.symm.trans hAmbient)

end TauCeti.AffinoidSubdomain
