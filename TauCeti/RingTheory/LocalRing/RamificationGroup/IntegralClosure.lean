/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RingTheory.LocalRing.RamificationGroup

/-!
# Integral-closure and fixed-field transport of lower ramification groups

This module transports the lower ramification filtration along algebra equivalences of
`integralClosure` (`AlgEquiv.autCongr`) and along Galois fixed fields
(`IsGalois.normalAutEquivQuotient`).

## Main results

* `AlgEquiv.ramificationGroup_integralClosure_eq_comap_autCongr`: `e : E ≃ₐ[K] E'` over `A` pulls
  back lower ramification groups on `integralClosure`.
* `TauCeti.IsLocalRing.ramificationGroup_fixedPoints_integralClosure_eq_comap`:
  `IsGalois.normalAutEquivQuotient H` pulls back lower ramification groups from
  `integralClosure A (IntermediateField.fixedField H)` to
  `FixedPoints.subalgebra A (integralClosure A L) H`.
-/

public section

open IsLocalRing

namespace TauCeti.IsLocalRing

/-- `e : E ≃ₐ[K] E'` over `A` pulls back lower ramification groups on `integralClosure`. -/
theorem _root_.AlgEquiv.ramificationGroup_integralClosure_eq_comap_autCongr {A K E E' : Type*}
    [CommRing A] [CommRing K] [CommRing E] [CommRing E'] [Algebra A K] [Algebra K E] [Algebra A E]
    [IsScalarTower A K E] [Algebra K E'] [Algebra A E'] [IsScalarTower A K E']
    [IsLocalRing (integralClosure A E)] [IsLocalRing (integralClosure A E')] (e : E ≃ₐ[K] E')
    (i : ℤ) : ramificationGroup (E ≃ₐ[K] E) (integralClosure A E) i =
      (ramificationGroup (E' ≃ₐ[K] E') (integralClosure A E') i).comap
        (e.autCongr : (E ≃ₐ[K] E) →* (E' ≃ₐ[K] E')) :=
  ramificationGroup_eq_comap_of_ringEquiv
    (e := (e.restrictScalars A).mapIntegralClosure.toRingEquiv)
    (fun _ _ ↦ Subtype.ext <| by simp [AlgEquiv.smul_def, AlgEquiv.autCongr_apply]) i

open IntermediateField in
/-- `IsGalois.normalAutEquivQuotient H` pulls back lower ramification groups from
`integralClosure A (fixedField H)` to `FixedPoints.subalgebra A (integralClosure A L) H`. -/
theorem ramificationGroup_fixedPoints_integralClosure_eq_comap (A : Type*) {K L : Type*}
    [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
    [IsLocalRing (integralClosure A L)] (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (i : ℤ) :
    ramificationGroup ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) i =
      (ramificationGroup (fixedField H ≃ₐ[K] fixedField H) (integralClosure A (fixedField H))
        i).comap (IsGalois.normalAutEquivQuotient H : _ →* _) :=
  ramificationGroup_eq_comap_of_ringEquiv
    (e := (TauCeti.fixedPointsSubalgebraIntegralClosureEquiv A H).toRingEquiv)
    (TauCeti.fixedPointsSubalgebraIntegralClosureEquiv_smul A H) i

end TauCeti.IsLocalRing
