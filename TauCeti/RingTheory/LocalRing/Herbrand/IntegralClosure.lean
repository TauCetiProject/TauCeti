/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LocalRing.Herbrand.Jump
public import TauCeti.RingTheory.LocalRing.RamificationGroup.IntegralClosure

/-!
# Integral-closure and fixed-field transport of Herbrand functions and upper filtrations

This module transports Herbrand functions, upper ramification filtrations, and upper breaks along
algebra equivalences of `integralClosure` (`AlgEquiv.autCongr`) and along Galois fixed fields
(`IsGalois.normalAutEquivQuotient`).
-/

public section
noncomputable section

open IsLocalRing

namespace TauCeti.IsLocalRing

section IntegralClosure

variable {A K E E' : Type*} [CommRing A] [CommRing K] [CommRing E] [CommRing E'] [Algebra A K]
  [Algebra K E] [Algebra A E] [IsScalarTower A K E] [Algebra K E'] [Algebra A E']
  [IsScalarTower A K E'] [IsLocalRing (integralClosure A E)] [IsLocalRing (integralClosure A E')]
  (e : E ≃ₐ[K] E')

include e

/-- `e : E ≃ₐ[K] E'` over `A` preserves `herbrandFun` on `integralClosure`. -/
theorem _root_.AlgEquiv.herbrandFun_integralClosure_eq_of_algEquiv (u : ℝ) :
    herbrandFun (E ≃ₐ[K] E) (integralClosure A E) u =
      herbrandFun (E' ≃ₐ[K] E') (integralClosure A E') u :=
  herbrandFun_eq_of_ramificationGroup_eq_comap e.autCongr.bijective
    e.ramificationGroup_integralClosure_eq_comap_autCongr u

/-- `e : E ≃ₐ[K] E'` over `A` preserves `inverseHerbrandFun` on `integralClosure`. -/
theorem _root_.AlgEquiv.inverseHerbrandFun_integralClosure_eq_of_algEquiv (v : ℝ) :
    inverseHerbrandFun (E ≃ₐ[K] E) (integralClosure A E) v =
      inverseHerbrandFun (E' ≃ₐ[K] E') (integralClosure A E') v :=
  inverseHerbrandFun_eq_of_ramificationGroup_eq_comap e.autCongr.bijective
    e.ramificationGroup_integralClosure_eq_comap_autCongr v

/-- Conjugation `e.autCongr` pulls back `upperRamificationGroup` on `integralClosure`. -/
theorem _root_.AlgEquiv.upperRamificationGroup_integralClosure_eq_comap_autCongr (v : ℝ) :
    upperRamificationGroup (E ≃ₐ[K] E) (integralClosure A E) v =
      (upperRamificationGroup (E' ≃ₐ[K] E') (integralClosure A E') v).comap
        (e.autCongr : (E ≃ₐ[K] E) →* (E' ≃ₐ[K] E')) :=
  upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap e.autCongr.bijective
    e.ramificationGroup_integralClosure_eq_comap_autCongr v

/-- `e : E ≃ₐ[K] E'` over `A` preserves `UpperJump` on `integralClosure`. -/
theorem _root_.AlgEquiv.upperJump_integralClosure_iff_of_algEquiv (u : ℝ) :
    UpperJump (E ≃ₐ[K] E) (integralClosure A E) u ↔
      UpperJump (E' ≃ₐ[K] E') (integralClosure A E') u :=
  upperJump_iff_of_ramificationGroup_eq_comap e.autCongr.bijective
    e.ramificationGroup_integralClosure_eq_comap_autCongr u

end IntegralClosure

section FixedField

open _root_.IntermediateField

variable (A : Type*) {K L : Type*} [CommRing A] [Field K] [Field L] [Algebra A K] [Algebra K L]
  [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] [IsGalois K L]
  [IsLocalRing (integralClosure A L)] (H : Subgroup (L ≃ₐ[K] L)) [H.Normal]

/-- `herbrandFun` of `Gal(L/K) ⧸ H` on `(integralClosure A L)^H` agrees with `fixedField H`. -/
theorem herbrandFun_fixedPoints_integralClosure (u : ℝ) :
    herbrandFun ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) u =
      herbrandFun (fixedField H ≃ₐ[K] fixedField H) (integralClosure A (fixedField H)) u :=
  herbrandFun_eq_of_ramificationGroup_eq_comap (IsGalois.normalAutEquivQuotient H).bijective
    (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) u

/-- `inverseHerbrandFun` of `Gal(L/K) ⧸ H` on `(integralClosure A L)^H` matches `fixedField H`. -/
theorem inverseHerbrandFun_fixedPoints_integralClosure (v : ℝ) :
    inverseHerbrandFun ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) v =
      inverseHerbrandFun (fixedField H ≃ₐ[K] fixedField H) (integralClosure A (fixedField H)) v :=
  inverseHerbrandFun_eq_of_ramificationGroup_eq_comap (IsGalois.normalAutEquivQuotient H).bijective
    (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) v

/-- `IsGalois.normalAutEquivQuotient H` pulls back upper ramification groups from
`integralClosure A (fixedField H)` to `FixedPoints.subalgebra A (integralClosure A L) H`. -/
theorem upperRamificationGroup_fixedPoints_integralClosure_eq_comap (v : ℝ) :
    upperRamificationGroup ((L ≃ₐ[K] L) ⧸ H)
        (FixedPoints.subalgebra A (integralClosure A L) H) v =
      (upperRamificationGroup (fixedField H ≃ₐ[K] fixedField H)
          (integralClosure A (fixedField H)) v).comap
        (IsGalois.normalAutEquivQuotient H : _ →* _) :=
  upperRamificationGroup_eq_comap_of_ramificationGroup_eq_comap
    (IsGalois.normalAutEquivQuotient H).bijective
    (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) v

/-- `UpperJump` of `Gal(L/K) ⧸ H` on `(integralClosure A L)^H` agrees with `fixedField H`. -/
theorem upperJump_fixedPoints_integralClosure_iff (u : ℝ) :
    UpperJump ((L ≃ₐ[K] L) ⧸ H) (FixedPoints.subalgebra A (integralClosure A L) H) u ↔
      UpperJump (fixedField H ≃ₐ[K] fixedField H) (integralClosure A (fixedField H)) u :=
  upperJump_iff_of_ramificationGroup_eq_comap (IsGalois.normalAutEquivQuotient H).bijective
    (ramificationGroup_fixedPoints_integralClosure_eq_comap A H) u

end FixedField

end TauCeti.IsLocalRing
