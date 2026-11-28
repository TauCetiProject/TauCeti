/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Affine.Basic
public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Affine.RestrictScalars

/-!
# Coherent formal modules on the formal completion of an affine scheme

Let `R` be a commutative ring and `J` an ideal of `R`. Combining
`TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Affine.Basic` and
`TauCeti.AlgebraicGeometry.AdicThickeningSystem.CoherentFormalModule.Affine.RestrictScalars`, this
file provides the Noetherian specialization `coherentFormalModuleEquivSpec` (Stacks, Lemma 30.23.1)
for any ideal `J` of a Noetherian ring `R`, along with its section-tower and `restrictScalars`
comparison isomorphisms.

## Main definitions

* `AlgebraicGeometry.Scheme.formalCompletion.coherentFormalModuleEquivSpec`:
  equivalence `FGModuleCat (AdicCompletion J R) ≌ CoherentFormalModule ((Spec R)/V(J))` for a
  Noetherian ring `R` (Stacks, Lemma 30.23.1).
* `coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso`:
  identification of the underlying `R`-module of the inverse functor with `specSectionsLim J`.

## References

* [Stacks Project, Lemma 30.23.1](https://stacks.math.columbia.edu/tag/087W).
-/

public section

open CategoryTheory Opposite AlgebraicGeometry
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.AdicThickeningSystem

universe u

namespace AlgebraicGeometry.Scheme.formalCompletion

noncomputable section

variable {R : Type u} [CommRing R]

/-- **Coherent formal modules on `(Spec R)/V(J)` over a Noetherian ring** (Stacks, Lemma 30.23.1):
for any ideal `J` of a Noetherian ring `R`, coherent formal modules on the formal completion of
`Spec R` along `V(J)` are equivalent to finite modules over the `J`-adic completion
`AdicCompletion J R`. -/
-- `@[expose]` is forced by dependent typing: the inverse module must reduce to the limit in the
-- type of `coherentFormalModuleEquivSpecInverseCompFiniteReductionIso_hom_app_reductionπ`.
@[expose, stacks 087W]
def coherentFormalModuleEquivSpec (J : Ideal R) [IsNoetherianRing R] :
    FGModuleCat.{u} (AdicCompletion J R) ≌
      CoherentFormalModule
        ((Spec (CommRingCat.of R)).formalCompletion
          (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))) :=
  coherentFormalModuleEquivSpecOfFG J (IsNoetherian.noetherian J)

/-- `coherentFormalModuleEquivSpec J` preserves addition of morphisms. -/
instance (J : Ideal R) [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).functor.Additive := by
  have fg : J.FG := IsNoetherian.noetherian J
  exact inferInstanceAs (coherentFormalModuleEquivSpecOfFG J fg).functor.Additive

/-- The inverse of `coherentFormalModuleEquivSpec J` transports along
`(specIsoSpfCompletion J _).inv` and takes the inverse limit of levelwise global sections over
the completed ring. -/
@[simp]
theorem coherentFormalModuleEquivSpec_inverse (J : Ideal R) [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).inverse =
      CoherentFormalModule.pullback (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv ⋙
        @CoherentFormalModule.finiteSectionsLim _ _
          (AdicRing.completion J (IsNoetherian.noetherian J)).ideal
          (AdicCompletion.isAdicComplete_self J (IsNoetherian.noetherian J)).toIsPrecomplete :=
  coherentFormalModuleEquivSpecOfFG_inverse J (IsNoetherian.noetherian J)

/-- Under `coherentFormalModuleEquivSpec J`, transporting the coherent formal module associated to
a finite `AdicCompletion J R`-module `M` along `(specIsoSpfCompletion J _).inv` has
global-sections tower naturally isomorphic to the reduction tower of `M` over the completed ring. -/
def coherentFormalModuleEquivSpecFunctorCompFiniteSectionsTowerIso (J : Ideal R)
    [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).functor ⋙
        CoherentFormalModule.pullback (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv ⋙
          CoherentFormalModule.finiteSectionsTower
            (AdicRing.completion J (IsNoetherian.noetherian J)).ideal ≅
      TauCeti.ModuleTower.finiteReduction
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal :=
  coherentFormalModuleEquivSpecOfFGFunctorCompFiniteSectionsTowerIso J (IsNoetherian.noetherian J)

/-- Under `coherentFormalModuleEquivSpec J`, the reduction tower of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module on `(Spec R)/V(J)` is
naturally isomorphic to the global-sections tower over the completed ring. -/
def coherentFormalModuleEquivSpecInverseCompFiniteReductionIso (J : Ideal R)
    [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).inverse ⋙
        TauCeti.ModuleTower.finiteReduction
          (AdicRing.completion J (IsNoetherian.noetherian J)).ideal ≅
      CoherentFormalModule.pullback (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv ⋙
        CoherentFormalModule.finiteSectionsTower
          (AdicRing.completion J (IsNoetherian.noetherian J)).ideal :=
  coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso J (IsNoetherian.noetherian J)

/-- The reductions-to-sections comparison for `coherentFormalModuleEquivSpec J` is induced by the
projections from the inverse limit over the completed ring. -/
@[simp]
theorem coherentFormalModuleEquivSpecInverseCompFiniteReductionIso_hom_app_reductionπ
    (J : Ideal R) [IsNoetherianRing R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower
      (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
      ((CoherentFormalModule.pullback
        (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).lim) :
    dsimp% only [CategoryTheory.Functor.comp_obj, CategoryTheory.ObjectProperty.ι_obj,
      FGModuleCat.obj_carrier]
    (((coherentFormalModuleEquivSpecInverseCompFiniteReductionIso J).hom.app M).hom.app
      (op n)).hom
      (TauCeti.ModuleTower.reductionπ
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal
        ((coherentFormalModuleEquivSpec J).inverse.obj M).obj n x) =
      ((CoherentFormalModule.sectionsTower
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
        ((CoherentFormalModule.pullback
          (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).limπ n x :=
  coherentFormalModuleEquivSpecOfFGInverseCompFiniteReductionIso_hom_app_reductionπ
    J (IsNoetherian.noetherian J) M n x

/-- Under `coherentFormalModuleEquivSpec J`, the underlying `R`-module of the finite
`AdicCompletion J R`-module corresponding to a coherent formal module `M` on `(Spec R)/V(J)` is
naturally isomorphic to `specSectionsLim J`, derived from
`coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso`. -/
def coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso (J : Ideal R)
    [IsNoetherianRing R] :
    (coherentFormalModuleEquivSpec J).inverse ⋙
        (ModuleCat.isFG (AdicCompletion J R)).ι ⋙
          ModuleCat.restrictScalars (algebraMap R (AdicCompletion J R)) ≅
      specSectionsLim J :=
  coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso J (IsNoetherian.noetherian J)

/-- On level-`n` projections, the inverse of
`coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J` pulls a global section back along
`(Spf.completionIso J _).hom.app n` and applies the pullback coherence isomorphism. -/
theorem coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso_inv_app_limπ
    (J : Ideal R) [IsNoetherianRing R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ) (y : ((specSectionsTower J).obj M).lim) :
    ((CoherentFormalModule.sectionsTower
        (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
        ((CoherentFormalModule.pullback
          (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).limπ n
      ((coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J).inv.app M y) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp
            (Spf.completionIso J (IsNoetherian.noetherian J)).hom
            (specIso J).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (specIsoSpfCompletion_inv J (IsNoetherian.noetherian J)).symm).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J (IsNoetherian.noetherian J)).hom.app n)).unit.app
            (((CoherentFormalModule.pullback (specIso J).inv).obj M).obj n))
          (((specSectionsTower J).obj M).limπ n y)) :=
  coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_inv_app_limπ
    J (IsNoetherian.noetherian J) M n y

/-- On level-`n` projections, `coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J` pulls
a global section back along `(Spf.completionIso J _).inv.app n` and applies the pullback coherence
isomorphism. -/
theorem coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso_hom_app_limπ
    (J : Ideal R) [IsNoetherianRing R]
    (M : CoherentFormalModule ((Spec (CommRingCat.of R)).formalCompletion
      (IdealSheafData.ofIdealTop (J.map (ΓSpecIso (CommRingCat.of R)).inv.hom))))
    (n : ℕ)
    (x : ((CoherentFormalModule.sectionsTower
      (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
      ((CoherentFormalModule.pullback
        (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).lim) :
    ((specSectionsTower J).obj M).limπ n
      ((coherentFormalModuleEquivSpecInverseCompRestrictScalarsIso J).hom.app M x) =
      moduleSpecΓFunctor.map
        (((CoherentFormalModule.pullbackComp
            (Spf.completionIso J (IsNoetherian.noetherian J)).inv
            (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).hom.app M).app n ≫
          ((CoherentFormalModule.pullbackCongr
            (completionIso_inv_comp_specIsoSpfCompletion_inv J
              (IsNoetherian.noetherian J))).hom.app M).app n)
        (moduleSpecΓFunctor.map
          ((Scheme.Modules.pullbackPushforwardAdjunction
            ((Spf.completionIso J (IsNoetherian.noetherian J)).inv.app n)).unit.app
            (((CoherentFormalModule.pullback
              (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M).obj n))
          (((CoherentFormalModule.sectionsTower
            (AdicRing.completion J (IsNoetherian.noetherian J)).ideal).obj
            ((CoherentFormalModule.pullback
              (specIsoSpfCompletion J (IsNoetherian.noetherian J)).inv).obj M)).limπ n x)) :=
  coherentFormalModuleEquivSpecOfFGInverseCompRestrictScalarsIso_hom_app_limπ
    J (IsNoetherian.noetherian J) M n x

end

end AlgebraicGeometry.Scheme.formalCompletion
