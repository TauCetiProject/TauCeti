/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Restriction
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Restriction of exterior powers on schemes

Exterior powers of module sheaves commute with restriction along every open immersion.
The forward comparison sends a wedge of restricted sections to the restriction of their wedge.
It is the canonical pushforward comparison for the functor sending an open to its image,
with coefficient map the inverse structure-sheaf isomorphism. No quasicoherence, finiteness,
or flatness hypothesis is required.

The natural isomorphism is `TauCeti.AlgebraicGeometry.restrictExteriorPowerIso`;
`TauCeti.AlgebraicGeometry.restrictExteriorPowerIso_hom_app` identifies its forward map.

The unit of the restriction--pushforward adjunction is compatible with this comparison and with
the pushforward comparison (`TauCeti.AlgebraicGeometry.restrictAdjunction_unit_app_exteriorPower`).
Consequently, along an open immersion `j` the canonical pullback comparison
`j^* (⋀ⁿ M) ⟶ ⋀ⁿ (j^* M)` is the inverse of the restriction isomorphism, read through the
identification of restriction with pullback
(`TauCeti.AlgebraicGeometry.pullbackExteriorPowerComparison_app_of_isOpenImmersion`), and so it
is invertible for every sheaf of modules
(`TauCeti.AlgebraicGeometry.isIso_pullbackExteriorPowerComparison_app_of_isOpenImmersion`).

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

-- Adapted from `AlgebraicGeometry.Scheme.Modules.restrictSymmetricPowerIso`.
/-- Exterior powers commute with restriction along an open immersion, naturally in the module
sheaf. The forward map is the canonical exterior-power pushforward comparison. -/
def restrictExteriorPowerIso (n : ℕ) :
    restrictFunctor f ⋙ _root_.SheafOfModules.exteriorPower X.sheaf n ≅
      _root_.SheafOfModules.exteriorPower Y.sheaf n ⋙ restrictFunctor f :=
  @asIso _ _ _ _ (TauCeti.SheafOfModules.pushforwardExteriorPowerComparison
    (restrictRingCatSheafHom f) n)
    -- The scheme and generic site sheaf categories have different instance heads;
    -- pass the coefficient-map isomorphism explicitly.
    (@TauCeti.SheafOfModules.isIso_pushforwardExteriorPowerComparison
      _ _ _ _ _ _ _ _ _ _ _ _ f.opensFunctor _ X.sheaf Y.sheaf
      (restrictRingCatSheafHom f) inferInstance
      (isIso_restrictRingCatSheafHom f) n)

/-- The forward restriction isomorphism is the canonical pushforward comparison. -/
-- Keep this equation named: expanding the forward map would obstruct simplification by the
-- generic isomorphism inverse laws in importing modules.
theorem restrictExteriorPowerIso_hom_app (n : ℕ) (M : Y.Modules) :
    (restrictExteriorPowerIso f n).hom.app M =
      (TauCeti.SheafOfModules.pushforwardExteriorPowerComparison
        (restrictRingCatSheafHom f) n).app M :=
  (rfl)

-- Adapted from `AlgebraicGeometry.Scheme.Modules.restrictAdjunction_unit_app_symmetricPower`.
/-- The unit `M ⟶ f_* (M|_X)` of the restriction--pushforward adjunction along an open
immersion is compatible with the exterior-power comparisons of pushforward and restriction. -/
theorem restrictAdjunction_unit_app_exteriorPower (n : ℕ) (M : Y.Modules) :
    (restrictAdjunction f).unit.app ((_root_.SheafOfModules.exteriorPower Y.sheaf n).obj M) =
      (_root_.SheafOfModules.exteriorPower Y.sheaf n).map ((restrictAdjunction f).unit.app M) ≫
        (TauCeti.SheafOfModules.pushforwardExteriorPowerComparison f.toRingCatSheafHom n).app
          (M.restrict f) ≫
        (pushforward f).map ((restrictExteriorPowerIso f n).hom.app M) := by
  rw [restrictExteriorPowerIso_hom_app]
  -- As in `restrictAdjunction_unit_app_tensor`, the adjunction of opens is stated for
  -- `IsOpenMap.functor`, which is `f.opensFunctor`; `show` restates it in the form the sheaf-level
  -- lemma unifies with `restrictAdjunction f`.
  exact TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_exteriorPower
    (show f.opensFunctor ⊣ TopologicalSpace.Opens.map f.base from
      f.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom f) f.toRingCatSheafHom
    _ _ n M

end

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

-- Adapted from `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_app_of_isOpenImmersion`.
/-- Along an open immersion `j`, the canonical comparison `j^* (⋀ⁿ M) ⟶ ⋀ⁿ (j^* M)` is the
inverse of the restriction isomorphism `⋀ⁿ (M|_U) ≅ (⋀ⁿ M)|_U`, read through the
identification `Scheme.Modules.restrictFunctorIsoPullback` of restriction with pullback. -/
theorem pullbackExteriorPowerComparison_app_of_isOpenImmersion (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullbackExteriorPowerComparison j n).app M =
      (restrictFunctorIsoPullback j).inv.app
          ((_root_.SheafOfModules.exteriorPower Y.sheaf n).obj M) ≫
        (restrictExteriorPowerIso j n).inv.app M ≫
        (_root_.SheafOfModules.exteriorPower U.sheaf n).map
          ((restrictFunctorIsoPullback j).hom.app M) := by
  -- Compare transposes under the pullback--pushforward adjunction `A`. The transpose of the
  -- comparison is `⋀ⁿ` of the unit followed by the pushforward comparison `q`. On the right,
  -- the units of `A` and of the restriction adjunction `B` differ by the identification `e` of
  -- restriction with pullback, and the unit of `B` factors through `q` and the restriction
  -- isomorphism `r`.
  let A := pullbackPushforwardAdjunction j
  let B := restrictAdjunction j
  let P : U.Modules ⥤ Y.Modules := pushforward j
  let W₁ : Y.Modules ⥤ Y.Modules := _root_.SheafOfModules.exteriorPower Y.sheaf n
  let W₂ : U.Modules ⥤ U.Modules := _root_.SheafOfModules.exteriorPower U.sheaf n
  let q : P ⋙ W₁ ⟶ W₂ ⋙ P :=
    TauCeti.SheafOfModules.pushforwardExteriorPowerComparison j.toRingCatSheafHom n
  let e : restrictFunctor j ≅ pullback j := restrictFunctorIsoPullback j
  let r : restrictFunctor j ⋙ W₂ ≅ W₁ ⋙ restrictFunctor j := restrictExteriorPowerIso j n
  have h₁ : A.unit.app (W₁.obj M) ≫
      P.map ((Scheme.Modules.pullbackExteriorPowerComparison j n).app M) =
      W₁.map (A.unit.app M) ≫ q.app _ :=
    Scheme.Modules.unit_comp_pushforward_map_pullbackExteriorPowerComparison_app j n M
  have h₂ : B.unit.app (W₁.obj M) = W₁.map (B.unit.app M) ≫ q.app _ ≫ P.map (r.hom.app M) :=
    restrictAdjunction_unit_app_exteriorPower j n M
  have hA : A.unit.app (W₁.obj M) ≫ P.map (e.inv.app (W₁.obj M)) = B.unit.app (W₁.obj M) :=
    Adjunction.unit_leftAdjointUniq_hom_app A B (W₁.obj M)
  have hB : B.unit.app M ≫ P.map (e.hom.app M) = A.unit.app M :=
    Adjunction.unit_leftAdjointUniq_hom_app B A M
  have hq : W₁.map (P.map (e.hom.app M)) ≫ q.app _ = q.app _ ≫ P.map (W₂.map (e.hom.app M)) :=
    q.naturality (e.hom.app M)
  have hr : P.map (r.hom.app M) ≫ P.map (r.inv.app M) = 𝟙 _ :=
    (P.mapIso (r.app M)).hom_inv_id
  have key : W₁.map (A.unit.app M) ≫ q.app _ =
      A.unit.app (W₁.obj M) ≫ P.map (e.inv.app (W₁.obj M) ≫ r.inv.app M ≫ W₂.map (e.hom.app M)) :=
    calc W₁.map (A.unit.app M) ≫ q.app _
        = W₁.map (B.unit.app M) ≫ q.app _ ≫ P.map (W₂.map (e.hom.app M)) := by
          rw [← hB, Functor.map_comp, Category.assoc, hq]
      _ = B.unit.app (W₁.obj M) ≫ P.map (r.inv.app M) ≫ P.map (W₂.map (e.hom.app M)) := by
          rw [h₂, Category.assoc, Category.assoc, reassoc_of% hr]
      _ = _ := by rw [← hA, P.map_comp, P.map_comp, Category.assoc]
  exact (A.homEquiv _ _).injective ((A.homEquiv_unit _ _ _).trans
    (h₁.trans (key.trans (A.homEquiv_unit _ _ _).symm)))

/-- Along an open immersion the canonical exterior-power comparison is invertible for every
sheaf of modules. -/
instance isIso_pullbackExteriorPowerComparison_app_of_isOpenImmersion (n : ℕ) (M : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackExteriorPowerComparison j n).app M) := by
  rw [pullbackExteriorPowerComparison_app_of_isOpenImmersion]
  exact Iso.isIso_hom ((restrictFunctorIsoPullback j).symm.app _ ≪≫
    (restrictExteriorPowerIso j n).symm.app M ≪≫
    (_root_.SheafOfModules.exteriorPower U.sheaf n).mapIso ((restrictFunctorIsoPullback j).app M))

end

end TauCeti.AlgebraicGeometry
