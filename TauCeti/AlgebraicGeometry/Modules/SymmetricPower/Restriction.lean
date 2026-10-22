/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Basic

/-!
# Restriction of symmetric powers on schemes

Symmetric powers of module sheaves commute with restriction along every open immersion.
The comparison is the canonical pushforward comparison for the functor sending an open to
its image; its coefficient map is the inverse of the structure-sheaf isomorphism on that open.
No quasicoherence hypothesis is required. The unit of the restriction--pushforward adjunction
is compatible with this comparison and with the pushforward comparison
(`Scheme.Modules.restrictAdjunction_unit_app_symmetricPower`).

Consequently, along an open immersion `j` the canonical pullback comparison
`j^* (Symⁿ M) ⟶ Symⁿ (j^* M)` is the inverse of the restriction isomorphism, read through the
identification of restriction with pullback
(`TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_app_of_isOpenImmersion`), and so it
is invertible for every sheaf of modules
(`TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_app_of_isOpenImmersion`).
-/

public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Symmetric powers commute with restriction along an open immersion, naturally in the
module sheaf. The forward map is the canonical symmetric-power pushforward comparison. -/
def restrictSymmetricPowerIso (n : ℕ) :
    restrictFunctor f ⋙ SheafOfModules.symmetricPower X.sheaf n ≅
      SheafOfModules.symmetricPower Y.sheaf n ⋙ restrictFunctor f :=
  @asIso _ _ _ _ (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison
    (restrictRingCatSheafHom f) n)
    -- The scheme sheaf category and the generic site sheaf category have different
    -- instance heads; pass the same coefficient-map isomorphism explicitly.
    (@TauCeti.SheafOfModules.isIso_pushforwardSymmetricPowerComparison
      _ _ _ _ _ _ _ _ _ _ _ _ f.opensFunctor _ X.sheaf Y.sheaf
      (restrictRingCatSheafHom f) inferInstance (isIso_restrictRingCatSheafHom f) n)

/-- The forward restriction isomorphism is the canonical pushforward comparison. -/
-- Keep this equation named: expanding the forward map prevents the generic isomorphism
-- inverse laws from matching in ordinary importing simplification.
theorem restrictSymmetricPowerIso_hom_app (n : ℕ) (M : Y.Modules) :
    (restrictSymmetricPowerIso f n).hom.app M =
      (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison
        (restrictRingCatSheafHom f) n).app M :=
  (rfl)

/-- The unit `M ⟶ f_* (M|_X)` of the restriction--pushforward adjunction along an open
immersion is compatible with the symmetric-power comparisons of pushforward and restriction. -/
theorem restrictAdjunction_unit_app_symmetricPower (n : ℕ) (M : Y.Modules) :
    (restrictAdjunction f).unit.app ((SheafOfModules.symmetricPower Y.sheaf n).obj M) =
      (SheafOfModules.symmetricPower Y.sheaf n).map ((restrictAdjunction f).unit.app M) ≫
        (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison f.toRingCatSheafHom n).app
          (M.restrict f) ≫
        (pushforward f).map ((restrictSymmetricPowerIso f n).hom.app M) := by
  rw [restrictSymmetricPowerIso_hom_app]
  -- As in `restrictAdjunction_unit_app_tensor`, the adjunction of opens is stated for
  -- `IsOpenMap.functor`, which is `f.opensFunctor`; `show` restates it in the form the sheaf-level
  -- lemma unifies with `restrictAdjunction f`.
  exact TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_symmetricPower
    (show f.opensFunctor ⊣ TopologicalSpace.Opens.map f.base from
      f.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom f) f.toRingCatSheafHom
    _ _ n M

end AlgebraicGeometry.Scheme.Modules

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

variable {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]

/-- Along an open immersion `j`, the canonical comparison `j^* (Symⁿ M) ⟶ Symⁿ (j^* M)` is the
inverse of the restriction isomorphism `Symⁿ (M|_U) ≅ (Symⁿ M)|_U`, read through the
identification `Scheme.Modules.restrictFunctorIsoPullback` of restriction with pullback. -/
theorem pullbackSymmetricPowerComparison_app_of_isOpenImmersion (n : ℕ) (M : Y.Modules) :
    (Scheme.Modules.pullbackSymmetricPowerComparison j n).app M =
      (Scheme.Modules.restrictFunctorIsoPullback j).inv.app
          ((_root_.SheafOfModules.symmetricPower Y.sheaf n).obj M) ≫
        (Scheme.Modules.restrictSymmetricPowerIso j n).inv.app M ≫
        (_root_.SheafOfModules.symmetricPower U.sheaf n).map
          ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app M) := by
  -- Compare transposes under the pullback--pushforward adjunction `A`. The transpose of the
  -- comparison is `Symⁿ` of the unit followed by the pushforward comparison `q`. On the right,
  -- the units of `A` and of the restriction adjunction `B` differ by the identification `e` of
  -- restriction with pullback, and the unit of `B` factors through `q` and the restriction
  -- isomorphism `r`.
  let A := Scheme.Modules.pullbackPushforwardAdjunction j
  let B := Scheme.Modules.restrictAdjunction j
  let P : U.Modules ⥤ Y.Modules := Scheme.Modules.pushforward j
  let W₁ : Y.Modules ⥤ Y.Modules := _root_.SheafOfModules.symmetricPower Y.sheaf n
  let W₂ : U.Modules ⥤ U.Modules := _root_.SheafOfModules.symmetricPower U.sheaf n
  let q : P ⋙ W₁ ⟶ W₂ ⋙ P :=
    SheafOfModules.pushforwardSymmetricPowerComparison j.toRingCatSheafHom n
  let e : Scheme.Modules.restrictFunctor j ≅ Scheme.Modules.pullback j :=
    Scheme.Modules.restrictFunctorIsoPullback j
  let r : Scheme.Modules.restrictFunctor j ⋙ W₂ ≅ W₁ ⋙ Scheme.Modules.restrictFunctor j :=
    Scheme.Modules.restrictSymmetricPowerIso j n
  have h₁ : A.unit.app (W₁.obj M) ≫
      P.map ((Scheme.Modules.pullbackSymmetricPowerComparison j n).app M) =
      W₁.map (A.unit.app M) ≫ q.app _ :=
    Scheme.Modules.unit_comp_pushforward_map_pullbackSymmetricPowerComparison_app j n M
  have h₂ : B.unit.app (W₁.obj M) = W₁.map (B.unit.app M) ≫ q.app _ ≫ P.map (r.hom.app M) :=
    Scheme.Modules.restrictAdjunction_unit_app_symmetricPower j n M
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

/-- Along an open immersion the canonical symmetric-power comparison is invertible for every
sheaf of modules. -/
instance isIso_pullbackSymmetricPowerComparison_app_of_isOpenImmersion (n : ℕ) (M : Y.Modules) :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison j n).app M) := by
  rw [pullbackSymmetricPowerComparison_app_of_isOpenImmersion]
  exact Iso.isIso_hom ((Scheme.Modules.restrictFunctorIsoPullback j).symm.app _ ≪≫
    (Scheme.Modules.restrictSymmetricPowerIso j n).symm.app M ≪≫
    (_root_.SheafOfModules.symmetricPower U.sheaf n).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app M))

end TauCeti.AlgebraicGeometry
