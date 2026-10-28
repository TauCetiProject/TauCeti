/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Pullback

/-!
# Pullback comparison for symmetric powers of modules on schemes

For a morphism of schemes `f : X ⟶ Y`, this file specializes the sheaf-theoretic comparison to
the canonical natural map `f^* (Symⁿ M) ⟶ Symⁿ (f^* M)`. Its transpose is characterized by the
pullback--pushforward adjunction equation. In degree one the comparison is an isomorphism.

The comparison is the input for proving that symmetric powers commute with pullback on
quasicoherent modules. That stronger invertibility statement in arbitrary degree requires the
affine calculation and descent; it is proved in
`TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Quasicoherent`.

## Main declaration

* `AlgebraicGeometry.Scheme.Modules.pullbackSymmetricPowerComparison`: the canonical comparison
  between pullback and symmetric power.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical comparison `f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` for modules on schemes, obtained
from the sheaf comparison along `f.toRingCatSheafHom`. -/
def pullbackSymmetricPowerComparison (n : ℕ) :
    SheafOfModules.symmetricPower Y.sheaf n ⋙ pullback f ⟶
      pullback f ⋙ SheafOfModules.symmetricPower X.sheaf n :=
  TauCeti.SheafOfModules.pullbackSymmetricPowerComparison
    (pullbackPushforwardAdjunction f) n

/-- The scheme comparison is the sheaf comparison for the scheme pullback adjunction. -/
theorem pullbackSymmetricPowerComparison_eq (n : ℕ) :
    pullbackSymmetricPowerComparison f n =
      TauCeti.SheafOfModules.pullbackSymmetricPowerComparison
        (pullbackPushforwardAdjunction f) n :=
  (rfl)

/-- The mate of the scheme comparison under the pullback--pushforward adjunction is the
pushforward comparison along `f.toRingCatSheafHom`. -/
-- Not a simp lemma: `mateEquiv_apply` expands its left-hand side first.
theorem mateEquiv_pullbackSymmetricPowerComparison (n : ℕ) :
    mateEquiv (pullbackPushforwardAdjunction f) (pullbackPushforwardAdjunction f)
        (pullbackSymmetricPowerComparison f n) =
      TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison f.toRingCatSheafHom n :=
  TauCeti.SheafOfModules.mateEquiv_pullbackSymmetricPowerComparison
    (pullbackPushforwardAdjunction f) n

/-- The adjunction equation characterizing the pullback comparison for modules on schemes. -/
theorem unit_comp_pushforward_map_pullbackSymmetricPowerComparison_app
    (n : ℕ) (M : Y.Modules) :
    (pullbackPushforwardAdjunction f).unit.app
        ((SheafOfModules.symmetricPower Y.sheaf n).obj M) ≫
      (pushforward f).map ((pullbackSymmetricPowerComparison f n).app M) =
    (SheafOfModules.symmetricPower Y.sheaf n).map
        ((pullbackPushforwardAdjunction f).unit.app M) ≫
      (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison
        f.toRingCatSheafHom n).app ((pullback f).obj M) :=
  TauCeti.SheafOfModules.unit_comp_pushforward_pullbackSymmetricPowerComparison
    (pullbackPushforwardAdjunction f) n M

/-- In degree one, the pullback comparison is the identity of `f^* M`, read through the
identifications `Sym¹ M ≅ M`. -/
theorem pullbackSymmetricPowerComparison_app_comp_symmetricPowerOneIso (M : Y.Modules) :
    (pullbackSymmetricPowerComparison f 1).app M ≫
        (SheafOfModules.symmetricPowerOneIso X.sheaf).hom.app ((pullback f).obj M) =
      (pullback f).map ((SheafOfModules.symmetricPowerOneIso Y.sheaf).hom.app M) :=
  TauCeti.SheafOfModules.pullbackSymmetricPowerComparison_app_comp_symmetricPowerOneIso
    (pullbackPushforwardAdjunction f) M

/-- The pullback comparison for modules on schemes is an isomorphism in degree one. -/
instance isIso_pullbackSymmetricPowerComparison_one :
    IsIso (pullbackSymmetricPowerComparison f 1) :=
  TauCeti.SheafOfModules.isIso_pullbackSymmetricPowerComparison_one
    (pullbackPushforwardAdjunction f)

end

end AlgebraicGeometry.Scheme.Modules
