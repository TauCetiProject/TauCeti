/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Pushforward.Basic

/-!
# Affine pushforward and restriction of scalars

For a ring map `φ : R → S`, the sheaf associated with an `S`-module considered as an
`R`-module is canonically the pushforward of its associated sheaf along `Spec φ`.
This identifies module sequences obtained by restriction of scalars with sequences
of direct-image sheaves, for example the normalization sequence of an affine curve.

The comparison uses Mathlib's `Scheme.Modules.fromTildeΓ` and the global-sections
comparison `pushforwardCompModuleSpecΓFunctorIso`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2(d).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat.{u} S)

/-- Associated sheaves turn restriction of scalars into direct image along a
morphism of affine schemes. -/
def tildeRestrictScalarsIsoPushforward :
    tilde ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M) := by
  have h : IsIso (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) :=
    isIso_fromTildeΓ_pushforward φ (tilde M)
  exact (tilde.functor R).mapIso
      ((ModuleCat.restrictScalars φ.hom).mapIso ((tilde.toTildeΓNatIso (R := S)).app M)) ≪≫
    (tilde.functor R).mapIso
      (((pushforwardCompModuleSpecΓFunctorIso φ).app (tilde M)).symm) ≪≫
    @asIso _ _ _ _ (Scheme.Modules.fromTildeΓ (R := R)
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M))) h

/-- The affine pushforward comparison preserves the global section associated
with an element of the module. -/
@[simp]
theorem tildeRestrictScalarsIsoPushforward_hom_toOpen (m : M) :
    ((tildeRestrictScalarsIsoPushforward φ M).hom.val.app (.op ⊤))
        (tilde.toOpen ((ModuleCat.restrictScalars φ.hom).obj M) ⊤ m) =
      tilde.toOpen M ⊤ m := by
  unfold tildeRestrictScalarsIsoPushforward
  -- Scheme modules and the underlying sheaves have definitionally equal category
  -- structures, but rewriting through their projections requires full transparency.
  erw [Iso.trans_hom, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    Functor.mapIso_hom, Iso.symm_hom, asIso_hom, SheafOfModules.comp_val,
    PresheafOfModules.comp_app]
  erw [asIso_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have h₁ := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app
      ((ModuleCat.restrictScalars φ.hom).map ((tilde.toTildeΓNatIso (R := S)).hom.app M)) ⊤) m
  erw [h₁, ConcreteCategory.comp_apply]
  have h₂ := ConcreteCategory.congr_hom
    (tilde.toOpen_map_app ((pushforwardCompModuleSpecΓFunctorIso φ).app (tilde M)).inv ⊤)
    (((ModuleCat.restrictScalars φ.hom).map ((tilde.toTildeΓNatIso (R := S)).hom.app M)) m)
  erw [h₂, ConcreteCategory.comp_apply]
  have h₃ := ConcreteCategory.congr_hom
    (Scheme.Modules.toOpen_fromTildeΓ_app
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde M)) ⊤)
    (((pushforwardCompModuleSpecΓFunctorIso φ).app (tilde M)).inv
      (((ModuleCat.restrictScalars φ.hom).map ((tilde.toTildeΓNatIso (R := S)).hom.app M)) m))
  erw [h₃]
  simp only [homOfLE_refl, op_id, Functor.comp_obj, Iso.app_inv, Functor.id_obj]
  exact pushforwardCompModuleSpecΓFunctorIso_inv_app_apply φ (tilde M)
    (((ModuleCat.restrictScalars φ.hom).map ((tilde.toTildeΓNatIso (R := S)).hom.app M)) m)

end TauCeti.AlgebraicGeometry
