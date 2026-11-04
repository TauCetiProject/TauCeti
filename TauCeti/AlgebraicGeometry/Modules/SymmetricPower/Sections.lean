/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.LocallyBijective
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Quasicoherent

/-!
# Sections of symmetric powers over affine opens

For a quasi-coherent `𝒪_X`-module `M` on a scheme `X` and an affine open `U`, the sections of the
symmetric power `Symⁿ M` over `U` are the `n`-th symmetric power of the `Γ(X, U)`-module of
sections of `M` over `U`:

`Symⁿ_{Γ(X, U)} Γ(M, U) ≃ Γ(Symⁿ M, U)`.

The map is the canonical one: `Symⁿ M` is the sheafification of the presheaf of modules
`V ↦ Symⁿ_{Γ(X, V)} Γ(M, V)`, and the map is the sheafification unit at `U`. No finiteness,
freeness or flatness assumption on `M` is needed.

It is an instance of `AlgebraicGeometry.IsAffineOpen.bijective_app_of_isLocalizedModule`, since the
restrictions of the sectionwise symmetric powers from `U` to its basic opens are localizations
(`Scheme.Modules.isLocalizedModule_symmetricPower_map_basicOpen`). This extends the affine
computation `TauCeti.AlgebraicGeometry.tildeSymmetricPowerIso` on `Spec R` to the sections
over every affine open of an arbitrary scheme. The modules `Γ(Symⁿ M, U)` are the homogeneous
components of the graded ring of sections over `U` of the graded symmetric algebra of `M`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bijective_symmetricPower_unit_app`: the sheafification unit
  `Symⁿ_{Γ(X, U)} Γ(M, U) → Γ(Symⁿ M, U)` is bijective for quasi-coherent `M` and affine `U`;
* `AlgebraicGeometry.Scheme.Modules.symmetricPowerSectionsIso`: the resulting isomorphism of
  `Γ(X, U)`-modules, characterized by `symmetricPowerSectionsIso_hom_apply`; it is natural in `M`
  (`symmetricPowerSectionsIso_hom_naturality`) and compatible with restriction to smaller affine
  opens (`symmetricPowerSectionsIso_hom_restrict`).

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.2 and Exercise II.5.16.
-/

public section

open CategoryTheory Opposite

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}

/-- **Sections of symmetric powers over affine opens.** For a quasi-coherent `M` and an affine
open `U`, the sheafification unit `Symⁿ_{Γ(X, U)} Γ(M, U) → Γ(Symⁿ M, U)` is bijective. -/
theorem bijective_symmetricPower_unit_app (hU : IsAffineOpen U) (n : ℕ) :
    Function.Bijective
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val)).app
          (op U)) := by
  let P := (PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val
  let S : X.Modules := (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P
  have : S.IsQuasicoherent := (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (SheafOfModules.symmetricPowerIso n M) inferInstance
  let η : P ⟶ S.val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map η) :=
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 X.ringCatSheaf.obj) P).symm ▸
      Presheaf.isLocallyInjective_toSheafify' (J := Opens.grothendieckTopology X) P.presheaf
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map η) :=
    (PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app
      (𝟙 X.ringCatSheaf.obj) P).symm ▸
      Presheaf.isLocallySurjective_toSheafify' (J := Opens.grothendieckTopology X) P.presheaf
  exact hU.bijective_app_of_isLocalizedModule (M := S) η fun f ↦
    M.isLocalizedModule_symmetricPower_map_basicOpen hU f n

/-- **Sections of symmetric powers over affine opens.** For a quasi-coherent `M` and an affine
open `U`, the isomorphism of `Γ(X, U)`-modules `Symⁿ_{Γ(X, U)} Γ(M, U) ≅ Γ(Symⁿ M, U)` given by the
sheafification unit of the sectionwise symmetric power (`symmetricPowerSectionsIso_hom_apply`). -/
def symmetricPowerSectionsIso (hU : IsAffineOpen U) (n : ℕ) :
    (PresheafOfModulesOfCommRing.obj (R := X.presheaf) M.val (op U)).symmetricPower n ≅
      (sectionsFunctor U).obj ((SheafOfModules.symmetricPower X.sheaf n).obj M) :=
  (LinearEquiv.ofBijective
    (PresheafOfModules.Hom.app' (R := X.presheaf)
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val)) (op U)).hom
    (M.bijective_symmetricPower_unit_app hU n)).toModuleIso ≪≫
  (sectionsFunctor U).mapIso (SheafOfModules.symmetricPowerIso n M).symm

/-- The isomorphism `symmetricPowerSectionsIso` is the sheafification unit of the sectionwise
symmetric power, followed by the defining identification `SheafOfModules.symmetricPowerIso` of the
symmetric power with that sheafification. -/
@[simp]
lemma symmetricPowerSectionsIso_hom_apply (hU : IsAffineOpen U) (n : ℕ)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) M.val (op U)).symmetricPower n) :
    (M.symmetricPowerSectionsIso hU n).hom x =
      (SheafOfModules.symmetricPowerIso n M).inv.val.app (op U)
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          ((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val)).app
            (op U) x) :=
  -- The hom of the composite isomorphism is the sheafification unit at `U` (the underlying map
  -- of `LinearEquiv.ofBijective`) followed by the component at `U` of `symmetricPowerIso.inv`.
  (rfl)

/-- `symmetricPowerSectionsIso` is natural in the quasi-coherent module: for `φ : M ⟶ N`, it
intertwines `Symⁿ` of the map of sections of `φ` over `U` with the map of sections of `Symⁿ φ`. -/
@[reassoc]
lemma symmetricPowerSectionsIso_hom_naturality {N : X.Modules} [N.IsQuasicoherent] (φ : M ⟶ N)
    (hU : IsAffineOpen U) (n : ℕ) :
    ModuleCat.symmetricPower.map ((sectionsFunctor U).map φ) n ≫
        (N.symmetricPowerSectionsIso hU n).hom =
      (M.symmetricPowerSectionsIso hU n).hom ≫
        (sectionsFunctor U).map ((SheafOfModules.symmetricPower X.sheaf n).map φ) := by
  ext x
  -- after `symmetricPowerSectionsIso_hom_apply`, this is naturality of the sheafification unit
  exact (SheafOfModules.symmetricPower_map_val_app_unit n φ (op U) x).symm

/-- `symmetricPowerSectionsIso` is compatible with restriction to a smaller affine open `V ≤ U`:
the restriction of the image of `x` is the image of the restriction of `x` in the sectionwise
symmetric power, which is `Symⁿ` of the restriction map of `M`
(`PresheafOfModulesOfCommRing.coe_symmetricPower_obj_map_apply`). -/
lemma symmetricPowerSectionsIso_hom_restrict (hU : IsAffineOpen U) {V : X.Opens}
    (hV : IsAffineOpen V) (i : V ⟶ U) (n : ℕ)
    (x : (PresheafOfModulesOfCommRing.obj (R := X.presheaf) M.val (op U)).symmetricPower n) :
    ((SheafOfModules.symmetricPower X.sheaf n).obj M).val.map i.op
        ((M.symmetricPowerSectionsIso hU n).hom x) =
      (M.symmetricPowerSectionsIso hV n).hom
        (((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val).map i.op
          x) :=
  -- naturality of `symmetricPowerIso.inv`, then of the sheafification unit
  Eq.trans
    (PresheafOfModules.naturality_apply (SheafOfModules.symmetricPowerIso n M).inv.val i.op _).symm
    (congrArg _ (PresheafOfModules.naturality_apply
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        ((PresheafOfModulesOfCommRing.symmetricPower (R := X.presheaf) n).obj M.val)) i.op x).symm)

end AlgebraicGeometry.Scheme.Modules
