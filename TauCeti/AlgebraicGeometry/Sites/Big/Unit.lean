/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf

/-!
# The big-site module of the structure sheaf

Let `S` be a scheme. The big-site module `(𝒪_S)^a : (T, h) ↦ Γ(T, h^* 𝒪_S)` of the structure sheaf
(`AlgebraicGeometry.Scheme.Modules.bigSheaf`) is the unit module over the big structure sheaf
`T ↦ Γ(T, 𝒪_T)`: the identifications `h^* 𝒪_S ≅ 𝒪_T` (`Scheme.Modules.pullbackObjUnitIso`) are
compatible with the restriction maps of the big site. This is `bigSheaf_structureSheaf` of
SchemeAndStackFoundations §2.9.

The isomorphism is built from the global section `1` of the unit module: its image is the family
of sections `(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1 ∈ Γ(T, h^* 𝒪_S)`, which is compatible with restriction
(`AlgebraicGeometry.Scheme.Modules.bigSectionsRestrict_pullbackObjUnitIso_inv_one`), and on
`Γ(T, 𝒪_T)` the induced map is the linear isomorphism `(h^* 𝒪_S ≅ 𝒪_T)⁻¹` on global sections.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.bigSheafUnitSection`: the global section `(1)_T` of
  `(𝒪_S)^a`.
* `AlgebraicGeometry.Scheme.bigSheafUnitIso`: `(𝒪_S)^a ≅ unit`, the big-site module of the
  structure sheaf is the unit module over the big structure sheaf.
-/

public section

open CategoryTheory Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

namespace Modules

variable {S : Scheme.{u}}

/-- Restricting the section `(h'^* 𝒪_S ≅ 𝒪_{T'})⁻¹ 1` of the big site along `f : T ⟶ T'` gives
the section `(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1`. -/
lemma bigSectionsRestrict_pullbackObjUnitIso_inv_one {T T' : Over S} (f : T ⟶ T') :
    bigSectionsRestrict (𝟙_ S.Modules) f
        ((pullbackObjUnitIso T'.hom).inv.app ⊤ (1 : Γ(T'.left, ⊤))) =
      (pullbackObjUnitIso T.hom).inv.app ⊤ (1 : Γ(T.left, ⊤)) := by
  have hu := Hom.pullbackSections_comp_of_eq T'.hom (𝟙_ S.Modules) f.left (Over.w f)
    (1 : Γ(S, ⊤))
  rw [← Hom.pullbackObjUnitIso_inv_app_one T'.hom, ← Hom.pullbackObjUnitIso_inv_app_one] at hu
  rw [bigSectionsRestrict_apply, ← hu]
  have e : ((pullbackCongr (Over.w f)).inv.app (𝟙_ S.Modules) ≫
      (pullbackComp f.left T'.hom).inv.app (𝟙_ S.Modules)) ≫
        ((pullbackComp f.left T'.hom).hom.app (𝟙_ S.Modules) ≫
          (pullbackCongr (Over.w f)).hom.app (𝟙_ S.Modules)) = 𝟙 _ := by
    simp
  exact congr(Hom.app $e ⊤ ((pullbackObjUnitIso T.hom).inv.app ⊤ (1 : Γ(T.left, ⊤))))

/-- The global section `(1)_T = (h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1` of the big-site module `(𝒪_S)^a` of the
structure sheaf. -/
noncomputable def bigSheafUnitSection (S : Scheme.{u}) :
    (bigSheaf (𝟙_ S.Modules)).val.sections :=
  PresheafOfModules.sectionsMk
    (fun T ↦ (pullbackObjUnitIso T.unop.hom).inv.app ⊤ (1 : Γ(T.unop.left, ⊤)))
    fun _ _ f ↦ bigSectionsRestrict_pullbackObjUnitIso_inv_one f.unop

end Modules

/-- The morphism from the unit module over the big structure sheaf to the big-site module of the
structure sheaf `𝒪_S` sending `1` to the section `(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1`. -/
noncomputable def unitToBigSheafUnit (S : Scheme.{u}) :
    SheafOfModules.unit (bigRingCatSheaf S) ⟶ Modules.bigSheaf (𝟙_ S.Modules) :=
  (Modules.bigSheaf (𝟙_ S.Modules)).unitHomEquiv.symm (Modules.bigSheafUnitSection S)

/-- On `Γ(T, 𝒪_T)`, the morphism `unitToBigSheafUnit S` is the inverse of the identification
`h^* 𝒪_S ≅ 𝒪_T` on global sections. -/
lemma unitToBigSheafUnit_val_app_apply (S : Scheme.{u}) (T : Over S) (r : Γ(T.left, ⊤)) :
    (unitToBigSheafUnit S).val.app (op T) r = (Modules.pullbackObjUnitIso T.hom).inv.app ⊤ r := by
  change r • (Modules.pullbackObjUnitIso T.hom).inv.app ⊤ (1 : Γ(T.left, ⊤)) = _
  exact (Modules.Hom.app_smul (Modules.pullbackObjUnitIso T.hom).inv r
    (show Γ(𝟙_ T.left.Modules, ⊤) from (1 : Γ(T.left, ⊤)))).symm.trans
      (congrArg _ (mul_one r))

/-- On each `S`-scheme `T`, the morphism `unitToBigSheafUnit S` is bijective: it is the inverse of
the identification `h^* 𝒪_S ≅ 𝒪_T` on global sections. -/
lemma bijective_unitToBigSheafUnit_val_app (S : Scheme.{u}) (T : Over S) :
    Function.Bijective ((unitToBigSheafUnit S).val.app (op T)) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun x ↦ (Modules.pullbackObjUnitIso T.hom).hom.app ⊤ x, fun r ↦ ?_, fun x ↦ ?_⟩
  · exact (congrArg (fun y ↦ (Modules.pullbackObjUnitIso T.hom).hom.app ⊤ y)
      (unitToBigSheafUnit_val_app_apply S T r)).trans
        congr(Modules.Hom.app $((Modules.pullbackObjUnitIso T.hom).inv_hom_id) ⊤ r)
  · exact (unitToBigSheafUnit_val_app_apply S T _).trans
      congr(Modules.Hom.app $((Modules.pullbackObjUnitIso T.hom).hom_inv_id) ⊤ x)

/-- The morphism `unitToBigSheafUnit S` is an isomorphism. -/
instance isIso_unitToBigSheafUnit (S : Scheme.{u}) : IsIso (unitToBigSheafUnit S) := by
  have (T : (Over S)ᵒᵖ) : IsIso ((unitToBigSheafUnit S).val.app T) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (bijective_unitToBigSheafUnit_val_app S T.unop)
  have : IsIso ((SheafOfModules.forget (bigRingCatSheaf S)).map (unitToBigSheafUnit S)) :=
    (PresheafOfModules.isoMk (fun T ↦ asIso ((unitToBigSheafUnit S).val.app T))
      fun _ _ f ↦ (unitToBigSheafUnit S).val.naturality f).isIso_hom
  exact isIso_of_reflects_iso _ (SheafOfModules.forget (bigRingCatSheaf S))

/-- **`bigSheaf_structureSheaf`.** The big-site module `(𝒪_S)^a : (T, h) ↦ Γ(T, h^* 𝒪_S)` of the
structure sheaf is the unit module over the big structure sheaf `T ↦ Γ(T, 𝒪_T)`, through the
identifications `h^* 𝒪_S ≅ 𝒪_T`. -/
noncomputable def bigSheafUnitIso (S : Scheme.{u}) :
    Modules.bigSheaf (𝟙_ S.Modules) ≅ SheafOfModules.unit (bigRingCatSheaf S) :=
  (asIso (unitToBigSheafUnit S)).symm

/-- The inverse of `bigSheafUnitIso S` is `unitToBigSheafUnit S`, which sends `1` to the section
`(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1`. -/
lemma bigSheafUnitIso_inv (S : Scheme.{u}) : (bigSheafUnitIso S).inv = unitToBigSheafUnit S :=
  (rfl)

/-- On `Γ(T, h^* 𝒪_S)`, the isomorphism `bigSheafUnitIso S` is the identification
`h^* 𝒪_S ≅ 𝒪_T` on global sections. -/
lemma bigSheafUnitIso_hom_val_app_apply (S : Scheme.{u}) (T : Over S)
    (x : Γ((Modules.pullback T.hom).obj (𝟙_ S.Modules), ⊤)) :
    (bigSheafUnitIso S).hom.val.app (op T) x = (Modules.pullbackObjUnitIso T.hom).hom.app ⊤ x := by
  apply (bijective_unitToBigSheafUnit_val_app S T).injective
  refine (congr(($((bigSheafUnitIso S).hom_inv_id)).val.app (op T) x)).trans ?_
  exact (congr(Modules.Hom.app $((Modules.pullbackObjUnitIso T.hom).hom_inv_id) ⊤ x)).symm.trans
    (unitToBigSheafUnit_val_app_apply S T _).symm

end AlgebraicGeometry.Scheme
