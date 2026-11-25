/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Free.Basic
public import TauCeti.AlgebraicGeometry.Sites.Big.Sheaf

/-!
# The big-site module of the structure sheaf

Let `S` be a scheme. The big-site module `(𝒪_S)^a : (T, h) ↦ Γ(T, h^* 𝒪_S)` of the structure sheaf
(`AlgebraicGeometry.Scheme.Modules.bigSheaf`) is the unit module over the big structure sheaf
`T ↦ Γ(T, 𝒪_T)`: the identifications `h^* 𝒪_S ≅ 𝒪_T` (`Scheme.Modules.pullbackObjUnitIso`) are
compatible with the restriction maps of the big site.

The isomorphism is built from the global section `1` of the unit module: its image is the family
of sections `(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1 ∈ Γ(T, h^* 𝒪_S)`, which is compatible with restriction
(`AlgebraicGeometry.Scheme.Modules.bigSectionsRestrict_pullbackObjUnitIso_inv_one`), and on
`Γ(T, 𝒪_T)` the induced map is the linear isomorphism `(h^* 𝒪_S ≅ 𝒪_T)⁻¹` on global sections.

## Main declarations

* `AlgebraicGeometry.Scheme.bigSheafUnitSection`: the global section `(1)_T` of
  `(𝒪_S)^a`.
* `AlgebraicGeometry.Scheme.bigSheafUnitIso`: `(𝒪_S)^a ≅ unit`, the big-site module of the
  structure sheaf is the unit module over the big structure sheaf.
-/

public section

open CategoryTheory Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Scheme

/-- The global section `(1)_T = (h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1` of the big-site module `(𝒪_S)^a` of the
structure sheaf. -/
noncomputable def bigSheafUnitSection (S : Scheme.{u}) :
    (Modules.bigSheaf (𝟙_ S.Modules)).val.sections :=
  PresheafOfModules.sectionsMk
    (fun T ↦ (Modules.pullbackObjUnitIso T.unop.hom).inv.app ⊤ (1 : Γ(T.unop.left, ⊤)))
    fun _ _ f ↦ Modules.bigSectionsRestrict_pullbackObjUnitIso_inv_one f.unop

/-- Over an `S`-scheme `T`, the section `bigSheafUnitSection S` is `(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1`. -/
@[simp]
lemma bigSheafUnitSection_eval (S : Scheme.{u}) (T : Over S) :
    (bigSheafUnitSection S).eval (op T) =
      (Modules.pullbackObjUnitIso T.hom).inv.app ⊤ (1 : Γ(T.left, ⊤)) :=
  (rfl)

/-- The morphism from the unit module over the big structure sheaf to the big-site module of the
structure sheaf `𝒪_S` sending `1` to the section `(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1`. -/
noncomputable def unitToBigSheafUnit (S : Scheme.{u}) :
    SheafOfModules.unit (bigRingCatSheaf S) ⟶ Modules.bigSheaf (𝟙_ S.Modules) :=
  (Modules.bigSheaf (𝟙_ S.Modules)).unitHomEquiv.symm (bigSheafUnitSection S)

/-- On `Γ(T, 𝒪_T)`, the morphism `unitToBigSheafUnit S` is the inverse of the identification
`h^* 𝒪_S ≅ 𝒪_T` on global sections. -/
lemma unitToBigSheafUnit_val_app_apply (S : Scheme.{u}) (T : Over S) (r : Γ(T.left, ⊤)) :
    (unitToBigSheafUnit S).val.app (op T) r = (Modules.pullbackObjUnitIso T.hom).inv.app ⊤ r := by
  -- The unit module of `T` has the sections of `𝒪_T` as its sections, so `r • 1 = r * 1 = r`.
  exact (TauCeti.SheafOfModules.unitHomEquiv_symm_val_app (bigSheafUnitSection S) (op T) r).trans
    ((Modules.Hom.app_smul (Modules.pullbackObjUnitIso T.hom).inv r _).symm.trans
      (congrArg _ (mul_one r)))

/-- On each `S`-scheme `T`, the morphism `unitToBigSheafUnit S` is bijective: it is the inverse of
the identification `h^* 𝒪_S ≅ 𝒪_T` on global sections. -/
lemma bijective_unitToBigSheafUnit_val_app (S : Scheme.{u}) (T : Over S) :
    Function.Bijective ((unitToBigSheafUnit S).val.app (op T)) := by
  rw [funext (unitToBigSheafUnit_val_app_apply S T)]
  exact ConcreteCategory.bijective_of_isIso ((Modules.pullbackObjUnitIso T.hom).inv.app ⊤)

/-- The morphism `unitToBigSheafUnit S` is an isomorphism. -/
instance isIso_unitToBigSheafUnit (S : Scheme.{u}) : IsIso (unitToBigSheafUnit S) :=
  TauCeti.SheafOfModules.isIso_unitHomEquiv_symm (bigSheafUnitSection S) fun T ↦
    bijective_unitToBigSheafUnit_val_app S T.unop

/-- The big-site module `(𝒪_S)^a : (T, h) ↦ Γ(T, h^* 𝒪_S)` of the structure sheaf is the unit
module over the big structure sheaf `T ↦ Γ(T, 𝒪_T)`, through the identifications
`h^* 𝒪_S ≅ 𝒪_T`. -/
noncomputable def bigSheafUnitIso (S : Scheme.{u}) :
    Modules.bigSheaf (𝟙_ S.Modules) ≅ SheafOfModules.unit (bigRingCatSheaf S) :=
  (asIso (unitToBigSheafUnit S)).symm

/-- The inverse of `bigSheafUnitIso S` is `unitToBigSheafUnit S`, which sends `1` to the section
`(h^* 𝒪_S ≅ 𝒪_T)⁻¹ 1`. -/
@[simp]
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
