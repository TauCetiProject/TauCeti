/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify
public import Mathlib.CategoryTheory.Limits.Lattice
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Constant
public import TauCeti.Topology.Sheaves.LocallyConstant.Basic

/-!
# Sheaves of `R`-modules are sheaves of modules over the locally constant functions

Let `X` be a topological space, `R` a ring and `R_X` the sheaf of rings of locally constant
`R`-valued functions (`TopCat.locallyConstantSheaf`). This file constructs an equivalence between
sheaves of `R`-modules on `X` and sheaves of `R_X`-modules
(`TopCat.sheafModuleCatEquivSheafOfModules`). Both functors keep the underlying sheaf of abelian
groups.

* A sheaf of `R`-modules `F` becomes a sheaf of `R_X`-modules
  (`TopCat.toLocallyConstantSheafOfModules`): a locally constant function `f` on `V` acts on a
  section `s` of `F` over `V` by gluing the sections `r • s|_W`, where `W` runs over the open
  subsets of `V` on which `f` is constant with value `r`
  (`TopCat.toLocallyConstantSheafOfModulesObj_map_smul`).
* Conversely, a sheaf of `R_X`-modules becomes a sheaf of `R`-modules
  (`TopCat.ofLocallyConstantSheafOfModules`) through Mathlib's forgetful functor
  `SheafOfModules.forgetToSheafModuleCat` to sheaves of modules over the ring of global sections
  `Γ(X, R_X)`, followed by restriction of scalars along the constant sections `R → Γ(X, R_X)`.
  The ring `Γ(X, R_X)` itself is in general larger than `R`.

The gluing is Mathlib's `PresheafOfModules.sheafify` (J. Riou), applied to the inclusion of the
constant presheaf of rings into `R_X`, which is locally bijective, and to the identity of the
underlying sheaf of abelian groups. That two module structures agree is checked locally on the
open subsets where a given locally constant function is constant.

## Main declarations

* `TopCat.toLocallyConstantSheafOfModules`, `TopCat.ofLocallyConstantSheafOfModules`: the two
  functors.
* `TopCat.toLocallyConstantSheafOfModulesObj_map_smul`: the action of a locally constant function
  on the open subsets where it is constant.
* `TopCat.ofLocallyConstantSheafOfModules_obj_obj_smul`: an element `r` of `R` acts as the
  constant function `r`.
* `TopCat.toLocallyConstantSheafOfModulesCompToSheafIso`,
  `TopCat.ofLocallyConstantSheafOfModulesCompSheafComposeIso`: the underlying sheaves of abelian
  groups are unchanged.
* `TopCat.sheafModuleCatEquivSheafOfModules`: the equivalence.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TopologicalSpace Limits

namespace TopCat

variable (X : TopCat.{u}) (R : Type u) [Ring R]

/-- The sheaf of `R_X`-modules with the same sections and restriction maps as a sheaf of
`R`-modules `F`. A locally constant function acts on a section by gluing the actions of its
values on the open subsets where it is constant
(`TopCat.toLocallyConstantSheafOfModulesObj_map_smul`). -/
noncomputable def toLocallyConstantSheafOfModulesObj
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    SheafOfModules.{u} (locallyConstantSheaf X R) :=
  PresheafOfModules.sheafify (constToLocallyConstant X R)
    (A := ⟨((PresheafOfModules.ofPresheafModuleCat R).obj F.obj).presheaf,
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).property⟩) (𝟙 _)

variable {X R} in
/-- If a locally constant function `f` on `V` is constant with value `r` on `W ⊆ V`, then the
restriction to `W` of `f • m` is `r • m|_W`. -/
theorem toLocallyConstantSheafOfModulesObj_map_smul
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    {V W : Opens X} (i : W ⟶ V) (f : (locallyConstantSheaf X R).obj.obj (op V)) (r : R)
    (hf : (constToLocallyConstant X R).app (op W) r = (locallyConstantSheaf X R).obj.map i.op f)
    (m : (toLocallyConstantSheafOfModulesObj X R F).val.obj (op V)) :
    F.obj.map i.op (f • m) = r • F.obj.map i.op m :=
  PresheafOfModules.Sheafify.map_smul_eq
    (A := ⟨((PresheafOfModules.ofPresheafModuleCat R).obj F.obj).presheaf,
      ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj F).property⟩)
    (constToLocallyConstant X R) (𝟙 _) f m i.op r hf (F.obj.map i.op m) rfl

/-- The functor from sheaves of `R`-modules to sheaves of modules over the sheaf `R_X` of
locally constant functions. It does not change sections, restriction maps or morphisms. -/
noncomputable def toLocallyConstantSheafOfModules :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ⥤
      SheafOfModules.{u} (locallyConstantSheaf X R) where
  obj F := toLocallyConstantSheafOfModulesObj X R F
  map {F G} g := ⟨PresheafOfModules.homMk
    (Functor.whiskerRight g.hom (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})) (by
      -- Linearity is checked on the open subsets where the scalar is constant.
      intro V f m
      refine ((sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).obj G).isSeparated
        _ _ (Presheaf.imageSieve_mem _ (constToLocallyConstant X R) f) _ _ ?_
      rintro W i ⟨r, hr⟩
      calc _ = g.hom.app (op W) (F.obj.map i.op (f • m)) :=
            (NatTrans.naturality_apply g.hom i.op (f • m)).symm
        _ = g.hom.app (op W) (r • F.obj.map i.op m) := by
            rw [toLocallyConstantSheafOfModulesObj_map_smul F i f r hr m]
        _ = r • g.hom.app (op W) (F.obj.map i.op m) := map_smul _ _ _
        _ = r • G.obj.map i.op (g.hom.app V m) := by rw [NatTrans.naturality_apply g.hom i.op m]
        _ = _ := (toLocallyConstantSheafOfModulesObj_map_smul G i f r hr (g.hom.app V m)).symm)⟩

@[simp]
lemma toLocallyConstantSheafOfModules_obj
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R)) :
    (toLocallyConstantSheafOfModules X R).obj F = toLocallyConstantSheafOfModulesObj X R F :=
  rfl

/-- The functor from sheaves of modules over `R_X` to sheaves of `R`-modules: Mathlib's forgetful
functor to sheaves of modules over the ring of global sections `Γ(X, R_X)`, followed by
restriction of scalars along the constant sections `R → Γ(X, R_X)`. -/
noncomputable def ofLocallyConstantSheafOfModules :
    SheafOfModules.{u} (locallyConstantSheaf X R) ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) :=
  SheafOfModules.forgetToSheafModuleCat _ (op ⊤) isTerminalTop.op ⋙
    -- The ring `LocallyConstant ⊤ R` is named directly, so that `HasSheafCompose` is found.
    (sheafCompose _ (ModuleCat.restrictScalars.{u}
      (LocallyConstant.constRingHom : R →+* LocallyConstant (⊤ : Opens X) R)) :
        CategoryTheory.Sheaf (Opens.grothendieckTopology X)
          (ModuleCat.{u} (LocallyConstant (⊤ : Opens X) R)) ⥤ _)

variable {X R} in
/-- In `ofLocallyConstantSheafOfModules X R M`, an element `r` of `R` acts on sections as the
constant function with value `r`. -/
@[simp]
lemma ofLocallyConstantSheafOfModules_obj_obj_smul
    (M : SheafOfModules.{u} (locallyConstantSheaf X R)) (V : (Opens X)ᵒᵖ) (r : R)
    (m : ((ofLocallyConstantSheafOfModules X R).obj M).obj.obj V) :
    r • m = (constToLocallyConstant X R).app V r • (show M.val.obj V from m) :=
  -- By definition, `r` acts as the restriction of the global constant function `r`.
  congr($((NatTrans.naturality_apply (constToLocallyConstant X R)
    (isTerminalTop.op.to V) r).symm) • (show M.val.obj V from m))

/-- `toLocallyConstantSheafOfModules` keeps the underlying sheaf of abelian groups. -/
noncomputable def toLocallyConstantSheafOfModulesCompToSheafIso :
    toLocallyConstantSheafOfModules X R ⋙ SheafOfModules.toSheaf _ ≅
      sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (fun _ ↦ rfl)

/-- `ofLocallyConstantSheafOfModules` keeps the underlying sheaf of abelian groups. -/
noncomputable def ofLocallyConstantSheafOfModulesCompSheafComposeIso :
    ofLocallyConstantSheafOfModules X R ⋙
        sheafCompose _ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}) ≅
      SheafOfModules.toSheaf _ :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _)) (fun _ ↦ rfl)

/-- Sheaves of `R`-modules on `X` are equivalent to sheaves of modules over the sheaf `R_X` of
locally constant `R`-valued functions. Both functors keep the underlying sheaf of abelian groups,
and the unit and counit are the identity on sections. -/
noncomputable def sheafModuleCatEquivSheafOfModules :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R) ≌
      SheafOfModules.{u} (locallyConstantSheaf X R) where
  functor := toLocallyConstantSheafOfModules X R
  inverse := ofLocallyConstantSheafOfModules X R
  unitIso := NatIso.ofComponents (fun F ↦ ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦
    let e : F.obj.obj V ≃ₗ[R] ((ofLocallyConstantSheafOfModules X R).obj
        ((toLocallyConstantSheafOfModules X R).obj F)).obj.obj V :=
      { toFun m := m
        invFun m := m
        map_add' _ _ := rfl
        map_smul' r m := by
          -- `r` acts on the target as the restriction of the global constant function `r`.
          have h := toLocallyConstantSheafOfModulesObj_map_smul F (𝟙 V.unop)
            ((locallyConstantSheaf X R).obj.map (isTerminalTop.op.to V)
              ((constToLocallyConstant X R).app (op ⊤) r)) r (by
            rw [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply]
            exact NatTrans.naturality_apply (constToLocallyConstant X R)
              (isTerminalTop.op.to V) r) m
          rw [op_id, F.obj.map_id] at h
          exact h.symm
        left_inv _ := rfl
        right_inv _ := rfl }
    e.toModuleIso) (fun _ ↦ rfl))) (fun _ ↦ by ext; rfl)
  counitIso := NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦
      let e : ((toLocallyConstantSheafOfModules X R).obj
          ((ofLocallyConstantSheafOfModules X R).obj M)).val.obj V ≃ₗ[
            (locallyConstantSheaf X R).obj.obj V] M.val.obj V :=
        { toFun m := m
          invFun m := m
          map_add' _ _ := rfl
          map_smul' f m := by
            -- Both actions of `f` agree on the open subsets where `f` is constant.
            refine ((SheafOfModules.toSheaf _).obj M).isSeparated _ _
              (Presheaf.imageSieve_mem _ (constToLocallyConstant X R) f) _ _ ?_
            rintro W i ⟨r, hr⟩
            refine (toLocallyConstantSheafOfModulesObj_map_smul
              ((ofLocallyConstantSheafOfModules X R).obj M) i f r hr m).trans ?_
            rw [ofLocallyConstantSheafOfModules_obj_obj_smul, hr]
            exact (M.val.map_smul i.op f m).symm
          left_inv _ := rfl
          right_inv _ := rfl }
      e.toModuleIso) (fun _ _ _ ↦ rfl))) (fun _ ↦ by ext; rfl)
  functor_unitIso_comp _ := by ext; rfl

@[simp]
lemma sheafModuleCatEquivSheafOfModules_functor :
    (sheafModuleCatEquivSheafOfModules X R).functor = toLocallyConstantSheafOfModules X R :=
  rfl

@[simp]
lemma sheafModuleCatEquivSheafOfModules_inverse :
    (sheafModuleCatEquivSheafOfModules X R).inverse = ofLocallyConstantSheafOfModules X R :=
  rfl

end TopCat
