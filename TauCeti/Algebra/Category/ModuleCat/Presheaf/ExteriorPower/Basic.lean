/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# Exterior powers of presheaves of modules

Let `R` be a presheaf of commutative rings on a category `C`. For a presheaf of `R`-modules `M`
and `n : ℕ`, the `n`-th exterior power of `M` is the presheaf of modules whose sections over `X`
are the exterior power `⋀[R.obj X]^n (M.obj X)` (Mathlib's `ModuleCat.exteriorPower`), and whose
restriction along `f : X ⟶ Y` sends `m₁ ∧ ⋯ ∧ mₙ` to `M.map f m₁ ∧ ⋯ ∧ M.map f mₙ`. This is the
presheaf-level input to exterior powers of sheaves of modules, which are obtained by
sheafification. As for Mathlib's monoidal structure on these presheaves of modules
(`PresheafOfModulesOfCommRing.monoidalCategoryStruct`), modules are taken in the universe of the
rings.

## Main declarations

* `PresheafOfModulesOfCommRing.exteriorPower n` is the `n`-th exterior power, as an
  endofunctor of presheaves of `R`-modules; `exteriorPower_obj_obj`, `exteriorPower_obj_map_mk`
  and `exteriorPower_map_app` compute its sections, restriction maps and action on morphisms;
* `PresheafOfModulesOfCommRing.exteriorPowerZeroIso` identifies the zeroth exterior power
  with the constant functor at the unit presheaf of modules `R`;
* `PresheafOfModulesOfCommRing.exteriorPowerOneIso` identifies the first exterior power
  with the identity functor.
-/

public section

open CategoryTheory

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Auxiliary definition for `exteriorPower`: the restriction maps of the exterior power of a
presheaf of modules, sending `m₁ ∧ ⋯ ∧ mₙ` to `M.map f m₁ ∧ ⋯ ∧ M.map f mₙ`. -/
def exteriorPowerObjMap (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) :
    (M.obj X).exteriorPower n ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).exteriorPower n) :=
  ModuleCat.exteriorPower.desc
    { toFun x := ModuleCat.exteriorPower.mk (M := M.obj Y) (n := n) fun j ↦ M.map f (x j)
      map_update_add' x i a b := by
        simp only [Function.apply_update (fun _ ↦ M.map f), map_add]
        exact (ModuleCat.exteriorPower.mk (M := M.obj Y) (n := n)).map_update_add _ _ _ _
      map_update_smul' x i c a := by
        simp only [Function.apply_update (fun _ ↦ M.map f), map_smul]
        exact (ModuleCat.exteriorPower.mk (M := M.obj Y) (n := n)).map_update_smul _ _
          (R.map f c) _
      map_eq_zero_of_eq' x i j h hij :=
        (ModuleCat.exteriorPower.mk (M := M.obj Y) (n := n)).map_eq_zero_of_eq _
          (by dsimp only; rw [h]) hij }

/-- The restriction maps of the exterior power on decomposable elements. -/
lemma exteriorPowerObjMap_mk (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : Fin n → M.obj X) :
    exteriorPowerObjMap M n f (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (M := M.obj Y) fun j ↦ M.map f (x j) :=
  ModuleCat.exteriorPower.desc_mk _ _

/-- Auxiliary definition for `exteriorPower`: the exterior power of a presheaf of modules. -/
@[expose]
def exteriorPowerObj (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModulesOfCommRing.mk (fun X ↦ (M.obj X).exteriorPower n)
    (fun f ↦ exteriorPowerObjMap M n f)
    (fun X ↦ ModuleCat.exteriorPower.hom_ext (by
      ext x
      simp only [ModuleCat.AlternatingMap.postcomp_apply, exteriorPowerObjMap_mk,
        PresheafOfModules.map_id, ModuleCat.restrictScalarsId'_inv_app,
        ModuleCat.restrictScalarsId'App_inv_apply]
      rfl))
    (fun {_ _ Z} f g ↦ ModuleCat.exteriorPower.hom_ext (by
      ext x
      refine (exteriorPowerObjMap_mk M n (f ≫ g) x).trans ?_
      -- the restriction-of-scalars comparison maps on the right are identities on elements
      exact (congrArg (ModuleCat.exteriorPower.mk (M := M.obj Z) (n := n))
        (funext fun j ↦ M.map_comp_apply f g (x j))).trans
          ((congrArg (exteriorPowerObjMap M n g) (exteriorPowerObjMap_mk M n f x)).trans
            (exteriorPowerObjMap_mk M n g _)).symm))

/-- The restriction maps of the exterior power are natural in the presheaf of modules. -/
lemma exteriorPowerObjMap_naturality {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    exteriorPowerObjMap M n f ≫ (ModuleCat.restrictScalars (R.map f).hom).map
        (ModuleCat.exteriorPower.map (φ.app' Y) n) =
      ModuleCat.exteriorPower.map (φ.app' X) n ≫ exteriorPowerObjMap N n f :=
  ModuleCat.exteriorPower.hom_ext (by
    ext x
    refine ((congrArg (ModuleCat.exteriorPower.map (φ.app' Y) n)
      (exteriorPowerObjMap_mk M n f x)).trans (ModuleCat.exteriorPower.map_mk _ _)).trans ?_
    refine Eq.trans ?_ ((congrArg (exteriorPowerObjMap N n f)
      (ModuleCat.exteriorPower.map_mk _ _)).trans (exteriorPowerObjMap_mk N n f _)).symm
    exact congrArg (ModuleCat.exteriorPower.mk (M := N.obj Y) (n := n))
      (funext fun j ↦ PresheafOfModulesOfCommRing.naturality_apply φ f (x j)))

/-- The `n`-th exterior power of presheaves of modules over a presheaf of commutative rings,
computed sectionwise: its sections over `X` are `⋀[R.obj X]^n (M.obj X)`, and its restriction maps
send `m₁ ∧ ⋯ ∧ mₙ` to the wedge product of the restrictions of the `mᵢ`. -/
@[expose]
def exteriorPower (n : ℕ) :
    PresheafOfModulesOfCommRing.{u} R ⥤ PresheafOfModulesOfCommRing.{u} R where
  obj M := exteriorPowerObj M n
  map φ := PresheafOfModulesOfCommRing.homMk
    (fun X ↦ ModuleCat.exteriorPower.map (φ.app' X) n)
    (fun f ↦ exteriorPowerObjMap_naturality φ n f)
  map_id M := by
    ext X : 1
    exact (ModuleCat.exteriorPower.functor _ n).map_id (M.obj X)
  map_comp φ ψ := by
    ext X : 1
    exact (ModuleCat.exteriorPower.functor _ n).map_comp (φ.app' X) (ψ.app' X)

/-- The sections of the exterior power over `X` are the exterior power of the sections. -/
lemma exteriorPower_obj_obj (n : ℕ) (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPower n).obj M).obj X = (M.obj X).exteriorPower n :=
  rfl

/-- The restriction maps of the exterior power restrict each factor of a wedge product. -/
@[simp]
lemma exteriorPower_obj_map_mk (n : ℕ) (M : PresheafOfModulesOfCommRing.{u} R) {X Y : Cᵒᵖ}
    (f : X ⟶ Y) (x : Fin n → M.obj X) :
    ((exteriorPower n).obj M).map f (ModuleCat.exteriorPower.mk x) =
      ModuleCat.exteriorPower.mk (M := M.obj Y) fun j ↦ M.map f (x j) :=
  exteriorPowerObjMap_mk M n f x

/-- The exterior power of a morphism is computed sectionwise. -/
@[simp]
lemma exteriorPower_map_app (n : ℕ) {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (X : Cᵒᵖ) :
    ((exteriorPower n).map φ).app X = ModuleCat.exteriorPower.map (φ.app' X) n :=
  rfl

variable (R) in
/-- The zeroth exterior power of a presheaf of `R`-modules is the unit presheaf of modules `R`,
naturally; on sections it is `ModuleCat.exteriorPower.iso₀`. -/
def exteriorPowerZeroIso :
    exteriorPower (R := R) 0 ≅ (Functor.const _).obj (PresheafOfModulesOfCommRing.unit R) :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModulesOfCommRing.isoMk
      (fun X ↦ ModuleCat.exteriorPower.iso₀ (M.obj X))
      (fun X Y f ↦ ModuleCat.exteriorPower.hom_ext (by
        ext x
        refine ((congrArg (ModuleCat.exteriorPower.iso₀ (M.obj Y)).hom
          (exteriorPower_obj_map_mk 0 M f x)).trans
            (ModuleCat.exteriorPower.iso₀_hom_apply _)).trans ?_
        exact ((congrArg ((PresheafOfModulesOfCommRing.unit R).map f)
          (ModuleCat.exteriorPower.iso₀_hom_apply x)).trans
            (PresheafOfModules.unit_map_one _ f)).symm)))
    (fun φ ↦ by
      ext X : 1
      exact ModuleCat.exteriorPower.iso₀_hom_naturality (φ.app' X))

@[simp]
lemma exteriorPowerZeroIso_hom_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerZeroIso R).hom.app M).app X = (ModuleCat.exteriorPower.iso₀ (M.obj X)).hom :=
  (rfl)

@[simp]
lemma exteriorPowerZeroIso_inv_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerZeroIso R).inv.app M).app X = (ModuleCat.exteriorPower.iso₀ (M.obj X)).inv :=
  (rfl)

variable (R) in
/-- The first exterior power of a presheaf of `R`-modules is the presheaf of modules itself,
naturally; on sections it is `ModuleCat.exteriorPower.iso₁`. -/
def exteriorPowerOneIso : exteriorPower (R := R) 1 ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun M ↦ PresheafOfModulesOfCommRing.isoMk
      (fun X ↦ ModuleCat.exteriorPower.iso₁ (M.obj X))
      (fun X Y f ↦ ModuleCat.exteriorPower.hom_ext (by
        ext x
        refine ((congrArg (ModuleCat.exteriorPower.iso₁ (M.obj Y)).hom
          (exteriorPower_obj_map_mk 1 M f x)).trans
            (ModuleCat.exteriorPower.iso₁_hom_apply _)).trans ?_
        exact congrArg (M.map f) (ModuleCat.exteriorPower.iso₁_hom_apply x).symm)))
    (fun φ ↦ by
      ext X : 1
      exact ModuleCat.exteriorPower.iso₁_hom_naturality (φ.app' X))

@[simp]
lemma exteriorPowerOneIso_hom_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerOneIso R).hom.app M).app X = (ModuleCat.exteriorPower.iso₁ (M.obj X)).hom :=
  (rfl)

@[simp]
lemma exteriorPowerOneIso_inv_app_app (M : PresheafOfModulesOfCommRing.{u} R) (X : Cᵒᵖ) :
    ((exteriorPowerOneIso R).inv.app M).app X = (ModuleCat.exteriorPower.iso₁ (M.obj X)).inv :=
  (rfl)

end PresheafOfModulesOfCommRing

end
