/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.ExteriorPower.Basic
public import TauCeti.Algebra.Category.ModuleCat.ExteriorPower.Mul

/-!
# Exterior multiplication of module presheaves

The sectionwise wedge product defines multiplication of exterior powers of module presheaves.
It is natural, associative and unital, and the braiding acts with the Koszul sign. These
maps and identities are the presheaf input to exterior multiplication of module sheaves.

The construction follows the sectionwise monoidal pattern of
`PresheafOfModulesOfCommRing.symmetricPowerMul`, using exterior rather than symmetric products.
-/

public section

open CategoryTheory MonoidalCategory

universe u v w

noncomputable section

namespace PresheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Exterior multiplication of presheaves of modules, computed by the wedge product on sections. -/
def exteriorPowerMul (M : PresheafOfModulesOfCommRing.{u} R) (i j : ℕ) :
    (exteriorPower i).obj M ⊗ (exteriorPower j).obj M ⟶ (exteriorPower (i + j)).obj M :=
  homMk (fun X ↦ ModuleCat.exteriorPower.mul (M.obj X) i j)
    (fun {X Y} f ↦ by
      refine ModuleCat.exteriorPower.tensor_hom_ext fun x y ↦ ?_
      -- Tensor sections and restriction-of-scalars wrappers are only definitionally the
      -- corresponding module tensors, so these sectionwise rewrites use `erw`.
      erw [ModuleCat.comp_apply, Monoidal.tensorObj_map_tmul,
        ModuleCat.restrictScalars.map_apply, exteriorPower_obj_map_mk, exteriorPower_obj_map_mk,
        ModuleCat.exteriorPower.mul_mk, ModuleCat.comp_apply, ModuleCat.exteriorPower.mul_mk,
        exteriorPower_obj_map_mk]
      congr 1
      ext k
      refine Fin.addCases (fun a ↦ ?_) (fun a ↦ ?_) k
      · exact (Fin.append_left _ _ a).trans
          (congrArg (M.map f) (Fin.append_left x y a).symm)
      · exact (Fin.append_right _ _ a).trans
          (congrArg (M.map f) (Fin.append_right x y a).symm))

/-- Exterior multiplication is computed sectionwise. -/
@[simp]
lemma exteriorPowerMul_app (M : PresheafOfModulesOfCommRing.{u} R) (i j : ℕ) (X : Cᵒᵖ) :
    (exteriorPowerMul M i j).app X = ModuleCat.exteriorPower.mul (M.obj X) i j :=
  (rfl)

private lemma eqToHom_exteriorPower_app (M : PresheafOfModulesOfCommRing.{u} R) {i j : ℕ}
    (h : i = j) (X : Cᵒᵖ) :
    (eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) h)).app X =
      eqToHom (congrArg (M.obj X).exteriorPower h) := by
  subst h
  rfl

/-- Exterior multiplication is natural in the presheaf of modules. -/
@[reassoc]
lemma exteriorPowerMul_naturality {M N : PresheafOfModulesOfCommRing.{u} R} (φ : M ⟶ N)
    (i j : ℕ) :
    ((exteriorPower i).map φ ⊗ₘ (exteriorPower j).map φ) ≫ exteriorPowerMul N i j =
      exteriorPowerMul M i j ≫ (exteriorPower (i + j)).map φ := by
  ext1 X
  simp only [PresheafOfModules.comp_app, tensorHom_app, exteriorPower_map_app,
    exteriorPowerMul_app]
  exact ModuleCat.exteriorPower.mul_naturality (φ.app' X) i j

/-- Exterior multiplication is associative, with the canonical identification of degrees. -/
@[reassoc]
lemma exteriorPowerMul_assoc (M : PresheafOfModulesOfCommRing.{u} R) (i j k : ℕ) :
    (exteriorPowerMul M i j ▷ (exteriorPower k).obj M) ≫ exteriorPowerMul M (i + j) k =
      (α_ _ _ _).hom ≫ ((exteriorPower i).obj M ◁ exteriorPowerMul M j k) ≫
        exteriorPowerMul M i (j + k) ≫
          eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (add_assoc i j k).symm) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, whiskerRight_app, whiskerLeft_app, associator_hom_app,
    exteriorPowerMul_app]
  rw [eqToHom_exteriorPower_app M (add_assoc i j k).symm]
  exact ModuleCat.exteriorPower.mul_assoc (M.obj X) i j k

/-- Swapping the exterior factors introduces the Koszul sign. -/
@[reassoc]
lemma exteriorPowerMul_comm (M : PresheafOfModulesOfCommRing.{u} R) (i j : ℕ) :
    (β_ ((exteriorPower i).obj M) ((exteriorPower j).obj M)).hom ≫ exteriorPowerMul M j i =
      (-1 : ℤ) ^ (i * j) • (exteriorPowerMul M i j ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (add_comm i j))) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, braiding_hom_app, exteriorPowerMul_app,
    PresheafOfModules.zsmul_app]
  rw [eqToHom_exteriorPower_app M (add_comm i j)]
  exact ModuleCat.exteriorPower.mul_comm (M.obj X) i j

/-- The zeroth exterior power is a left unit. -/
@[reassoc]
lemma exteriorPowerMul_one_mul (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    ((exteriorPowerZeroIso R).inv.app M ▷ (exteriorPower n).obj M) ≫ exteriorPowerMul M 0 n =
      (λ_ ((exteriorPower n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (zero_add n).symm) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, whiskerRight_app, leftUnitor_hom_app,
    exteriorPowerMul_app, exteriorPowerZeroIso_inv_app_app]
  rw [eqToHom_exteriorPower_app M (zero_add n).symm]
  exact ModuleCat.exteriorPower.one_mul (M.obj X) n

/-- The zeroth exterior power is a right unit. -/
@[reassoc]
lemma exteriorPowerMul_mul_one (M : PresheafOfModulesOfCommRing.{u} R) (n : ℕ) :
    ((exteriorPower n).obj M ◁ (exteriorPowerZeroIso R).inv.app M) ≫ exteriorPowerMul M n 0 =
      (ρ_ ((exteriorPower n).obj M)).hom ≫
        eqToHom (congrArg (fun n ↦ (exteriorPower n).obj M) (add_zero n).symm) := by
  ext1 X
  simp only [PresheafOfModules.comp_app, whiskerLeft_app, rightUnitor_hom_app,
    exteriorPowerMul_app, exteriorPowerZeroIso_inv_app_app]
  rw [eqToHom_exteriorPower_app M (add_zero n).symm]
  exact ModuleCat.exteriorPower.mul_one (M.obj X) n

end PresheafOfModulesOfCommRing
