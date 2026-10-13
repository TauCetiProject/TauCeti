/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit

/-!
# The regular bimodule acts as the identity on graded left modules

Evaluation identifies the balanced tensor of the regular graded bimodule with a graded left
module with that module. Its inverse inserts the unit element. Both maps preserve the internal
grading, and evaluation is natural in graded module maps.

The construction adapts `bimoduleTensorLeftUnitor` from
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Unit`, using the left-module
analogue of its supporting `bimoduleTensorLift` from
`TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic`.

This is the unit comparison for the graded bimodule action on left modules. The module universe
contains the algebra universe, as in the selected graded endobimodule monoidal category.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory MulOpposite
open scoped TensorProduct

universe v uk uA

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]
  (Γ : InternalGrading k A) [GradedAlgebra Γ.piece]
  (N : GradedModuleCat.{max v uA} Γ.piece)

private def unitAction : bimoduleUnit.{v} Γ →ₗ[k] N →ₗ[k] N :=
  (Algebra.lsmul k k N (A := A)).toLinearMap.comp (bimoduleUnitEquiv.{v} Γ).symm.toLinearMap

private theorem unitAction_apply (x : bimoduleUnit.{v} Γ) (n : N) :
    unitAction.{v} Γ N x n = (bimoduleUnitEquiv.{v} Γ).symm x • n := by
  simp only [unitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply]

private theorem unitAction_degree {p q : ℤ} {x : bimoduleUnit.{v} Γ} {n : N}
    (hx : x ∈ (bimoduleUnit.{v} Γ).grading.piece p) (hn : n ∈ N.grading.piece q) :
    unitAction.{v} Γ N x n ∈ N.grading.piece (p + q) := by
  rw [unitAction_apply]
  exact SetLike.GradedSMul.smul_mem ((mem_bimoduleUnit_piece_iff.{v} Γ p x).1 hx) hn

/-- Evaluate a regular-bimodule element by its left action on a graded module. -/
def bimoduleModuleTensorLeftUnitorHom :
    bimoduleModuleTensorObj Γ Γ (bimoduleUnit.{v} Γ) N ⟶ N :=
  bimoduleModuleTensorLift Γ Γ (unitAction.{v} Γ N)
    (fun a x n ↦ by simp [unitAction_apply, bimoduleUnitEquiv_symm_smul, mul_smul])
    (fun a x n ↦ by simp [unitAction_apply, bimoduleUnitEquiv_symm_smul, mul_smul])
    (unitAction_degree.{v} Γ N)

@[simp]
theorem bimoduleModuleTensorLeftUnitorHom_tmul (x : bimoduleUnit.{v} Γ) (n : N) :
    (bimoduleModuleTensorLeftUnitorHom.{v} Γ N).hom
      (bimoduleModuleTensorTmul Γ Γ (bimoduleUnit.{v} Γ) N x n) =
      (bimoduleUnitEquiv.{v} Γ).symm x • n := by
  unfold bimoduleModuleTensorLeftUnitorHom
  calc
    _ = unitAction.{v} Γ N x n := bimoduleModuleTensorLift_tmul Γ Γ _ _ _ _ x n
    _ = _ := unitAction_apply.{v} Γ N x n

/-- Balancing transfers a module scalar to the regular bimodule's unit element. -/
@[simp]
theorem bimoduleModuleTensorTmul_unit_smul (a : A) (n : N) :
    bimoduleModuleTensorTmul Γ Γ (bimoduleUnit.{v} Γ) N (bimoduleUnitEquiv.{v} Γ 1) (a • n) =
      bimoduleModuleTensorTmul Γ Γ (bimoduleUnit.{v} Γ) N (bimoduleUnitEquiv.{v} Γ a) n := by
  rw [← bimoduleModuleTensorTmul_balance Γ Γ (bimoduleUnit.{v} Γ) N a]
  simp only [tmul_smul_bimoduleUnitEquiv, unop_op, one_mul]

private def unitInsert :
    N →ₗ[k] bimoduleModuleTensorObj Γ Γ (bimoduleUnit.{v} Γ) N :=
  bimoduleModuleTensorMk Γ Γ (bimoduleUnit.{v} Γ) N (bimoduleUnitEquiv.{v} Γ 1)

private def unitInsertLinear :
    N →ₗ[A] bimoduleModuleTensorObj Γ Γ (bimoduleUnit.{v} Γ) N where
  toAddHom := (unitInsert.{v} Γ N).toAddHom
  map_smul' a n := by
    simp only [unitInsert, LinearMap.toFun_eq_coe, RingHom.id_apply,
      bimoduleModuleTensorMk_apply, smul_bimoduleModuleTensorTmul,
      tmul_smul_bimoduleUnitEquiv, unop_one, mul_one, bimoduleModuleTensorTmul_unit_smul]

private theorem unitInsertLinear_apply (n : N) :
    unitInsertLinear.{v} Γ N n =
      bimoduleModuleTensorTmul Γ Γ (bimoduleUnit.{v} Γ) N (bimoduleUnitEquiv.{v} Γ 1) n :=
  bimoduleModuleTensorMk_apply Γ Γ _ _ _ n

/-- Insert the regular bimodule's unit element in the first tensor factor. -/
def bimoduleModuleTensorLeftUnitorInv :
    N ⟶ bimoduleModuleTensorObj Γ Γ (bimoduleUnit.{v} Γ) N :=
  ofHom (unitInsertLinear.{v} Γ N) (LinearMap.isHomogeneous_def.2 fun p n hn ↦ by
    rw [unitInsertLinear_apply]
    have hunit : bimoduleUnitEquiv.{v} Γ 1 ∈ (bimoduleUnit.{v} Γ).grading.piece 0 :=
      (mem_bimoduleUnit_piece_iff.{v} Γ 0 _).2 (by simpa using SetLike.one_mem_graded Γ.piece)
    simpa only [zero_add, add_zero]
      using bimoduleModuleTensorTmul_mem Γ Γ (bimoduleUnit.{v} Γ) N hunit hn)

@[simp]
theorem bimoduleModuleTensorLeftUnitorInv_apply (n : N) :
    (bimoduleModuleTensorLeftUnitorInv.{v} Γ N).hom n =
      bimoduleModuleTensorTmul Γ Γ (bimoduleUnit.{v} Γ) N (bimoduleUnitEquiv.{v} Γ 1) n :=
  bimoduleModuleTensorMk_apply Γ Γ _ _ _ n

/-- Tensoring the regular graded bimodule with a left module returns that left module. -/
def bimoduleModuleTensorLeftUnitor :
    bimoduleModuleTensorObj Γ Γ (bimoduleUnit.{v} Γ) N ≅ N where
  hom := bimoduleModuleTensorLeftUnitorHom.{v} Γ N
  inv := bimoduleModuleTensorLeftUnitorInv.{v} Γ N
  hom_inv_id := by
    apply bimoduleModuleTensor_hom_ext Γ Γ
    intro x n
    simp only [hom_comp, LinearMap.comp_apply, bimoduleModuleTensorLeftUnitorHom_tmul,
      bimoduleModuleTensorLeftUnitorInv_apply, hom_id, LinearMap.id_apply]
    rw [bimoduleModuleTensorTmul_unit_smul]
    simp only [LinearEquiv.apply_symm_apply]
  inv_hom_id := by
    apply hom_ext
    ext n
    simp only [hom_comp, LinearMap.comp_apply, bimoduleModuleTensorLeftUnitorInv_apply,
      bimoduleModuleTensorLeftUnitorHom_tmul, LinearEquiv.symm_apply_apply,
      one_smul, hom_id, LinearMap.id_apply]

@[simp]
theorem bimoduleModuleTensorLeftUnitor_hom :
    (bimoduleModuleTensorLeftUnitor.{v} Γ N).hom =
      bimoduleModuleTensorLeftUnitorHom.{v} Γ N := (rfl)

@[simp]
theorem bimoduleModuleTensorLeftUnitor_inv :
    (bimoduleModuleTensorLeftUnitor.{v} Γ N).inv =
      bimoduleModuleTensorLeftUnitorInv.{v} Γ N := (rfl)

/-- Evaluation of a left unit commutes with every graded left-module map. -/
@[reassoc (attr := simp)]
theorem bimoduleModuleTensorLeftUnitorHom_naturality
    {N' : GradedModuleCat.{max v uA} Γ.piece} (f : N ⟶ N') :
    bimoduleModuleTensorMap Γ Γ (𝟙 (bimoduleUnit.{v} Γ)) f ≫
        bimoduleModuleTensorLeftUnitorHom.{v} Γ N' =
      bimoduleModuleTensorLeftUnitorHom.{v} Γ N ≫ f := by
  apply bimoduleModuleTensor_hom_ext Γ Γ
  intro x n
  simp only [hom_comp, LinearMap.comp_apply, bimoduleModuleTensorMap_tmul,
    hom_id, LinearMap.id_apply, bimoduleModuleTensorLeftUnitorHom_tmul, map_smul]

/-- The regular bimodule acts as the identity functor on graded left modules. -/
def bimoduleModuleTensorLeftUnitorNatIso :
    (bimoduleModuleTensor.{max v uA, max v uA} Γ Γ).obj (bimoduleUnit.{v} Γ) ≅
      𝟭 (GradedModuleCat.{max v uA} Γ.piece) :=
  NatIso.ofComponents (fun N ↦
    eqToIso (bimoduleModuleTensor_obj_obj Γ Γ (M := bimoduleUnit.{v} Γ) (N := N)) ≪≫
      bimoduleModuleTensorLeftUnitor.{v} Γ N) (by
    intro N N' f
    apply (cancel_epi (eqToHom
      (bimoduleModuleTensor_obj_obj Γ Γ (M := bimoduleUnit.{v} Γ) (N := N)).symm)).1
    simp only [Iso.trans_hom, eqToIso.hom, bimoduleModuleTensor_obj_map,
      Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Functor.id_map]
    simpa only [bimoduleModuleTensorLeftUnitor_hom] using
      bimoduleModuleTensorLeftUnitorHom_naturality.{v} Γ N f)

/-- The forward natural comparison is evaluation after the public object transport. -/
@[simp, reassoc]
theorem bimoduleModuleTensorLeftUnitorNatIso_hom_app :
    (bimoduleModuleTensorLeftUnitorNatIso.{v} Γ).hom.app N =
      eqToHom (bimoduleModuleTensor_obj_obj Γ Γ (M := bimoduleUnit.{v} Γ) (N := N)) ≫
        (bimoduleModuleTensorLeftUnitor.{v} Γ N).hom := by
  simp only [bimoduleModuleTensorLeftUnitorNatIso, NatIso.ofComponents_hom_app,
    Iso.trans_hom, eqToIso.hom]

/-- The inverse natural comparison inserts the unit before the inverse object transport. -/
@[simp, reassoc]
theorem bimoduleModuleTensorLeftUnitorNatIso_inv_app :
    (bimoduleModuleTensorLeftUnitorNatIso.{v} Γ).inv.app N =
      (bimoduleModuleTensorLeftUnitor.{v} Γ N).inv ≫
        eqToHom (bimoduleModuleTensor_obj_obj Γ Γ (M := bimoduleUnit.{v} Γ) (N := N)).symm := by
  simp only [bimoduleModuleTensorLeftUnitorNatIso, NatIso.ofComponents_inv_app,
    Iso.trans_inv, eqToIso.inv]

end TauCeti.GradedModuleCat
