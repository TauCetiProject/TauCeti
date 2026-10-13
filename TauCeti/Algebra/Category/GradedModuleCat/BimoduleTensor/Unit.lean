/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.BimoduleTensor.Basic
public import TauCeti.Algebra.CentralSimple.Bimodule
public import Mathlib.Algebra.Module.ULift

/-!
# Graded units for bimodule tensor composition

The regular bimodule of a graded algebra is the unit for balanced tensor composition.
Its carrier is lifted so that it lies in the same universe as the modules being tensored.
The grading is transported from the algebra; no internal shift is introduced.

The construction uses `Bimodule.of`, `InternalGrading.map`, and the balanced homogeneous
lift. The unit identities are the graded enveloping-module versions of
`BalancedTensorProduct.lid` and `BalancedTensorProduct.rid`.

Both unit isomorphisms have public evaluation and insertion formulas. Their evaluation
maps are natural in graded bimodule maps; on the tensor of two regular bimodules, left
and right evaluation agree.
-/

public section

noncomputable section

namespace TauCeti.GradedModuleCat

open CategoryTheory MulOpposite
open scoped TensorProduct

universe v uk uA uB

variable {k : Type uk} {A : Type uA} [CommRing k] [Ring A] [Algebra k A]

private abbrev unitEquiv : A ≃ₗ[k] ULift.{v} (Bimodule (AlgHom.id k A)) :=
  (Bimodule.of (AlgHom.id k A)).trans ULift.moduleEquiv.symm

private theorem unitEquiv_symm_smul (a : A) (b : Aᵐᵒᵖ)
    (x : ULift.{v} (Bimodule (AlgHom.id k A))) :
    unitEquiv.symm ((a ⊗ₜ[k] b) • x) = a * unitEquiv.symm x * unop b := by
  exact Bimodule.symm_smul (AlgHom.id k A) a b x.down

variable (Γ : InternalGrading k A) [GradedAlgebra Γ.piece]

/-- The universe-lifted regular graded bimodule of `A`. -/
-- The concrete carrier and transported grading are used by the unit computation API.
@[expose]
def bimoduleUnit : GradedModuleCat.{max v uA} (Γ.tensorProduct Γ.opposite).piece where
  carrier := ULift.{v} (Bimodule (AlgHom.id k A))
  grading := Γ.map ((Bimodule.of (AlgHom.id k A)).trans ULift.moduleEquiv.symm)
  gradedSMul := ⟨fun {p q} {z x} hz hx ↦ by
    rw [InternalGrading.tensorProduct_piece_eq_iSup] at hz
    have hx' := (Γ.mem_map_piece_iff unitEquiv q x).1 hx
    refine (iSup_le fun r ↦ Submodule.map₂_le.mpr fun a ha b hb ↦ ?_ :
      _ ≤ ((Γ.map unitEquiv).piece (p + q)).comap
        (LinearMap.applyₗ (R := k) x ∘ₗ
          (Algebra.lsmul k k (ULift.{v} (Bimodule (AlgHom.id k A)))
            (A := A ⊗[k] Aᵐᵒᵖ)).toLinearMap)) hz
    simp only [Submodule.mem_comap, LinearMap.comp_apply, LinearMap.applyₗ_apply_apply,
      TensorProduct.mk_apply, AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
    apply (Γ.mem_map_piece_iff unitEquiv (p + q) _).2
    rw [unitEquiv_symm_smul]
    have hb' := (Γ.mem_opposite_piece_iff (p - r) b).1 hb
    have h := SetLike.GradedMul.mul_mem (SetLike.GradedMul.mul_mem ha hx') hb'
    have hdeg : r + q + (p - r) = p + q := by omega
    simpa only [hdeg] using h⟩

/-- The unit bimodule has the same ground-ring module as the algebra. -/
def bimoduleUnitEquiv : A ≃ₗ[k] bimoduleUnit.{v} Γ := unitEquiv

/-- The algebra element in the concrete lifted regular-bimodule carrier. -/
theorem bimoduleUnitEquiv_apply (a : A) :
    bimoduleUnitEquiv.{v} Γ a = ULift.up (Bimodule.of (AlgHom.id k A) a) := (rfl)

/-- Read the algebra element from the concrete lifted regular-bimodule carrier. -/
theorem bimoduleUnitEquiv_symm_apply (x : bimoduleUnit.{v} Γ) :
    (bimoduleUnitEquiv.{v} Γ).symm x = (Bimodule.of (AlgHom.id k A)).symm x.down := (rfl)

@[simp]
theorem bimoduleUnitEquiv_symm_smul (a : A) (b : Aᵐᵒᵖ) (x : bimoduleUnit.{v} Γ) :
    (bimoduleUnitEquiv.{v} Γ).symm ((a ⊗ₜ[k] b) • x) =
      a * (bimoduleUnitEquiv.{v} Γ).symm x * unop b :=
  unitEquiv_symm_smul a b x

@[simp]
theorem tmul_smul_bimoduleUnitEquiv (a : A) (b : Aᵐᵒᵖ) (x : A) :
    (a ⊗ₜ[k] b) • bimoduleUnitEquiv.{v} Γ x =
      bimoduleUnitEquiv.{v} Γ (a * x * unop b) := by
  apply (bimoduleUnitEquiv.{v} Γ).symm.injective
  rw [bimoduleUnitEquiv_symm_smul.{v} Γ, LinearEquiv.symm_apply_apply,
    LinearEquiv.symm_apply_apply]

/-- Homogeneous membership in the regular bimodule is membership in the algebra grading. -/
@[simp]
theorem mem_bimoduleUnit_piece_iff (p : ℤ) (x : bimoduleUnit.{v} Γ) :
    x ∈ (bimoduleUnit.{v} Γ).grading.piece p ↔ (bimoduleUnitEquiv.{v} Γ).symm x ∈ Γ.piece p :=
  Γ.mem_map_piece_iff unitEquiv p x

section LeftUnitor

variable {B : Type uB} [Ring B] [Algebra k B]
  (Δ : InternalGrading k B) [GradedAlgebra Δ.piece]
  (M : GradedModuleCat.{max v uA} (Γ.tensorProduct Δ.opposite).piece)

/-- Restrict the envelope action to the left algebra factor. -/
local instance : Module A M :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- The restricted left action respects the ground-ring action. -/
local instance : IsScalarTower k A M :=
  TauCeti.Algebra.TensorProduct.moduleLeftIsScalarTower (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- Restrict the envelope action to the right algebra factor. -/
local instance : Module Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- The restricted left and right actions commute. -/
local instance : SMulCommClass A Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := A) (B := Bᵐᵒᵖ) M

private abbrev leftUnitAction : bimoduleUnit.{v} Γ →ₗ[k] M →ₗ[k] M :=
  (Algebra.lsmul k k M (A := A)).toLinearMap.comp (bimoduleUnitEquiv.{v} Γ).symm.toLinearMap

private theorem leftUnitAction_degree {p q : ℤ} {x : bimoduleUnit.{v} Γ} {m : M}
    (hx : x ∈ (bimoduleUnit.{v} Γ).grading.piece p) (hm : m ∈ M.grading.piece q) :
    leftUnitAction.{v} Γ Δ M x m ∈ M.grading.piece (p + q) := by
  have hx' := (mem_bimoduleUnit_piece_iff.{v} Γ p x).1 hx
  have h1 : (1 : Bᵐᵒᵖ) ∈ Δ.opposite.piece 0 :=
    (Δ.mem_opposite_piece_iff 0 1).2 (SetLike.one_mem_graded Δ.piece)
  have h := Γ.tmul_mem_tensorProduct Δ.opposite hx' h1
  rw [add_zero] at h
  exact SetLike.GradedSMul.smul_mem h hm

/-- Evaluate the regular left tensor factor by its action on the second factor. -/
def bimoduleTensorLeftUnitorHom : bimoduleTensorObj Γ Γ Δ (bimoduleUnit.{v} Γ) M ⟶ M :=
  bimoduleTensorLift Γ Γ Δ (leftUnitAction.{v} Γ Δ M)
    (fun a x m ↦ by
      simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
      rw [bimoduleUnitEquiv_symm_smul.{v} Γ]
      simp only [unop_op, one_mul, ← TauCeti.Algebra.TensorProduct.smul_moduleLeft]
      exact mul_smul _ a m)
    (fun a x m ↦ by
      simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
      rw [bimoduleUnitEquiv_symm_smul.{v} Γ]
      simp only [unop_one, mul_one, ← TauCeti.Algebra.TensorProduct.smul_moduleLeft]
      exact mul_smul a _ m)
    (fun b x m ↦ by
      simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
        ← TauCeti.Algebra.TensorProduct.smul_moduleRight]
      exact smul_comm _ b m)
    (leftUnitAction_degree.{v} Γ Δ M)

@[simp]
theorem bimoduleTensorLeftUnitorHom_tmul (x : bimoduleUnit.{v} Γ) (m : M) :
    (bimoduleTensorLeftUnitorHom.{v} Γ Δ M).hom
      (bimoduleTensorTmul Γ Γ Δ (bimoduleUnit.{v} Γ) M x m) =
      ((bimoduleUnitEquiv.{v} Γ).symm x ⊗ₜ[k] (1 : Bᵐᵒᵖ)) • m := by
  rw [bimoduleTensorLeftUnitorHom, bimoduleTensorLift_tmul]
  simp only [leftUnitAction, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
    TauCeti.Algebra.TensorProduct.smul_moduleLeft]

private abbrev leftUnitInsertBase :
    M →ₗ[k] bimoduleTensorObj Γ Γ Δ (bimoduleUnit.{v} Γ) M where
  toFun m := bimoduleTensorTmul Γ Γ Δ (bimoduleUnit.{v} Γ) M (bimoduleUnitEquiv.{v} Γ 1) m
  map_add' m n := bimoduleTensorTmul_add_right Γ Γ Δ (bimoduleUnit.{v} Γ) M _ m n
  map_smul' c m := bimoduleTensorTmul_smul_right Γ Γ Δ (bimoduleUnit.{v} Γ) M c _ m

private theorem leftUnitInsertBase_apply (m : M) :
    leftUnitInsertBase.{v} Γ Δ M m =
      bimoduleTensorTmul Γ Γ Δ (bimoduleUnit.{v} Γ) M (bimoduleUnitEquiv.{v} Γ 1) m := rfl

private abbrev leftUnitInsertLinear :
    M →ₗ[A ⊗[k] Bᵐᵒᵖ] bimoduleTensorObj Γ Γ Δ (bimoduleUnit.{v} Γ) M :=
  TauCeti.Algebra.TensorProduct.linearMapOfFactors M (leftUnitInsertBase.{v} Γ Δ M)
    (fun a m ↦ by
      simp only [leftUnitInsertBase_apply]
      have hb := bimoduleTensorTmul_balance Γ Γ Δ (bimoduleUnit.{v} Γ) M a
        (bimoduleUnitEquiv.{v} Γ 1) m
      have ho := tmul_smul_bimoduleTensorTmul Γ Γ Δ (bimoduleUnit.{v} Γ) M a 1
        (bimoduleUnitEquiv.{v} Γ 1) m
      simp only [tmul_smul_bimoduleUnitEquiv.{v} Γ, one_mul, mul_one, unop_op, unop_one,
        ← Algebra.TensorProduct.one_def, one_smul] at hb ho
      exact hb.symm.trans ho.symm)
    (fun b m ↦ by
      simp only [leftUnitInsertBase_apply]
      have h := tmul_smul_bimoduleTensorTmul Γ Γ Δ (bimoduleUnit.{v} Γ) M 1 b
        (bimoduleUnitEquiv.{v} Γ 1) m
      simpa only [← Algebra.TensorProduct.one_def, one_smul] using h.symm)

/-- Insert `1` in the regular left tensor factor, as a degree-zero bimodule map. -/
def bimoduleTensorLeftUnitorInv : M ⟶ bimoduleTensorObj Γ Γ Δ (bimoduleUnit.{v} Γ) M :=
  ofHom (leftUnitInsertLinear.{v} Γ Δ M) (LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
    rw [TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply, leftUnitInsertBase_apply]
    have h1 : bimoduleUnitEquiv.{v} Γ 1 ∈ (bimoduleUnit.{v} Γ).grading.piece 0 :=
      (mem_bimoduleUnit_piece_iff.{v} Γ 0 _).2 (by
        simpa only [LinearEquiv.symm_apply_apply] using SetLike.one_mem_graded Γ.piece)
    simpa only [zero_add, add_zero] using
      bimoduleTensorTmul_mem Γ Γ Δ (bimoduleUnit.{v} Γ) M h1 hm)

@[simp]
theorem bimoduleTensorLeftUnitorInv_apply (m : M) :
    (bimoduleTensorLeftUnitorInv.{v} Γ Δ M).hom m =
      bimoduleTensorTmul Γ Γ Δ (bimoduleUnit.{v} Γ) M (bimoduleUnitEquiv.{v} Γ 1) m := by
  rw [bimoduleTensorLeftUnitorInv, hom_ofHom, leftUnitInsertLinear,
    TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply, leftUnitInsertBase_apply]

/-- The regular graded bimodule is a left unit for balanced tensor composition. -/
def bimoduleTensorLeftUnitor : bimoduleTensorObj Γ Γ Δ (bimoduleUnit.{v} Γ) M ≅ M where
  hom := bimoduleTensorLeftUnitorHom.{v} Γ Δ M
  inv := bimoduleTensorLeftUnitorInv.{v} Γ Δ M
  hom_inv_id := by
    apply bimoduleTensor_hom_ext Γ Γ Δ
    intro x m
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorLeftUnitorHom_tmul,
      bimoduleTensorLeftUnitorInv_apply, hom_id, LinearMap.id_apply]
    have h := bimoduleTensorTmul_balance Γ Γ Δ (bimoduleUnit.{v} Γ) M
      ((bimoduleUnitEquiv.{v} Γ).symm x) (bimoduleUnitEquiv.{v} Γ 1) m
    simpa only [tmul_smul_bimoduleUnitEquiv.{v} Γ, one_mul, unop_op,
      LinearEquiv.apply_symm_apply] using h.symm
  inv_hom_id := by
    apply hom_ext
    apply LinearMap.ext
    intro m
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorLeftUnitorInv_apply,
      bimoduleTensorLeftUnitorHom_tmul, LinearEquiv.symm_apply_apply,
      ← Algebra.TensorProduct.one_def, one_smul, hom_id, LinearMap.id_apply]

@[simp]
theorem bimoduleTensorLeftUnitor_hom :
    (bimoduleTensorLeftUnitor.{v} Γ Δ M).hom = bimoduleTensorLeftUnitorHom.{v} Γ Δ M := (rfl)

@[simp]
theorem bimoduleTensorLeftUnitor_inv :
    (bimoduleTensorLeftUnitor.{v} Γ Δ M).inv = bimoduleTensorLeftUnitorInv.{v} Γ Δ M := (rfl)

/-- Evaluation of a left unit commutes with every graded bimodule map. -/
@[reassoc (attr := simp)]
theorem bimoduleTensorLeftUnitorHom_naturality
    {N : GradedModuleCat.{max v uA} (Γ.tensorProduct Δ.opposite).piece} (f : M ⟶ N) :
    bimoduleTensorMap Γ Γ Δ (𝟙 (bimoduleUnit.{v} Γ)) f ≫
        bimoduleTensorLeftUnitorHom.{v} Γ Δ N =
      bimoduleTensorLeftUnitorHom.{v} Γ Δ M ≫ f := by
  apply bimoduleTensor_hom_ext Γ Γ Δ
  intro x m
  simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorMap_tmul, hom_id,
    LinearMap.id_apply, bimoduleTensorLeftUnitorHom_tmul, map_smul]

end LeftUnitor

section RightUnitor

variable {B : Type uB} [Ring B] [Algebra k B]
  (Δ : InternalGrading k B) [GradedAlgebra Δ.piece]
  (M : GradedModuleCat.{max v uB} (Γ.tensorProduct Δ.opposite).piece)

/-- Restrict the envelope action to the left algebra factor. -/
local instance : Module A M :=
  TauCeti.Algebra.TensorProduct.moduleLeft (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- Restrict the envelope action to the right algebra factor. -/
local instance : Module Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRight (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- The restricted right action respects the ground-ring action. -/
local instance : IsScalarTower k Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleRightIsScalarTower (k := k) (A := A) (B := Bᵐᵒᵖ) M

/-- The restricted left and right actions commute. -/
local instance : SMulCommClass A Bᵐᵒᵖ M :=
  TauCeti.Algebra.TensorProduct.moduleSMulCommClass (k := k) (A := A) (B := Bᵐᵒᵖ) M

private abbrev rightUnitAction : M →ₗ[k] bimoduleUnit.{v} Δ →ₗ[k] M :=
  ((Algebra.lsmul k k M (A := Bᵐᵒᵖ)).toLinearMap.comp
    ((bimoduleUnitEquiv.{v} Δ).symm.trans (opLinearEquiv k)).toLinearMap).flip

private theorem rightUnitAction_degree {p q : ℤ} {m : M} {x : bimoduleUnit.{v} Δ}
    (hm : m ∈ M.grading.piece p) (hx : x ∈ (bimoduleUnit.{v} Δ).grading.piece q) :
    rightUnitAction.{v} Γ Δ M m x ∈ M.grading.piece (p + q) := by
  simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
    TauCeti.Algebra.TensorProduct.smul_moduleRight]
  have hx' := (mem_bimoduleUnit_piece_iff.{v} Δ q x).1 hx
  have h1 : (1 : A) ∈ Γ.piece 0 := SetLike.one_mem_graded Γ.piece
  have hxop : op ((bimoduleUnitEquiv.{v} Δ).symm x) ∈ Δ.opposite.piece q :=
    (Δ.mem_opposite_piece_iff q _).2 (by simpa only [unop_op] using hx')
  have h := Γ.tmul_mem_tensorProduct Δ.opposite h1 hxop
  rw [zero_add] at h
  simpa only [vadd_eq_add, add_comm] using SetLike.GradedSMul.smul_mem h hm

/-- Evaluate the regular right tensor factor by its right action on the first factor. -/
def bimoduleTensorRightUnitorHom : bimoduleTensorObj Γ Δ Δ M (bimoduleUnit.{v} Δ) ⟶ M :=
  bimoduleTensorLift Γ Δ Δ (rightUnitAction.{v} Γ Δ M)
    (fun b m x ↦ by
      simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
        AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
      rw [bimoduleUnitEquiv_symm_smul.{v} Δ]
      simp only [unop_one, mul_one, ← TauCeti.Algebra.TensorProduct.smul_moduleRight]
      rw [op_mul, mul_smul])
    (fun a m x ↦ by
      simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
        AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
        ← TauCeti.Algebra.TensorProduct.smul_moduleLeft]
      exact (smul_comm a _ m).symm)
    (fun b m x ↦ by
      simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
        LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
        AlgHom.toLinearMap_apply, Algebra.lsmul_apply]
      rw [bimoduleUnitEquiv_symm_smul.{v} Δ]
      simp only [one_mul, ← TauCeti.Algebra.TensorProduct.smul_moduleRight]
      rw [op_mul, op_unop, mul_smul])
    (rightUnitAction_degree.{v} Γ Δ M)

@[simp]
theorem bimoduleTensorRightUnitorHom_tmul (m : M) (x : bimoduleUnit.{v} Δ) :
    (bimoduleTensorRightUnitorHom.{v} Γ Δ M).hom
      (bimoduleTensorTmul Γ Δ Δ M (bimoduleUnit.{v} Δ) m x) =
      ((1 : A) ⊗ₜ[k] op ((bimoduleUnitEquiv.{v} Δ).symm x)) • m := by
  rw [bimoduleTensorRightUnitorHom, bimoduleTensorLift_tmul]
  simp only [rightUnitAction, LinearMap.flip_apply, LinearMap.comp_apply,
    LinearEquiv.coe_toLinearMap, LinearEquiv.trans_apply, coe_opLinearEquiv,
    AlgHom.toLinearMap_apply, Algebra.lsmul_apply,
    TauCeti.Algebra.TensorProduct.smul_moduleRight]

private abbrev rightUnitInsertBase :
    M →ₗ[k] bimoduleTensorObj Γ Δ Δ M (bimoduleUnit.{v} Δ) where
  toFun m := bimoduleTensorTmul Γ Δ Δ M (bimoduleUnit.{v} Δ) m (bimoduleUnitEquiv.{v} Δ 1)
  map_add' m n := bimoduleTensorTmul_add_left Γ Δ Δ M (bimoduleUnit.{v} Δ) m n _
  map_smul' c m := bimoduleTensorTmul_smul_left Γ Δ Δ M (bimoduleUnit.{v} Δ) c m _

private theorem rightUnitInsertBase_apply (m : M) :
    rightUnitInsertBase.{v} Γ Δ M m =
      bimoduleTensorTmul Γ Δ Δ M (bimoduleUnit.{v} Δ) m (bimoduleUnitEquiv.{v} Δ 1) := rfl

private abbrev rightUnitInsertLinear :
    M →ₗ[A ⊗[k] Bᵐᵒᵖ] bimoduleTensorObj Γ Δ Δ M (bimoduleUnit.{v} Δ) :=
  TauCeti.Algebra.TensorProduct.linearMapOfFactors M (rightUnitInsertBase.{v} Γ Δ M)
    (fun a m ↦ by
      simp only [rightUnitInsertBase_apply]
      have h := tmul_smul_bimoduleTensorTmul Γ Δ Δ M (bimoduleUnit.{v} Δ) a 1 m
        (bimoduleUnitEquiv.{v} Δ 1)
      simpa only [← Algebra.TensorProduct.one_def, one_smul] using h.symm)
    (fun b m ↦ by
      simp only [rightUnitInsertBase_apply]
      have hb := bimoduleTensorTmul_balance Γ Δ Δ M (bimoduleUnit.{v} Δ) (unop b) m
        (bimoduleUnitEquiv.{v} Δ 1)
      have ho := tmul_smul_bimoduleTensorTmul Γ Δ Δ M (bimoduleUnit.{v} Δ) 1 b m
        (bimoduleUnitEquiv.{v} Δ 1)
      simp only [tmul_smul_bimoduleUnitEquiv.{v} Δ, one_mul, mul_one, unop_one, op_unop,
        ← Algebra.TensorProduct.one_def, one_smul] at hb ho
      exact hb.trans ho.symm)

/-- Insert `1` in the regular right tensor factor, as a degree-zero bimodule map. -/
def bimoduleTensorRightUnitorInv : M ⟶ bimoduleTensorObj Γ Δ Δ M (bimoduleUnit.{v} Δ) :=
  ofHom (rightUnitInsertLinear.{v} Γ Δ M) (LinearMap.isHomogeneous_def.2 fun p m hm ↦ by
    rw [TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply, rightUnitInsertBase_apply]
    have h1 : bimoduleUnitEquiv.{v} Δ 1 ∈ (bimoduleUnit.{v} Δ).grading.piece 0 :=
      (mem_bimoduleUnit_piece_iff.{v} Δ 0 _).2 (by
        simpa only [LinearEquiv.symm_apply_apply] using SetLike.one_mem_graded Δ.piece)
    simpa only [add_zero] using
      bimoduleTensorTmul_mem Γ Δ Δ M (bimoduleUnit.{v} Δ) hm h1)

@[simp]
theorem bimoduleTensorRightUnitorInv_apply (m : M) :
    (bimoduleTensorRightUnitorInv.{v} Γ Δ M).hom m =
      bimoduleTensorTmul Γ Δ Δ M (bimoduleUnit.{v} Δ) m (bimoduleUnitEquiv.{v} Δ 1) := by
  rw [bimoduleTensorRightUnitorInv, hom_ofHom, rightUnitInsertLinear,
    TauCeti.Algebra.TensorProduct.linearMapOfFactors_apply, rightUnitInsertBase_apply]

/-- The regular graded bimodule is a right unit for balanced tensor composition. -/
def bimoduleTensorRightUnitor : bimoduleTensorObj Γ Δ Δ M (bimoduleUnit.{v} Δ) ≅ M where
  hom := bimoduleTensorRightUnitorHom.{v} Γ Δ M
  inv := bimoduleTensorRightUnitorInv.{v} Γ Δ M
  hom_inv_id := by
    apply bimoduleTensor_hom_ext Γ Δ Δ
    intro m x
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorRightUnitorHom_tmul,
      bimoduleTensorRightUnitorInv_apply, hom_id, LinearMap.id_apply]
    have h := bimoduleTensorTmul_balance Γ Δ Δ M (bimoduleUnit.{v} Δ)
      ((bimoduleUnitEquiv.{v} Δ).symm x) m (bimoduleUnitEquiv.{v} Δ 1)
    simpa only [tmul_smul_bimoduleUnitEquiv.{v} Δ, mul_one, unop_one,
      LinearEquiv.apply_symm_apply] using h
  inv_hom_id := by
    apply hom_ext
    apply LinearMap.ext
    intro m
    simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorRightUnitorInv_apply,
      bimoduleTensorRightUnitorHom_tmul, LinearEquiv.symm_apply_apply, op_one,
      ← Algebra.TensorProduct.one_def, one_smul, hom_id, LinearMap.id_apply]

@[simp]
theorem bimoduleTensorRightUnitor_hom :
    (bimoduleTensorRightUnitor.{v} Γ Δ M).hom = bimoduleTensorRightUnitorHom.{v} Γ Δ M := (rfl)

@[simp]
theorem bimoduleTensorRightUnitor_inv :
    (bimoduleTensorRightUnitor.{v} Γ Δ M).inv = bimoduleTensorRightUnitorInv.{v} Γ Δ M := (rfl)

/-- Evaluation of a right unit commutes with every graded bimodule map. -/
@[reassoc (attr := simp)]
theorem bimoduleTensorRightUnitorHom_naturality
    {N : GradedModuleCat.{max v uB} (Γ.tensorProduct Δ.opposite).piece} (f : M ⟶ N) :
    bimoduleTensorMap Γ Δ Δ f (𝟙 (bimoduleUnit.{v} Δ)) ≫
        bimoduleTensorRightUnitorHom.{v} Γ Δ N =
      bimoduleTensorRightUnitorHom.{v} Γ Δ M ≫ f := by
  apply bimoduleTensor_hom_ext Γ Δ Δ
  intro m x
  simp only [hom_comp, LinearMap.comp_apply, bimoduleTensorMap_tmul, hom_id,
    LinearMap.id_apply, bimoduleTensorRightUnitorHom_tmul, map_smul]

end RightUnitor

/-- Left and right evaluation agree on the tensor of two regular graded bimodules. -/
theorem bimoduleTensorUnitHom_eq :
    bimoduleTensorLeftUnitorHom.{v} Γ Γ (bimoduleUnit.{v} Γ) =
      bimoduleTensorRightUnitorHom.{v} Γ Γ (bimoduleUnit.{v} Γ) := by
  apply bimoduleTensor_hom_ext Γ Γ Γ
  intro x y
  rw [bimoduleTensorLeftUnitorHom_tmul, bimoduleTensorRightUnitorHom_tmul]
  apply (bimoduleUnitEquiv.{v} Γ).symm.injective
  simp only [bimoduleUnitEquiv_symm_smul.{v} Γ, unop_one, mul_one, unop_op, one_mul]

end TauCeti.GradedModuleCat
