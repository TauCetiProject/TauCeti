/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import TauCeti.Algebra.Homology.DG.Algebra.Hom.Basic
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Monoidal

/-!
# DG algebras from monoid objects in DG bimodules

A monoid object in DG `(A, A)`-bimodules is a DG algebra equipped with a DG algebra map
from `A`. Its multiplication evaluates the categorical multiplication on pure balanced tensors;
its unit is the image of `1 ∈ A`. The given left and right actions are multiplication by the
image of `A`, which need not be central. Only the ground ring acts centrally.

This realizes categorical tensor-algebra constructions as concrete internally graded DG
algebras, without changing their underlying module, grading, or differential. The construction
is underived; it does not assert cofibrancy or a Calabi--Yau property.

## References

* B. Keller, *Deformed Calabi--Yau completions*, Section 4.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory MulOpposite

namespace TauCeti.DGBimoduleCat

universe uR uA

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {dA : A →ₗ[R] A}
  {hA : IsDGAlgebra 𝒜 dA}
  (M : DGBimoduleCat.{uR, uA, uA, uA} hA hA) [MonObj M]

open BalancedTensorProduct

/-- Multiplication in a DG bimodule monoid evaluates its multiplication on a pure tensor. -/
instance monObjMul : Mul M := ⟨fun x y ↦ MonObj.mul (X := M) (tmul R A x y)⟩

/-- The unit of a DG bimodule monoid is the image of the base algebra's unit. -/
instance monObjOne : One M := ⟨MonObj.one (X := M) (tensorUnitEquiv hA 1)⟩

/-- Concrete multiplication agrees with the categorical multiplication. -/
theorem monObj_mul_def (x y : M) :
    x * y = MonObj.mul (X := M) (tmul R A x y) := (rfl)

/-- Concrete one agrees with the categorical unit. -/
theorem monObj_one_def :
    (1 : M) = MonObj.one (X := M) (tensorUnitEquiv hA 1) := (rfl)

private theorem monObj_mul_assoc (x y z : M) : x * y * z = x * (y * z) := by
  have h := congrArg (fun f ↦ f (tmul R A (tmul R A x y) z)) (MonObj.mul_assoc M)
  simp only [comp_apply] at h
  rw [whiskerRight_tmul, associator_hom_tmul, whiskerLeft_tmul] at h
  exact h

/-- The categorical unit recovers the given left action by multiplication. -/
private theorem monObj_one_apply_mul (a : A) (x : M) :
    MonObj.one (X := M) (tensorUnitEquiv hA a) * x = a • x := by
  have h := congrArg (fun f ↦ f (tmul R A (tensorUnitEquiv hA a) x)) (MonObj.one_mul M)
  simp only [comp_apply] at h
  rw [whiskerRight_tmul, leftUnitor_hom_tmul] at h
  simpa only [monObj_mul_def, tensorUnitEquiv_apply, ULift.down_up] using h

/-- The categorical unit recovers the given right action by multiplication. -/
private theorem monObj_mul_one_apply (x : M) (a : A) :
    x * MonObj.one (X := M) (tensorUnitEquiv hA a) = op a • x := by
  have h := congrArg (fun f ↦ f (tmul R A x (tensorUnitEquiv hA a))) (MonObj.mul_one M)
  simp only [comp_apply] at h
  rw [whiskerLeft_tmul, rightUnitor_hom_tmul] at h
  simpa only [monObj_mul_def, tensorUnitEquiv_apply, ULift.down_up] using h

/-- A monoid object in DG bimodules is a ring on its existing additive group. -/
instance monObjRing : Ring M where
  __ := M.addCommGroup
  mul := (· * ·)
  one := 1
  mul_assoc := by exact monObj_mul_assoc M
  one_mul x := by rw [monObj_one_def, monObj_one_apply_mul, one_smul]
  mul_one x := by rw [monObj_one_def, monObj_mul_one_apply, op_one, one_smul]
  left_distrib x y z := by simp only [monObj_mul_def, tmul_add, map_add]
  right_distrib x y z := by simp only [monObj_mul_def, add_tmul, map_add]
  zero_mul x := by simp only [monObj_mul_def, zero_tmul, map_zero]
  mul_zero x := by simp only [monObj_mul_def, tmul_zero, map_zero]

/-- The ground-ring module structure on a DG bimodule monoid is an algebra structure. -/
instance monObjAlgebra : Algebra R M :=
  Algebra.ofModule
    (fun r x y ↦ by
      rw [monObj_mul_def, smul_tmul]
      exact (MonObj.mul (X := M)).val.toLinearMap.map_smul_of_tower r _)
    (fun r x y ↦ by
      rw [monObj_mul_def, tmul_smul]
      exact (MonObj.mul (X := M)).val.toLinearMap.map_smul_of_tower r _)

/-- The existing grading is multiplicative for the realized algebra. -/
instance monObjGradedAlgebra : GradedAlgebra M.grading where
  one_mem := Graded.map_mem (MonObj.one (X := M)) (tensorUnitEquiv_one_mem_grading_zero hA)
  mul_mem i j x y hx hy := by
    have ht : tmul R A x y ∈ (M ⊗ M).grading (i + j) := by
      rw [tensorObj_grading]
      exact tmul_mem_tensorObj_grading hx hy
    exact Graded.map_mem (MonObj.mul (X := M)) ht

/-- The unchanged differential makes the realized monoid a DG algebra. -/
theorem monObj_isDGAlgebra : IsDGAlgebra M.grading M.differential where
  map_mem := M.isDGRightModule.isHomogeneous.map_mem
  sq_zero := M.isDGRightModule.sq_zero
  leibniz {p x} hx y := by
    have hd : (M ⊗ M).differential (tmul R A x y) =
        tmul R A (M.differential x) y + p.negOnePow • tmul R A x (M.differential y) := by
      rw [tensorObj_differential]
      exact tensorObj_differential_tmul hx y
    rw [monObj_mul_def, map_d, hd, map_add, map_zsmul_unit]
    rfl

/-- The unit morphism of a DG bimodule monoid is a DG algebra map from the base algebra. -/
def monObjBaseHom : DGAlgHom hA (monObj_isDGAlgebra M) where
  toAlgHom := AlgHom.ofLinearMap
    (((MonObj.one (X := M)).val.toLinearMap.restrictScalars R).comp
      (tensorUnitEquiv hA).toLinearMap)
    (by rfl)
    (fun a b ↦ by
      simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
        DGRightModuleHom.coe_toLinearMap, DGBimoduleHom.coe_val]
      rw [monObj_one_apply_mul]
      rw [← map_smul_left]
      congr 1
      simpa only [op_one, one_smul, mul_one] using
        (tensorUnitEquiv_smul hA a 1 b).symm)
  map_mem {p a} ha := by
    apply Graded.map_mem (MonObj.one (X := M))
    exact (mem_tensorUnit_grading_iff hA p _).2
      (by simpa only [LinearEquiv.coe_coe, tensorUnitEquiv_apply, ULift.down_up] using ha)
  map_d' a := by
    -- Expose evaluation through the graded homomorphism and composed linear map wrappers.
    change M.differential (MonObj.one (X := M) (tensorUnitEquiv hA a)) =
      MonObj.one (X := M) (tensorUnitEquiv hA (dA a))
    rw [map_d]
    congr 1
    exact (tensorUnit_differential_apply hA _).trans
      (by rw [tensorUnitEquiv_apply, tensorUnitEquiv_apply])

/-- The base map is the categorical unit evaluated on the lifted base element. -/
theorem monObjBaseHom_apply (a : A) :
    monObjBaseHom M a = MonObj.one (X := M) (tensorUnitEquiv hA a) := (rfl)

/-- Left multiplication by a base element is the original left action. -/
@[simp]
theorem monObjBaseHom_mul (a : A) (x : M) : monObjBaseHom M a * x = a • x := by
  rw [monObjBaseHom_apply, monObj_one_apply_mul]

/-- Right multiplication by a base element is the original right action. -/
@[simp]
theorem mul_monObjBaseHom (x : M) (a : A) : x * monObjBaseHom M a = op a • x := by
  rw [monObjBaseHom_apply, monObj_mul_one_apply]

variable {M} {N : DGBimoduleCat.{uR, uA, uA, uA} hA hA} [MonObj N]

/-- A morphism of DG bimodule monoids realizes as a DG algebra morphism. -/
def monObjMap (f : M ⟶ N) [IsMonHom f] :
    DGAlgHom (monObj_isDGAlgebra M) (monObj_isDGAlgebra N) where
  toAlgHom := AlgHom.ofLinearMap (f.val.toLinearMap.restrictScalars R)
    (by
      have h := congrArg (fun g ↦ g (tensorUnitEquiv hA 1)) (IsMonHom.one_hom f)
      simpa only [LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val, comp_apply, ← monObj_one_def] using h)
    (fun x y ↦ by
      have h := congrArg (fun g ↦ g (tmul R A x y)) (IsMonHom.mul_hom f)
      simpa only [LinearMap.restrictScalars_apply, DGRightModuleHom.coe_toLinearMap,
        DGBimoduleHom.coe_val, comp_apply, tensorHom_tmul, ← monObj_mul_def] using h)
  map_mem := Graded.map_mem f
  map_d' := map_d f

/-- Realization does not change the function underlying a morphism. -/
@[simp]
theorem monObjMap_apply (f : M ⟶ N) [IsMonHom f] (x : M) : monObjMap f x = f x := (rfl)

/-- Morphisms of DG bimodule monoids commute with the base algebra maps. -/
@[simp]
theorem monObjMap_base (f : M ⟶ N) [IsMonHom f] (a : A) :
    f (monObjBaseHom M a) = monObjBaseHom N a := by
  have h := congrArg (fun g ↦ g (tensorUnitEquiv hA a)) (IsMonHom.one_hom f)
  simpa only [comp_apply, monObjBaseHom_apply] using h

/-- Realization preserves identity morphisms. -/
@[simp]
theorem monObjMap_id : monObjMap (𝟙 M) = DGAlgHom.id (monObj_isDGAlgebra M) := by
  ext x
  simp

/-- Realization preserves composition of monoid morphisms. -/
@[simp]
theorem monObjMap_comp {P : DGBimoduleCat.{uR, uA, uA, uA} hA hA} [MonObj P]
    (f : M ⟶ N) (g : N ⟶ P) [IsMonHom f] [IsMonHom g] :
    monObjMap (f ≫ g) = (monObjMap g).comp (monObjMap f) := by
  ext x
  simp

end TauCeti.DGBimoduleCat
