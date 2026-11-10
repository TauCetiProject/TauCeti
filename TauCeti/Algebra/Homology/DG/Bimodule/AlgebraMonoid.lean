/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import TauCeti.Algebra.Homology.DG.Bimodule.OfHom
public import TauCeti.Algebra.Homology.DG.Module.Right.Restriction.Basic
public import TauCeti.Algebra.Homology.DG.Bimodule.TensorProduct.Monoidal

/-!
# DG algebras as monoids in bimodules over their base

A DG algebra map `f : A → B` makes `B` a monoid in DG `(A,A)`-bimodules: both actions
are multiplication through `f`, the unit is `f`, and multiplication is the balanced product.
The given grading and differential on `B` are retained. This lets universal properties stated
for monoid objects accept native DG algebra targets. No centrality of the image of `A`,
flatness, or field hypothesis is needed.

The carrier reuses the right restriction-of-scalars wrapper. Its left action is also restricted
through `f`. Open the scope `TauCeti.DGAlgHom` to use the additional left-action instances on
this wrapper, including when forming balanced pure tensors of its elements.
Tensor products and the monoidal coherence maps are the existing balanced DG bimodule
constructions; no derived or completed tensor product is asserted.

## References

* B. Keller, *Deriving DG categories*, Sections 2 and 6.1.
* B. Keller, *Deformed Calabi--Yau completions*, Section 4.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory MulOpposite

namespace TauCeti.DGAlgHom

universe uR u

variable {R : Type uR} {A B : Type u} [CommRing R] [Ring A] [Ring B]
  [Algebra R A] [Algebra R B] {𝒜 : ℤ → Submodule R A} {ℬ : ℤ → Submodule R B}
  [GradedAlgebra 𝒜] [GradedAlgebra ℬ] {dA : A →ₗ[R] A} {dB : B →ₗ[R] B}
  {hA : IsDGAlgebra 𝒜 dA} {hB : IsDGAlgebra ℬ dB}
  (f : DGAlgHom hA hB)

open DGRightModule

local notation "T" => RestrictScalars f B
local notation "E" => RestrictScalars.linearEquiv f B
local notation "Γ" => IsDGRightModule.restrictScalarsGrading (ℳ := ℬ) f
local notation "D" => IsDGRightModule.restrictScalarsDifferential (dM := dB) f

/-- Left multiplication through the base map on the restricted target carrier. -/
scoped instance algebraBimoduleLeftModule : Module A T :=
  letI := Module.compHom B f.toGradedAlgHom.toAlgHom.toRingHom
  AddEquiv.module A
    { toFun := RestrictScalars.val, invFun := RestrictScalars.mk,
      left_inv _ := rfl, right_inv _ := rfl, map_add' _ _ := rfl }

/-- On underlying elements, the left action is multiplication through the base map. -/
@[simp]
theorem algebraBimodule_val_smul (a : A) (x : T) : (a • x).val = f a * x.val := (rfl)

/-- The restricted left action extends the original ground-ring action. -/
scoped instance : IsScalarTower R A T :=
  IsScalarTower.of_algebraMap_smul fun r x ↦ by
    apply RestrictScalars.ext
    rw [algebraBimodule_val_smul, RestrictScalars.val_smul, AlgHomClass.commutes]
    exact (Algebra.smul_def r x.val).symm

/-- Left and right multiplication through the base map commute. -/
scoped instance : SMulCommClass A Aᵐᵒᵖ T where
  smul_comm a b x := by
    refine MulOpposite.rec' (fun b ↦ ?_) b
    apply RestrictScalars.ext
    simp only [algebraBimodule_val_smul, RestrictScalars.val_op_smul, op_smul_eq_mul]
    exact (mul_assoc _ _ _).symm

/-- The left action through a graded algebra map respects the restricted grading. -/
scoped instance : SetLike.GradedSMul 𝒜 Γ where
  smul_mem {i j a x} ha hx := by
    rw [IsDGRightModule.mem_restrictScalarsGrading_iff] at hx ⊢
    rw [RestrictScalars.linearEquiv_apply] at hx ⊢
    rw [algebraBimodule_val_smul]
    have h := f.bimoduleGradedSMulLeft.smul_mem ha
      ((f.mem_bimoduleGrading_iff).2
        (by simpa only [LinearEquiv.symm_apply_apply] using hx) :
          Bimodule.of f.toGradedAlgHom.toAlgHom x.val ∈ f.bimoduleGrading j)
    simpa only [mem_bimoduleGrading_iff, Algebra.TensorProduct.smul_moduleLeft,
      Bimodule.symm_smul, LinearEquiv.symm_apply_apply, unop_one, mul_one,
      GradedAlgHom.coe_toAlgHom, coe_toGradedAlgHom] using h

/-- The two actions restricted through a DG algebra map satisfy both DG Leibniz rules. -/
theorem isDGBimodule_algebraBimodule : IsDGBimodule hA hA Γ D where
  toIsDGLeftModule :=
    { isHomogeneous := (hB.isDGRightModule.restrictScalars f).isHomogeneous
      sq_zero := (hB.isDGRightModule.restrictScalars f).sq_zero
      leibniz := fun ha x ↦ by
        apply RestrictScalars.ext
        simp only [IsDGRightModule.val_restrictScalarsDifferential,
          algebraBimodule_val_smul, RestrictScalars.val_add, Units.smul_def,
          RestrictScalars.val_zsmul]
        simpa only [bimoduleOf_symm_bimoduleDifferential, map_add, Units.smul_def,
          map_zsmul, Algebra.TensorProduct.smul_moduleLeft, Bimodule.symm_smul,
          LinearEquiv.symm_apply_apply, unop_one, mul_one,
          GradedAlgHom.coe_toAlgHom, coe_toGradedAlgHom] using
          congrArg (Bimodule.of f.toGradedAlgHom.toAlgHom).symm
            (f.isDGBimodule.leibniz ha (Bimodule.of f.toGradedAlgHom.toAlgHom x.val)) }
  leibniz_right := (hB.isDGRightModule.restrictScalars f).leibniz

/-- A DG algebra under `A` as an `(A,A)`-DG bimodule, with both actions through its base map.
The abbreviation retains the restriction-of-scalars carrier and its evaluation interface. -/
abbrev algebraBimodule : DGBimoduleCat.{uR, u, u, u} hA hA :=
  DGBimoduleCat.of (isDGBimodule_algebraBimodule f)

open BalancedTensorProduct

attribute [local instance 100] BalancedTensorProduct.leftModule
  BalancedTensorProduct.rightModule BalancedTensorProduct.leftIsScalarTower
  BalancedTensorProduct.rightIsScalarTower BalancedTensorProduct.outerSMulCommClass
attribute [local instance] BalancedTensorProduct.tensorGradedOuterLeft
  BalancedTensorProduct.tensorGradedOuterRight

private def mulBilinear : T →ₗ[R] T →ₗ[R] T :=
  ((LinearMap.mul R B).compl₁₂ (E).toLinearMap (E).toLinearMap).compr₂ (E).symm.toLinearMap

private theorem mulBilinear_apply (x y : T) : mulBilinear f x y = (E).symm (x.val * y.val) := by
  simp [mulBilinear, RestrictScalars.linearEquiv_apply]

private theorem mulBilinear_balanced (a : A) (x y : T) :
    mulBilinear f (op a • x) y = mulBilinear f x (a • y) := by
  rw [mulBilinear_apply, mulBilinear_apply, RestrictScalars.val_op_smul,
    algebraBimodule_val_smul]
  exact congrArg (E).symm (mul_assoc _ _ _)

private def mulLinearMap :
    DGBimoduleCat.tensorObj f.algebraBimodule f.algebraBimodule →ₗ[Aᵐᵒᵖ] T where
  toFun := lift (mulBilinear f) (mulBilinear_balanced f)
  map_add' := map_add _
  map_smul' a z := lift_smul_right Aᵐᵒᵖ (mulBilinear f) (mulBilinear_balanced f)
    (fun a x y ↦ by
      refine MulOpposite.rec' (fun a ↦ ?_) a
      apply (E).injective
      simp only [mulBilinear_apply,
        RestrictScalars.linearEquiv_apply, RestrictScalars.val_op_smul,
        RestrictScalars.linearEquiv_symm_apply, op_smul_eq_mul]
      exact (mul_assoc _ _ _).symm) a z

private theorem mulLinearMap_tmul (x y : T) :
    mulLinearMap f (tmul R A x y) = (E).symm (x.val * y.val) := by
  rw [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, lift_tmul, mulBilinear_apply]

private instance : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece
    (InternalGrading.ofDecomposition Γ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

private instance : SetLike.GradedSMul 𝒜 (InternalGrading.ofDecomposition Γ).piece := by
  rw [InternalGrading.ofDecomposition_piece]
  infer_instance

/-- Multiplication of the target DG algebra, balanced over its base algebra. -/
private def algebraBimoduleMul :
    DGBimoduleCat.tensorObj f.algebraBimodule f.algebraBimodule ⟶ f.algebraBimodule := by
  refine ⟨{ toLinearMap := mulLinearMap f, map_mem' := ?_, map_d' := ?_ }, ?_⟩
  · intro p z hz
    have h := map_mem_of_tmul (𝒜 := 𝒜)
      (InternalGrading.ofDecomposition Γ) (InternalGrading.ofDecomposition Γ) Γ
      (lift (mulBilinear f) (mulBilinear_balanced f)) 0
      (fun {q r} {x y} hx hy ↦ by
        rw [lift_tmul, mulBilinear_apply, IsDGRightModule.mem_restrictScalarsGrading_iff]
        simp only [RestrictScalars.linearEquiv_apply, RestrictScalars.linearEquiv_symm_apply]
        rw [InternalGrading.ofDecomposition_piece,
          IsDGRightModule.mem_restrictScalarsGrading_iff,
          RestrictScalars.linearEquiv_apply] at hx hy
        simpa only [add_zero] using SetLike.GradedMul.mul_mem hx hy)
      (by simpa only [InternalGrading.ofDecomposition_piece] using hz)
    simpa only [mulLinearMap, LinearMap.coe_mk, AddHom.coe_mk, add_zero] using h
  · intro z
    induction z using BalancedTensorProduct.induction_on with
    | ht x y =>
        induction x using DirectSum.Decomposition.inductionOn Γ with
        | zero => simp
        | @homogeneous p x =>
            rw [DGBimoduleCat.tensorObj_differential_tmul x.2, map_add, map_zsmul_unit,
              mulLinearMap_tmul, mulLinearMap_tmul, mulLinearMap_tmul]
            apply (E).injective
            simp only [RestrictScalars.linearEquiv_apply,
              IsDGRightModule.val_restrictScalarsDifferential,
              RestrictScalars.linearEquiv_symm_apply, RestrictScalars.val_add, Units.smul_def,
              RestrictScalars.val_zsmul]
            have hx := (IsDGRightModule.mem_restrictScalarsGrading_iff f).1 x.2
            rw [RestrictScalars.linearEquiv_apply] at hx
            exact hB.leibniz hx y.val
        | add x x' hx hx' => simp only [add_tmul, map_add, hx, hx']
    | ha x y hx hy => simp only [map_add, hx, hy]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a z
    exact lift_smul_left A (mulBilinear f) (mulBilinear_balanced f)
      (fun a x y ↦ by
        apply (E).injective
        simp only [mulBilinear_apply,
          RestrictScalars.linearEquiv_apply, algebraBimodule_val_smul,
          RestrictScalars.linearEquiv_symm_apply]
        exact mul_assoc _ _ _) a z

/-- The balanced multiplication is the original multiplication under the carrier equivalence. -/
private theorem algebraBimoduleMul_tmul (x y : f.algebraBimodule) :
    (f.algebraBimoduleMul (tmul R A x y)).val = x.val * y.val := by
  rw [algebraBimoduleMul, ← DGBimoduleHom.coe_val, DGRightModuleHom.coe_mk,
    mulLinearMap_tmul, RestrictScalars.linearEquiv_symm_apply]

private def unitRightLinearMap : DGBimoduleCat.tensorUnit.{u} hA →ₗ[Aᵐᵒᵖ] T where
  toFun a := (E).symm (f a.down)
  map_add' a b := by
    have hab : (a + b).down = a.down + b.down := ULift.add_down
    apply RestrictScalars.ext
    simp only [RestrictScalars.linearEquiv_symm_apply, RestrictScalars.val_add]
    rw [hab, map_add]
  map_smul' a x := by
    refine MulOpposite.rec' (fun a ↦ ?_) a
    apply RestrictScalars.ext
    simp only [RingHom.id_apply, RestrictScalars.val_op_smul,
      RestrictScalars.linearEquiv_symm_apply,
      DGBimoduleCat.tensorUnit_op_smul_down, map_mul, op_smul_eq_mul]

/-- The base map is the unit of the target algebra regarded as a bimodule monoid. -/
private def algebraBimoduleUnit : DGBimoduleCat.tensorUnit.{u} hA ⟶ f.algebraBimodule := by
  refine ⟨{ toLinearMap := unitRightLinearMap f, map_mem' := ?_, map_d' := ?_ }, ?_⟩
  · intro p a ha
    rw [DGBimoduleCat.mem_tensorUnit_grading_iff] at ha
    exact (IsDGRightModule.mem_restrictScalarsGrading_iff f).2 (by
      simpa only [unitRightLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
        LinearEquiv.apply_symm_apply] using Graded.map_mem f ha)
  · intro a
    apply (E).injective
    simp only [RestrictScalars.linearEquiv_apply, IsDGRightModule.val_restrictScalarsDifferential,
      unitRightLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
      RestrictScalars.linearEquiv_symm_apply, DGBimoduleCat.tensorUnit_differential_apply,
      f.map_d]
  · rw [mem_dgBimoduleHomSubmodule]
    intro a x
    apply (E).injective
    simp only [unitRightLinearMap, DGRightModuleHom.coe_mk, LinearMap.coe_mk, AddHom.coe_mk,
      DGBimoduleCat.tensorUnit_smul_down, map_mul,
      RestrictScalars.linearEquiv_apply, algebraBimodule_val_smul,
      RestrictScalars.linearEquiv_symm_apply]

/-- The unit morphism evaluates to the specified base DG algebra map. -/
private theorem algebraBimoduleUnit_apply (a : DGBimoduleCat.tensorUnit.{u} hA) :
    (f.algebraBimoduleUnit a).val = f a.down := by
  rw [algebraBimoduleUnit, ← DGBimoduleHom.coe_val, DGRightModuleHom.coe_mk,
    unitRightLinearMap, LinearMap.coe_mk, AddHom.coe_mk,
    RestrictScalars.linearEquiv_symm_apply]

open scoped MonObj

/-- A DG algebra under `A` is a monoid object in DG `(A,A)`-bimodules.
The monoidal category uses carriers in the universe of `A`. -/
@[no_expose]
instance algebraBimoduleMonObj : MonObj f.algebraBimodule where
  one := algebraBimoduleUnit f
  mul := algebraBimoduleMul f
  one_mul := by
    apply DGBimoduleCat.tensorObj_hom_ext
    intro a x
    apply RestrictScalars.ext
    rw [DGBimoduleCat.comp_apply, DGBimoduleCat.whiskerRight_tmul,
      algebraBimoduleMul_tmul, algebraBimoduleUnit_apply,
      DGBimoduleCat.leftUnitor_hom_tmul, algebraBimodule_val_smul]
  mul_one := by
    apply DGBimoduleCat.tensorObj_hom_ext
    intro x a
    apply RestrictScalars.ext
    rw [DGBimoduleCat.comp_apply, DGBimoduleCat.whiskerLeft_tmul,
      algebraBimoduleMul_tmul, algebraBimoduleUnit_apply,
      DGBimoduleCat.rightUnitor_hom_tmul, RestrictScalars.val_op_smul,
      MulOpposite.smul_eq_mul_unop, unop_op]
  mul_assoc := by
    apply DGBimoduleCat.tensorObj_hom_ext
    intro z w
    induction z using BalancedTensorProduct.induction_on with
    | ht x y =>
        apply RestrictScalars.ext
        rw [DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply, DGBimoduleCat.comp_apply,
          DGBimoduleCat.whiskerRight_tmul, algebraBimoduleMul_tmul,
          algebraBimoduleMul_tmul, DGBimoduleCat.associator_hom_tmul,
          DGBimoduleCat.whiskerLeft_tmul, algebraBimoduleMul_tmul,
          algebraBimoduleMul_tmul, mul_assoc]
    | ha z z' hz hz' => simp only [add_tmul, map_add, hz, hz']

/-- The monoid unit is the given DG algebra map on underlying elements. -/
@[simp]
theorem algebraBimodule_one_apply (a : DGBimoduleCat.tensorUnit.{u} hA) :
    (η[f.algebraBimodule] a).val = f a.down := by
  exact algebraBimoduleUnit_apply f a

/-- The monoid product is the target algebra product on underlying elements. -/
@[simp]
theorem algebraBimodule_mul_tmul (x y : f.algebraBimodule) :
    (μ[f.algebraBimodule] (tmul R A x y)).val = x.val * y.val := by
  exact algebraBimoduleMul_tmul f x y

end TauCeti.DGAlgHom
