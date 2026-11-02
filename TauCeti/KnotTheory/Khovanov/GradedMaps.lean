/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.GradedObject.Braiding
public import TauCeti.KnotTheory.Khovanov.QuantumGrading
public import TauCeti.Algebra.Module.GradedModule.TensorProduct.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Submodule
import TauCeti.CategoryTheory.GradedObject.MonObj

/-!
# Quantum-graded Frobenius maps

The merge, split, birth and death maps of the Khovanov Frobenius algebra are morphisms of
native graded objects into shifted targets. Their tensor source or target is Mathlib's
`GradedObject.Monoidal.tensorObj`, and its symmetry is the unsigned native braiding.
The maps are characterized on homogeneous elements and on the labels `1` and `X`.

Here the native categorical shift `[n]` has component `X[p+n]`. Thus the quantum shift
`⟨k⟩`, whose component is `X[p-k]`, is the categorical shift `[-k]`: merge and split
land in `[−1] = ⟨1⟩`, while birth and death land in `[1] = ⟨−1⟩`.
The evaluation of the native tensor in the ungraded tensor identifies these maps with the
multiplication, comultiplication, algebra map and counit already defined on `R[ε]`.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §2.
-/

public section

open CategoryTheory DualNumber TrivSqZeroExt
open GradedObject.Monoidal
open scoped TensorProduct MonoidalCategory

namespace TauCeti.Khovanov

universe u

variable (R : Type u) [CommRing R]

/-- The native total-degree tensor square of the quantum-graded circle object. -/
noncomputable abbrev quantumTensorObject : GradedObject ℤ (ModuleCat.{u} R) :=
  tensorObj (quantumGradedObject R) (quantumGradedObject R)

/-- The native graded tensor unit, concentrated in quantum degree zero. -/
noncomputable abbrev quantumUnitObject : GradedObject ℤ (ModuleCat.{u} R) := tensorUnit

/-- The circle label `1`, in quantum degree `1`. -/
def quantumOne : quantumGradedObject R 1 := ⟨1, one_mem_quantumGrading_piece_one⟩

/-- The circle label `X`, in quantum degree `−1`. -/
def quantumX : quantumGradedObject R (-1) := ⟨ε, eps_mem_quantumGrading_piece_neg_one⟩

@[simp] theorem coe_quantumOne : (quantumOne R : R[ε]) = 1 := (rfl)

@[simp] theorem coe_quantumX : (quantumX R : R[ε]) = ε := (rfl)

/-- A homogeneous pure tensor included in its native total-degree component. -/
noncomputable def quantumTensor {p q n : ℤ} (h : p + q = n)
    (x : quantumGradedObject R p) (y : quantumGradedObject R q) : quantumTensorObject R n :=
  ιTensorObj (quantumGradedObject R) (quantumGradedObject R) p q n h (x ⊗ₜ[R] y)

-- Run these rules before dependent component normalization changes their carrier presentation.
/-- The homogeneous tensor vanishes when its left input is zero. -/
@[simp↓]
theorem quantumTensor_zero_left {p q n : ℤ} (h : p + q = n)
    (y : quantumGradedObject R q) : quantumTensor R h 0 y = 0 := by
  simp only [quantumTensor, TensorProduct.zero_tmul, map_zero]

/-- The homogeneous tensor vanishes when its right input is zero. -/
@[simp↓]
theorem quantumTensor_zero_right {p q n : ℤ} (h : p + q = n)
    (x : quantumGradedObject R p) : quantumTensor R h x 0 = 0 := by
  simp only [quantumTensor, TensorProduct.tmul_zero, map_zero]

/-- Homogeneous tensors are additive in the left input. -/
@[simp↓]
theorem quantumTensor_add_left {p q n : ℤ} (h : p + q = n)
    (x x' : quantumGradedObject R p) (y : quantumGradedObject R q) :
    quantumTensor R h (x + x') y = quantumTensor R h x y + quantumTensor R h x' y := by
  simp only [quantumTensor, TensorProduct.add_tmul, map_add]

/-- Homogeneous tensors are additive in the right input. -/
@[simp↓]
theorem quantumTensor_add_right {p q n : ℤ} (h : p + q = n)
    (x : quantumGradedObject R p) (y y' : quantumGradedObject R q) :
    quantumTensor R h x (y + y') = quantumTensor R h x y + quantumTensor R h x y' := by
  simp only [quantumTensor, TensorProduct.tmul_add, map_add]

/-- Homogeneous tensors respect scalar multiplication in the left input. -/
@[simp↓]
theorem quantumTensor_smul_left {p q n : ℤ} (h : p + q = n) (r : R)
    (x : quantumGradedObject R p) (y : quantumGradedObject R q) :
    quantumTensor R h (r • x) y = r • quantumTensor R h x y := by
  simp only [quantumTensor, ← TensorProduct.smul_tmul', map_smul]

/-- Homogeneous tensors respect scalar multiplication in the right input. -/
@[simp↓]
theorem quantumTensor_smul_right {p q n : ℤ} (h : p + q = n) (r : R)
    (x : quantumGradedObject R p) (y : quantumGradedObject R q) :
    quantumTensor R h x (r • y) = r • quantumTensor R h x y := by
  simp only [quantumTensor, TensorProduct.tmul_smul, map_smul]

/-- Maps from a native quantum tensor component are determined by homogeneous pure tensors. -/
theorem quantumTensor_hom_ext {n : ℤ} {M : ModuleCat.{u} R}
    (f g : quantumTensorObject R n ⟶ M)
    (h : ∀ (p q : ℤ) (hpq : p + q = n)
      (x : quantumGradedObject R p) (y : quantumGradedObject R q),
      f (quantumTensor R hpq x y) = g (quantumTensor R hpq x y)) : f = g := by
  apply tensorObj_ext
  intro p q hpq
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h p q hpq x y

/-- Forget the homogeneous decomposition of a native tensor component. -/
noncomputable def quantumTensorEval (n : ℤ) :
    quantumTensorObject R n ⟶ ModuleCat.of R (R[ε] ⊗[R] R[ε]) :=
  tensorObjDesc fun p q _ ↦ ModuleCat.ofHom
    (TensorProduct.map (R := R) ((quantumGrading R).piece p).subtype
      ((quantumGrading R).piece q).subtype)

/-- Evaluating a native homogeneous pure tensor forgets the two membership proofs. -/
-- These computation rules run before simplification: normalizing dependent graded components
-- first changes the categorical carrier presentation and prevents ordinary application matching.
@[simp↓]
theorem quantumTensorEval_quantumTensor {p q n : ℤ} (h : p + q = n)
    (x : quantumGradedObject R p) (y : quantumGradedObject R q) :
    quantumTensorEval R n (quantumTensor R h x y) = (x : R[ε]) ⊗ₜ[R] (y : R[ε]) := by
  unfold quantumTensorEval quantumTensor
  rw [← ModuleCat.comp_apply, ι_tensorObjDesc]
  rfl

/-- Evaluation of a native quantum tensor is the internal tensor comparison followed by the
inclusion of its homogeneous piece. -/
theorem quantumTensorEval_eq_tensorProductGradedObjectIso (n : ℤ) :
    quantumTensorEval R n =
      ((quantumGrading R).tensorProductGradedObjectIso (quantumGrading R)).hom n ≫
        ModuleCat.ofHom
          (((quantumGrading R).tensorProduct (quantumGrading R)).piece n).subtype := by
  apply quantumTensor_hom_ext
  intro p q h x y
  rw [quantumTensorEval_quantumTensor]
  exact ((quantumGrading R).tensorProductGradedObjectIso_hom_tmul
    (quantumGrading R) h x y).symm

/-- The underlying tensor remembers every element of a native quantum tensor component. -/
theorem quantumTensorEval_injective (n : ℤ) : Function.Injective (quantumTensorEval R n) := by
  rw [quantumTensorEval_eq_tensorProductGradedObjectIso]
  exact Subtype.val_injective.comp
    (((GradedObject.eval n).mapIso
      ((quantumGrading R).tensorProductGradedObjectIso (quantumGrading R))).toLinearEquiv.injective)

/-- The image of a native quantum tensor component is exactly the corresponding homogeneous
piece of the underlying tensor product. -/
theorem range_quantumTensorEval (n : ℤ) :
    LinearMap.range (quantumTensorEval R n).hom =
      ((quantumGrading R).tensorProduct (quantumGrading R)).piece n := by
  have he := ((GradedObject.eval n).mapIso ((quantumGrading R).tensorProductGradedObjectIso
    (quantumGrading R))).toLinearEquiv.range
  simp only [Iso.toLinearMap_toLinearEquiv, Functor.mapIso_hom, GradedObject.eval_map] at he
  rw [quantumTensorEval_eq_tensorProductGradedObjectIso]
  rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.range_comp_of_range_eq_top _ he, Submodule.range_subtype]

/-- The native symmetry interchanges labels without a quantum Koszul sign. -/
@[simp]
theorem braiding_quantumTensor {p q n : ℤ} (h : p + q = n)
    (x : quantumGradedObject R p) (y : quantumGradedObject R q) :
    (braiding (quantumGradedObject R) (quantumGradedObject R)).hom n (quantumTensor R h x y) =
      quantumTensor R (add_comm q p |>.trans h) y x := by
  -- Use the partially defined native braiding, without a global graded monoidal instance.
  unfold GradedObject.Monoidal.braiding quantumTensor
  rw [← ModuleCat.comp_apply, ι_tensorObjDesc]
  exact congrArg (fun z ↦ (ιTensorObj (quantumGradedObject R)
    (quantumGradedObject R) q p n (add_comm q p |>.trans h)) z)
    (ModuleCat.MonoidalCategory.braiding_hom_apply x y)

private noncomputable def quantumMulSummand (p q n : ℤ) (h : p + q = n) :
    quantumGradedObject R p ⊗ quantumGradedObject R q ⟶ quantumGradedObject R (n + -1) :=
  ModuleCat.ofHom <| Submodule.inclusion (Submodule.mul_le.mpr (by
    intro x hx y hy
    simpa only [← h, sub_eq_add_neg] using mul_mem_quantumGrading_piece hx hy)) ∘ₗ
      Submodule.mulMap' ((quantumGrading R).piece p) ((quantumGrading R).piece q)

/-- Merge has degree `−1`, expressed as a degree-zero map to the categorical shift `[−1]`. -/
noncomputable def quantumMul : quantumTensorObject R ⟶
    (shiftFunctor (GradedObjectWithShift (1 : ℤ) (ModuleCat R)) (-1)).obj
      (quantumGradedObject R) :=
  fun n ↦ tensorObjDesc fun p q h ↦ quantumMulSummand R p q n h

/-- On homogeneous labels the graded merge is the underlying dual-number product. -/
@[simp↓]
theorem coe_quantumMul_quantumTensor {p q n : ℤ} (h : p + q = n)
    (x : quantumGradedObject R p) (y : quantumGradedObject R q) :
    (quantumMul R n (quantumTensor R h x y) :
      (quantumGrading R).piece (n + -1)).val = (x : R[ε]) * (y : R[ε]) := by
  unfold quantumMul quantumTensor
  rw [← ModuleCat.comp_apply, ι_tensorObjDesc]
  rfl

/-- Forgetting the graded merge gives the existing multiplication map. -/
theorem quantumMul_comp_subtype (n : ℤ) :
    quantumMul R n ≫ ModuleCat.ofHom ((quantumGrading R).piece (n + -1)).subtype =
      quantumTensorEval R n ≫ ModuleCat.ofHom (LinearMap.mul' R R[ε]) := by
  apply tensorObj_ext
  intro p q h
  simp only [quantumMul, quantumTensorEval, ι_tensorObjDesc_assoc]
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  rfl

/-- Split has degree `−1`, with its values constructed in the native graded tensor. -/
noncomputable def quantumComul : quantumGradedObject R ⟶
    (shiftFunctor (GradedObjectWithShift (1 : ℤ) (ModuleCat R)) (-1)).obj
      (quantumTensorObject R) := fun p ↦ by
  by_cases hp : p = 1
  · subst p
    exact ModuleCat.ofHom <| ((fstHom R R R).toLinearMap.domRestrict _).smulRight
      (quantumTensor R (by norm_num) (quantumOne R) (quantumX R) +
        quantumTensor R (by norm_num) (quantumX R) (quantumOne R))
  · by_cases hm : p = -1
    · subst p
      exact ModuleCat.ofHom <| ((sndHom R R).domRestrict _).smulRight
        (quantumTensor R (by norm_num) (quantumX R) (quantumX R))
    · exact 0

/-- The split on the degree-one piece, inside the native tensor. -/
theorem quantumComul_apply_one (x : quantumGradedObject R 1) :
    quantumComul R 1 x = (x : R[ε]).fst •
      (quantumTensor R (by norm_num) (quantumOne R) (quantumX R) +
        quantumTensor R (by norm_num) (quantumX R) (quantumOne R)) := (rfl)

/-- The split on the degree-minus-one piece, inside the native tensor. -/
theorem quantumComul_apply_neg_one (x : quantumGradedObject R (-1)) :
    quantumComul R (-1) x = (x : R[ε]).snd •
      quantumTensor R (by norm_num) (quantumX R) (quantumX R) := (rfl)

/-- The split vanishes outside the two degrees occupied by the circle object. -/
@[simp]
theorem quantumComul_eq_zero {p : ℤ} (hp : p ≠ 1) (hm : p ≠ -1) :
    quantumComul R p = 0 := by
  simp [quantumComul, hp, hm]

/-- The split of `1` in the actual native tensor component of degree zero. -/
@[simp↓]
theorem quantumComul_quantumOne : quantumComul R 1 (quantumOne R) =
    quantumTensor R (by norm_num) (quantumOne R) (quantumX R) +
      quantumTensor R (by norm_num) (quantumX R) (quantumOne R) := by
  rw [quantumComul_apply_one]
  simp

/-- The split of `X` in the actual native tensor component of degree `−2`. -/
@[simp↓]
theorem quantumComul_quantumX : quantumComul R (-1) (quantumX R) =
    quantumTensor R (by norm_num) (quantumX R) (quantumX R) := by
  rw [quantumComul_apply_neg_one]
  simp

/-- Forgetting the graded split recovers the chosen Khovanov comultiplication. -/
@[simp↓]
theorem quantumTensorEval_quantumComul (p : ℤ) (x : quantumGradedObject R p) :
    quantumTensorEval R (p + -1) (quantumComul R p x) =
      Coalgebra.comul (R := R) (x : R[ε]) := by
  by_cases hp : p = 1
  · subst p
    have hx := mem_quantumGrading_piece_one_iff.mp x.property
    rw [quantumComul_apply_one]
    simp only [map_smul, map_add]
    rw [quantumTensorEval_quantumTensor, quantumTensorEval_quantumTensor]
    simp [DualNumber.khovanov_comul_apply, hx]
  · by_cases hm : p = -1
    · subst p
      have hx := mem_quantumGrading_piece_neg_one_iff.mp x.property
      rw [quantumComul_apply_neg_one]
      simp only [map_smul]
      rw [quantumTensorEval_quantumTensor]
      simp [DualNumber.khovanov_comul_apply, hx]
    · have hx : x = 0 := by
        apply Subtype.ext
        exact (Submodule.mem_bot R).mp ((quantumGrading_piece_eq_bot (R := R) hp hm) ▸ x.property)
      simp [hx, quantumComul, hp, hm]

/-- The birth map has degree `1`, from the native tensor unit to the circle shifted by `[1]`. -/
noncomputable def quantumUnit : quantumUnitObject R ⟶
    (shiftFunctor (GradedObjectWithShift (1 : ℤ) (ModuleCat R)) (1 : ℤ)).obj
      (quantumGradedObject R) :=
  oneOfDegreeZero _ (ModuleCat.ofHom ((Algebra.linearMap R R[ε]).codRestrict _
    (by intro r; simp [TrivSqZeroExt.algebraMap_eq_inl])))

/-- Birth on an arbitrary element of the degree-zero tensor unit is the algebra map. -/
theorem coe_quantumUnit_zero (x : quantumUnitObject R 0) :
    (quantumUnit R 0 x : (quantumGrading R).piece 1).val =
      algebraMap R R[ε] ((tensorUnit₀ (C := ModuleCat R) (I := ℤ)).hom x) := by
  rw [quantumUnit, oneOfDegreeZero_zero]
  rfl

/-- Birth vanishes on every nonzero degree of the tensor unit. -/
@[simp]
theorem quantumUnit_eq_zero {p : ℤ} (hp : p ≠ 0) : quantumUnit R p = 0 :=
  (isInitialTensorUnitApply p hp).hom_ext _ _

/-- A scalar viewed in degree zero of the native tensor unit. -/
noncomputable def quantumScalar (r : R) : quantumUnitObject R 0 :=
  (tensorUnit₀ (C := ModuleCat R) (I := ℤ)).inv r

/-- Birth is the usual algebra map on scalars. -/
@[simp↓]
theorem coe_quantumUnit_quantumScalar (r : R) :
    (quantumUnit R 0 (quantumScalar R r) : (quantumGrading R).piece 1).val =
      algebraMap R R[ε] r := by
  rw [coe_quantumUnit_zero]
  unfold quantumScalar
  rw [ModuleCat.hom_inv_apply]

/-- Birth sends the scalar `1` to the homogeneous label `1`. -/
@[simp↓]
theorem quantumUnit_quantumScalar_one :
    quantumUnit R 0 (quantumScalar R 1) = quantumOne R := by
  apply Subtype.ext
  exact (coe_quantumUnit_quantumScalar R 1).trans (map_one _)

/-- Death has degree `1`, to the native tensor unit shifted by `[1]`. -/
noncomputable def quantumCounit : quantumGradedObject R ⟶
    (shiftFunctor (GradedObjectWithShift (1 : ℤ) (ModuleCat R)) (1 : ℤ)).obj
      (quantumUnitObject R) := fun p ↦ by
  by_cases hp : p = -1
  · subst p
    exact ModuleCat.ofHom ((Coalgebra.counit (R := R) (A := R[ε])).domRestrict _) ≫
      (tensorUnit₀ (C := ModuleCat R) (I := ℤ)).inv
  · exact 0

/-- On the degree `−1` piece, death is the chosen ungraded counit. -/
@[simp↓]
theorem quantumCounit_neg_one (x : quantumGradedObject R (-1)) :
    quantumCounit R (-1) x = quantumScalar R (Coalgebra.counit (R := R) (x : R[ε])) := by
  simp [quantumCounit, quantumScalar]

/-- Death evaluates `X` to the unit scalar. -/
theorem quantumCounit_quantumX :
    quantumCounit R (-1) (quantumX R) = quantumScalar R 1 :=
  quantumCounit_neg_one R (quantumX R)

/-- Death vanishes on all homogeneous pieces except degree `−1`. -/
@[simp]
theorem quantumCounit_eq_zero {p : ℤ} (hp : p ≠ -1) : quantumCounit R p = 0 := by
  simp [quantumCounit, hp]

end TauCeti.Khovanov
