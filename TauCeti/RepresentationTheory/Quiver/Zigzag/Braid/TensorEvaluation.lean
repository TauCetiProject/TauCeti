/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Unit

/-!
# Evaluation on tensor products of zigzag vertex bimodules

Evaluate either factor of a balanced vertex tensor using its multiplication map
and the appropriate unit identification. Both orders of evaluation agree as maps
to the regular bimodule. These maps and their pure-tensor computations are used
by the differential matrices of braid products.
-/

public section
noncomputable section
namespace TauCeti
open CategoryTheory MulOpposite
open scoped TensorProduct
universe u w
variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "T" => GradedModuleCat.bimoduleTensorObj Γ Γ Γ
local notation "E" => zigzagBraidEvaluationHom k G

/-- Evaluate the first vertex factor of a balanced tensor product. -/
def zigzagBraidTensorEvaluationLeft (i j : V) : T (U i) (U j) ⟶ U j :=
  GradedModuleCat.bimoduleTensorMap Γ Γ Γ (E i) (𝟙 (U j)) ≫
    (zigzagBimoduleLeftUnitor k G (U j)).hom

/-- Evaluate the second vertex factor of a balanced tensor product. -/
def zigzagBraidTensorEvaluationRight (i j : V) : T (U i) (U j) ⟶ U i :=
  GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i)) (E j) ≫
    (zigzagBimoduleRightUnitor k G (U i)).hom

/-- Left evaluation on a pure balanced tensor is the left action of its evaluated factor. -/
@[simp]
theorem zigzagBraidTensorEvaluationLeft_tmul (i j : V) (x : U i) (y : U j) :
    (zigzagBraidTensorEvaluationLeft k G i j).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U j) x y) =
      ((Bimodule.of (AlgHom.id k (zigzagAlgebra k G))).symm ((E i).hom x) ⊗ₜ[k]
        (1 : (zigzagAlgebra k G)ᵐᵒᵖ)) • y := by
  -- Compute the tensor-map and unitor components in the evaluation composite.
  change (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (E i) (𝟙 (U j)) ≫
    (zigzagBimoduleLeftUnitor k G (U j)).hom).hom _ = _
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorMap_tmul, GradedModuleCat.hom_id,
    LinearMap.id_apply, zigzagBimoduleLeftUnitor_hom_tmul]

/-- Right evaluation on a pure balanced tensor is the right action of its evaluated factor. -/
@[simp]
theorem zigzagBraidTensorEvaluationRight_tmul (i j : V) (x : U i) (y : U j) :
    (zigzagBraidTensorEvaluationRight k G i j).hom
      (GradedModuleCat.bimoduleTensorTmul Γ Γ Γ (U i) (U j) x y) =
      ((1 : zigzagAlgebra k G) ⊗ₜ[k]
        op ((Bimodule.of (AlgHom.id k (zigzagAlgebra k G))).symm ((E j).hom y))) • x := by
  -- Compute the tensor-map and unitor components in the evaluation composite.
  change (GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i)) (E j) ≫
    (zigzagBimoduleRightUnitor k G (U i)).hom).hom _ = _
  simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
    GradedModuleCat.bimoduleTensorMap_tmul, GradedModuleCat.hom_id,
    LinearMap.id_apply, zigzagBimoduleRightUnitor_hom_tmul]

/-- Left evaluation is the tensor of evaluation with the identity, followed by the unitor. -/
@[reassoc]
theorem zigzagBraidTensorEvaluationLeft_eq (i j : V) :
    zigzagBraidTensorEvaluationLeft k G i j =
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ (E i) (𝟙 (U j)) ≫
        (zigzagBimoduleLeftUnitor k G (U j)).hom := by
  apply GradedModuleCat.bimoduleTensor_hom_ext Γ Γ Γ
  intro x y
  simp only [zigzagBraidTensorEvaluationLeft_tmul, GradedModuleCat.hom_comp,
    LinearMap.comp_apply, GradedModuleCat.bimoduleTensorMap_tmul,
    GradedModuleCat.hom_id, LinearMap.id_apply, zigzagBimoduleLeftUnitor_hom_tmul]

/-- Right evaluation is the tensor of the identity with evaluation, followed by the unitor. -/
@[reassoc]
theorem zigzagBraidTensorEvaluationRight_eq (i j : V) :
    zigzagBraidTensorEvaluationRight k G i j =
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ (𝟙 (U i)) (E j) ≫
        (zigzagBimoduleRightUnitor k G (U i)).hom := by
  apply GradedModuleCat.bimoduleTensor_hom_ext Γ Γ Γ
  intro x y
  simp only [zigzagBraidTensorEvaluationRight_tmul, GradedModuleCat.hom_comp,
    LinearMap.comp_apply, GradedModuleCat.bimoduleTensorMap_tmul,
    GradedModuleCat.hom_id, LinearMap.id_apply, zigzagBimoduleRightUnitor_hom_tmul]

/-- Both orders of factor evaluation give the same map to the regular bimodule. -/
@[reassoc]
theorem zigzagBraidTensorEvaluation_comm (i j : V) :
    zigzagBraidTensorEvaluationLeft k G i j ≫ E j =
      zigzagBraidTensorEvaluationRight k G i j ≫ E i := by
  rw [zigzagBraidTensorEvaluationLeft, zigzagBraidTensorEvaluationRight,
    Category.assoc, Category.assoc,
    ← zigzagBimoduleLeftUnitor_naturality k G (U j) (E j),
    ← zigzagBimoduleRightUnitor_naturality k G (U i) (E i),
    zigzagBimoduleUnitHom_eq k G]
  simp only [← Category.assoc, ← GradedModuleCat.bimoduleTensorMap_comp,
    Category.id_comp, Category.comp_id]

end TauCeti
