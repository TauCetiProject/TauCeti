/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Adjacent.Tensor
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Normal
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.SelfTensor

/-!
# The cancellable blocks in an adjacent braid product

Evaluating the middle factor of the degree-two arrow insertion gives the volume
insertion in the self-tensor. This identifies the invertible component of the
lowest differential of the actual adjacent triple product.
-/

public section
noncomputable section
namespace TauCeti
open MulOpposite CategoryTheory
open scoped TensorProduct
variable (k : Type*) [CommRing k] {V : Type*} (G : SimpleGraph V) [Finite V]
local notation "Z" => AlgCat.carrier (zigzagAlgebra k G)
local notation "Γ" => zigzagAlgebraInternalGrading k G
local notation "U" => zigzagGradedBraidBimodule k G
local notation "T" => GradedModuleCat.bimoduleTensorObj Γ Γ Γ
local notation "e" => fun i : V ↦ zigzagAlgebraBasis k G (Sum.inl i)
local notation "L" => fun i : V ↦ (Ideal.span {e i} : Ideal Z)
local notation "R" => fun i : V ↦ (Ideal.span {op (e i)} : Ideal Zᵐᵒᵖ)
attribute [local instance] zigzagAlgebraIntegerGradedAlgebra

private theorem evaluation_factors (i : V) (l : L i) (r : R i) :
    (Bimodule.of (AlgHom.id k Z)).symm
      ((zigzagBraidEvaluationHom k G i).hom
        ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r))) =
      (l : Z) * unop (r : Zᵐᵒᵖ) := by
  have heval :=
    (LinearMap.congr_fun (hom_zigzagBraidEvaluationHom (k := k) (G := G) i)
      ((zigzagBraidBimoduleFactorsEquiv k G i).symm (l ⊗ₜ[k] r))).trans
        (zigzagBraidEvaluation_apply (k := k) (G := G) (i := i) _)
  simpa only [coe_zigzagBraidBimoduleFactorsEquiv_symm_tmul, Bimodule.smul_of,
    AlgHom.id_apply, mul_one, LinearEquiv.symm_apply_apply] using
      congrArg (Bimodule.of (AlgHom.id k Z)).symm heval

private theorem evaluation_adjacentArrow {i j : V} (h : G.Adj j i) :
    (Bimodule.of (AlgHom.id k Z)).symm
      ((zigzagBraidEvaluationHom k G j).hom
        ((zigzagBraidBimoduleFactorsEquiv k G j).symm
          ((zigzagAlgebraBasis k G (.inr (.inl (⟨(j, i), h⟩ : G.Dart))) •
            spanSingletonGenerator (e j)) ⊗ₜ[k]
              spanSingletonGenerator (op (e j))))) =
      zigzagAlgebraBasis k G (.inr (.inl (⟨(j, i), h⟩ : G.Dart))) := by
  rw [evaluation_factors]
  simp

/-- Evaluating the middle vertex of the adjacent top tensor inserts the volume in the
self-tensor, with no internal shift lost. -/
@[reassoc]
theorem zigzagBraidAdjacentTripleInsert_evaluateMiddle {i j : V} (h : G.Adj j i) :
    zigzagBraidAdjacentTripleInsert k G h ≫
      GradedModuleCat.bimoduleTensorMap Γ Γ Γ
        (zigzagBraidTensorEvaluationRight k G i j) (𝟙 (U i)) =
      zigzagBraidSelfTensorInr k G i := by
  classical
  apply GradedModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨t, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G i).symm.surjective u
  induction t using TensorProduct.inductionOn with
  | tmul l r =>
    simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply]
    have hinsert := zigzagBraidAdjacentTripleInsert_hom_factors k G h l r
    rw [hinsert]
    rw [GradedModuleCat.bimoduleTensorMap_tmul]
    simp only [GradedModuleCat.hom_id, LinearMap.id_apply,
      zigzagBraidTensorEvaluationRight_tmul, evaluation_adjacentArrow]
    rw [GradedModuleCat.bimoduleTensorTmul_balance]
    simp only [zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul]
    rw [zigzagBraidSelfTensorInr_hom_factors]
    simp [smul_smul, zigzagAlgebraBasis_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The degree-zero self-tensor insertion followed by right evaluation is the identity. -/
@[reassoc]
theorem zigzagBraidSelfTensorInl_evaluationRight (i : V) :
    zigzagBraidSelfTensorInl k G i ≫ zigzagBraidTensorEvaluationRight k G i i =
      𝟙 (U i) := by
  apply GradedModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨t, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G i).symm.surjective u
  induction t using TensorProduct.inductionOn with
  | tmul l r =>
    have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
    have heop : IsIdempotentElem (op (e i)) := by rw [IsIdempotentElem, ← op_mul, he.eq]
    have hr : e i * unop (r : Zᵐᵒᵖ) = unop (r : Zᵐᵒᵖ) := by
      simpa only [unop_mul, unop_op] using
        congrArg unop ((mem_span_singleton_iff_mul_eq_self heop).mp r.property)
    simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      GradedModuleCat.hom_id, LinearMap.id_apply]
    rw [zigzagBraidSelfTensorInl_hom_factors k G i l r,
      zigzagBraidTensorEvaluationRight_tmul, evaluation_factors]
    simp only [coe_spanSingletonGenerator, hr, op_unop,
      zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul,
      smul_spanSingletonGenerator heop]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The degree-zero self-tensor insertion followed by left evaluation is the identity. -/
@[reassoc]
theorem zigzagBraidSelfTensorInl_evaluationLeft (i : V) :
    zigzagBraidSelfTensorInl k G i ≫ zigzagBraidTensorEvaluationLeft k G i i =
      𝟙 (U i) := by
  apply GradedModuleCat.hom_ext
  apply LinearMap.ext
  intro u
  obtain ⟨t, rfl⟩ := (zigzagBraidBimoduleFactorsEquiv k G i).symm.surjective u
  induction t using TensorProduct.inductionOn with
  | tmul l r =>
    have he := isIdempotentElem_zigzagAlgebraBasis_inl k G i
    have hl : (l : Z) * e i = (l : Z) :=
      (mem_span_singleton_iff_mul_eq_self he).mp l.property
    simp only [GradedModuleCat.hom_comp, LinearMap.comp_apply,
      GradedModuleCat.hom_id, LinearMap.id_apply]
    rw [zigzagBraidSelfTensorInl_hom_factors k G i l r,
      zigzagBraidTensorEvaluationLeft_tmul, evaluation_factors]
    simp only [coe_spanSingletonGenerator, unop_op, hl,
      zigzagBraidBimoduleFactorsEquiv_symm_tmul_smul, one_smul,
      smul_spanSingletonGenerator he]
  | add x y hx hy => simp only [map_add, hx, hy]

end TauCeti
