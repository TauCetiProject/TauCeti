/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.Adjacent.Tensor
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Braid.SelfTensor

/-!
# The cancellable blocks in an adjacent braid product

Evaluating the middle factor of the degree-two arrow insertion gives the volume
insertion in the self-tensor. This identifies the invertible component of the
lowest differential of the actual adjacent triple product.

## References

* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*,
  [arXiv:math/0002060](https://arxiv.org/abs/math/0002060), Sections 3 and 4.6, Proposition 7.
* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*,
  [arXiv:math/0006056](https://arxiv.org/abs/math/0006056), Theorem 2.5 for the type-A relation.
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

private theorem evaluation_adjacentArrow {i j : V} (h : G.Adj j i) :
    (Bimodule.of (AlgHom.id k Z)).symm
      ((zigzagBraidEvaluationHom k G j).hom
        ((zigzagBraidBimoduleFactorsEquiv k G j).symm
          ((zigzagAlgebraBasis k G (.inr (.inl (⟨(j, i), h⟩ : G.Dart))) •
            spanSingletonGenerator (e j)) ⊗ₜ[k]
              spanSingletonGenerator (op (e j))))) =
      zigzagAlgebraBasis k G (.inr (.inl (⟨(j, i), h⟩ : G.Dart))) := by
  rw [hom_zigzagBraidEvaluationHom, zigzagBraidEvaluation_factors]
  simp

/-- Evaluating the middle vertex of the adjacent top tensor inserts the volume in the
self-tensor, with no internal shift lost. -/
@[reassoc (attr := simp)]
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

end TauCeti
