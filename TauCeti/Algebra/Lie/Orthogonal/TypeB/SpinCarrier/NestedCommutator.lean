/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
import TauCeti.Algebra.Lie.Orthogonal.TypeB.SerreRelations
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Single-bond nested commutators in the type-B spin carrier

At a single bond of the type-B diagram, the positive and negative numbered root points satisfy
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` and its negative-root counterpart. Both directed
Cartan entries must be `-1`: these are the rank-two A₂ relations, not the relations at the
terminal double bond. The identities hold over arbitrary commutative rings, including
characteristic two, because the square-zero and Serre calculations are performed on the integral
spin lattice before changing coefficients.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The group-identity argument follows the E₇ minuscule nested commutator proofs in
  `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, using
  `Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra
open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {n : ℕ}

local notation "CM" => CartanMatrix.B (n + 1)
local notation "rootGen" k => TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k

private noncomputable abbrev rootOperator (k : Fin (n + 1) ⊕ Fin (n + 1)) :=
  kostantRootOperator (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) k

private noncomputable abbrev rootEnd (k : Fin (n + 1) ⊕ Fin (n + 1)) :=
  rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGen k))

private theorem rootOperator_lie_eq_zero
    {a b : Fin (n + 1) ⊕ Fin (n + 1)} (h : ⁅rootEnd a, rootEnd b⁆ = 0) :
    ⁅rootOperator a, rootOperator b⁆ = 0 := by
  ext v
  have hv := congrArg (fun f => f (v : ExteriorAlgebra ℚ (polarization n).W)) h
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    AddSubgroup.coe_sub, coe_kostantRootOperator_apply, LinearMap.zero_apply,
    ZeroMemClass.coe_zero] using hv

private theorem rootOperator_lie_lie_eq_zero
    {a b : Fin (n + 1) ⊕ Fin (n + 1)} (h : ⁅rootEnd a, ⁅rootEnd a, rootEnd b⁆⁆ = 0) :
    ⁅rootOperator a, ⁅rootOperator a, rootOperator b⁆⁆ = 0 := by
  ext v
  have hv := congrArg (fun f => f (v : ExteriorAlgebra ℚ (polarization n).W)) h
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    AddSubgroup.coe_sub, coe_kostantRootOperator_apply, LinearMap.zero_apply,
    ZeroMemClass.coe_zero, map_sub] using hv

private theorem rootOperator_lie_lie_eq
    {a b c : Fin (n + 1) ⊕ Fin (n + 1)}
    (h : ⁅⁅rootEnd a, rootEnd b⁆, rootEnd c⁆ = rootEnd a) :
    ⁅⁅rootOperator a, rootOperator b⁆, rootOperator c⁆ = rootOperator a := by
  ext v
  have hv := congrArg (fun f => f (v : ExteriorAlgebra ℚ (polarization n).W)) h
  simpa only [Ring.lie_def, LinearMap.sub_apply, mul_apply_eq_comp,
    AddSubgroup.coe_sub, coe_kostantRootOperator_apply, map_sub] using hv

private theorem adjacent_ne {i j : Fin (n + 1)} (hij : CM i j = -1) : i ≠ j := by
  rintro rfl
  rw [CartanMatrix.B_diag] at hij
  norm_num at hij

private theorem rootEnd_inl (i : Fin (n + 1)) :
    rootEnd (.inl i) = rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.typeBSimpleRootGenerator i)) := by
  simp only [rootEnd, TauCeti.typeBSimpleRootGeneratorFamily_inl]

private theorem rootEnd_inr (i : Fin (n + 1)) :
    rootEnd (.inr i) = rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ
      (TauCeti.typeBSimpleNegativeRootGenerator i)) := by
  simp only [rootEnd, TauCeti.typeBSimpleRootGeneratorFamily_inr]

-- The Serre convention has coroots as rows, hence the transpose of the public Cartan matrix.
private theorem represented_serreSystem :
    IsSerreSystem ℚ (Matrix.transpose CM)
      (((rep n).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) ∘
        TauCeti.typeBSimpleCorootGenerator)
      (((rep n).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) ∘
        TauCeti.typeBSimpleRootGenerator)
      (((rep n).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ)) ∘
        TauCeti.typeBSimpleNegativeRootGenerator) :=
  (TauCeti.isSerreSystem_typeBSimpleRootGenerator (K := ℚ) (n := n)).map
    ((rep n).toLieHom.comp (_root_.UniversalEnvelopingAlgebra.ι ℚ))

private theorem nested_matrix_identity
    {a b c : Fin (n + 1) ⊕ Fin (n + 1)}
    (hAC : ⁅rootEnd a, rootEnd c⁆ = 0)
    (hABC : ⁅⁅rootEnd a, rootEnd b⁆, rootEnd c⁆ = rootEnd a)
    (hAAB : ⁅rootEnd a, ⁅rootEnd a, rootEnd b⁆⁆ = 0)
    (hBBA : ⁅rootEnd b, ⁅rootEnd b, rootEnd a⁆⁆ = 0)
    (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints n a A (Multiplicative.ofAdd t),
        rootSubgroupPoints n b A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints n c A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints n a A (Multiplicative.ofAdd (t * s * r)) := by
  -- First restrict the rational relations to the invariant lattice, then pass to its basis
  -- matrices. The integral unipotent identity can now be specialized even in characteristic two.
  let f : Module.End ℤ (lattice n).toAddSubgroup →ₗ⁅ℤ⁆
      Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ :=
    (LinearMap.toMatrixAlgEquiv (latticeBasis n)).toAlgHom.toLieHom
  have hf (k : Fin (n + 1) ⊕ Fin (n + 1)) : f (rootOperator k) = rootIntMatrix n k :=
    (rootIntMatrix_eq_toMatrix n k).symm
  have hAC' := congrArg f (rootOperator_lie_eq_zero hAC)
  have hABC' := congrArg f (rootOperator_lie_lie_eq hABC)
  have hAAB' := congrArg f (rootOperator_lie_lie_eq_zero hAAB)
  have hBBA' := congrArg f (rootOperator_lie_lie_eq_zero hBBA)
  simp only [LieHom.map_lie, map_zero, hf] at hAC' hABC' hAAB' hBBA'
  apply (points n A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul
    (rootIntMatrix n a) (rootIntMatrix n b) (rootIntMatrix n c)
    (rootIntMatrix_mul_self n a) (rootIntMatrix_mul_self n b)
    (rootIntMatrix_mul_self n c) hAC' hABC' hAAB' hBBA' t s r _ _ _
    (by rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd])

/-- Positive type-B spin root points at a single bond satisfy the A₂ nested commutator identity
over every commutative ring. The two directed Cartan hypotheses exclude the double bond. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl
    {i j : Fin (n + 1)} (hij : CM i j = -1) (hji : CM j i = -1)
    (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints n (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have h := represented_serreSystem (n := n)
  apply nested_matrix_identity
  all_goals simp only [rootEnd_inl, rootEnd_inr]
  · exact h.lie_E_F_of_ne i j (adjacent_ne hij)
  · simpa only [Matrix.transpose_apply, hij, neg_one_zsmul, neg_neg,
      Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply] using
      h.lie_lie_E_E_F_of_ne (adjacent_ne hij)
  · simpa [Matrix.transpose_apply, hji] using h.ad_pow_lie_E_E i j
  · simpa [Matrix.transpose_apply, hij] using h.ad_pow_lie_E_E j i

/-- Negative type-B spin root points at a single bond satisfy the A₂ nested commutator identity
over every commutative ring. The two directed Cartan hypotheses exclude the double bond. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr
    {i j : Fin (n + 1)} (hij : CM i j = -1) (hji : CM j i = -1)
    (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints n (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have h := represented_serreSystem (n := n)
  apply nested_matrix_identity
  all_goals simp only [rootEnd_inl, rootEnd_inr]
  · rw [← lie_skew, neg_eq_zero]
    exact h.lie_E_F_of_ne j i (adjacent_ne hji)
  · simpa only [Matrix.transpose_apply, hij, neg_one_zsmul, neg_neg,
      Function.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply] using
      h.lie_lie_F_F_E_of_ne (adjacent_ne hij)
  · simpa [Matrix.transpose_apply, hji] using h.ad_pow_lie_F_F i j
  · simpa [Matrix.transpose_apply, hij] using h.ad_pow_lie_F_F j i

end TauCeti.TypeBSpinCarrier
