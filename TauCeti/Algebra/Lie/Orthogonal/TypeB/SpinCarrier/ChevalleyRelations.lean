/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
import TauCeti.Algebra.Lie.Orthogonal.TypeB.SerreRelations
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations
import TauCeti.LinearAlgebra.RootSystem.FiniteType.Classical
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Simple-root Chevalley relations of the type-B spin carrier

The numbered positive and negative simple-root subgroups of the full-weight type-`B` spin carrier
satisfy the zero-commutator Chevalley relations. Root subgroups of the same sign commute when their
nodes are not adjacent in the Dynkin diagram, while root subgroups of opposite signs commute at
distinct nodes. These statements hold over every commutative coefficient ring, including rings of
positive characteristic.

Together with the torus conjugation equations, these relations provide part of the pinned root
subgroup data for comparing the spin carrier with a simply connected group scheme of type `B`.
At a single bond, the root points also satisfy the nested identities
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` and their negative-root counterparts. Both directed
Cartan entries must be `-1`, excluding the terminal double bond. The square-zero and Serre
calculations take place on the integral spin lattice before changing coefficients. Full nonzero
commutator formulas involving the remaining nonsimple root subgroups are not asserted here.

## Main results

* `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inl_inl`: positive root subgroups at
  nonadjacent nodes commute.
* `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inr_inr`: negative root subgroups at
  nonadjacent nodes commute.
* `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inl_inr` and
  `TauCeti.TypeBSpinCarrier.commute_rootSubgroupPoints_inr_inl`: opposite-sign root subgroups at
  distinct nodes commute.
* `TauCeti.TypeBSpinCarrier.commutatorElement_commutatorElement_rootSubgroupPoints_inl` and
  `TauCeti.TypeBSpinCarrier.commutatorElement_commutatorElement_rootSubgroupPoints_inr`:
  positive and negative root points at a single bond satisfy the A₂ nested commutator identities.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The formal argument follows
  `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, specialized to the type-`B` Serre
  generators and spin representation. The nested group identities use
  `Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

universe u

variable {n : ℕ}

local notation "CM" => CartanMatrix.B (n + 1)
local notation "rootGen" k => TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k

private theorem lie_positive_positive_eq_zero {i j : Fin (n + 1)}
    (hij : CM i j = 0) :
    ⁅rootGen (.inl i), rootGen (.inl j)⁆ = 0 := by
  have hji : CM j i = 0 :=
    (TauCeti.isFiniteType_cartanMatrix_B (n + 1)).apply_eq_zero_symm hij
  simpa [TauCeti.typeBSimpleRootGeneratorFamily_inl, hji] using
    TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator
      (K := ℚ) i j

private theorem lie_negative_negative_eq_zero {i j : Fin (n + 1)}
    (hij : CM i j = 0) :
    ⁅rootGen (.inr i), rootGen (.inr j)⁆ = 0 := by
  have hji : CM j i = 0 :=
    (TauCeti.isFiniteType_cartanMatrix_B (n + 1)).apply_eq_zero_symm hij
  simpa [TauCeti.typeBSimpleRootGeneratorFamily_inr, hji] using
    TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator
      (K := ℚ) i j

private theorem lie_positive_negative_eq_zero {i j : Fin (n + 1)} (hij : i ≠ j) :
    ⁅rootGen (.inl i), rootGen (.inr j)⁆ = 0 := by
  simpa only [TauCeti.typeBSimpleRootGeneratorFamily_inl,
    TauCeti.typeBSimpleRootGeneratorFamily_inr] using
      TauCeti.typeBSimpleRootGenerator_lie_negative_of_ne (K := ℚ) i j hij

private theorem commute_rootSubgroupPoints_of_lie_eq_zero
    {i j : Fin (n + 1) ⊕ Fin (n + 1)} (hij : ⁅rootGen i, rootGen j⁆ = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n i A s) (rootSubgroupPoints n j A t) := by
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, coe_rootSubgroupPoints] using
    (commute_kostantRootSubgroupMatrix
      (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
      (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n)
      (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) (latticeBasis n)
      hij (isNilpotent_rep_rootGenerator n i) (isNilpotent_rep_rootGenerator n j)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm s)
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm t)).eq

/-- Positive numbered simple-root subgroups at nonadjacent type-`B` nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inl {i j : Fin (n + 1)} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inl i) A s) (rootSubgroupPoints n (.inl j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_positive_positive_eq_zero hij) A s t

/-- Negative numbered simple-root subgroups at nonadjacent type-`B` nodes commute over every
commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inr {i j : Fin (n + 1)} (hij : CM i j = 0)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inr i) A s) (rootSubgroupPoints n (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_negative_negative_eq_zero hij) A s t

/-- Positive and negative numbered simple-root subgroups at distinct type-`B` nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inl_inr {i j : Fin (n + 1)} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inl i) A s) (rootSubgroupPoints n (.inr j) A t) :=
  commute_rootSubgroupPoints_of_lie_eq_zero (lie_positive_negative_eq_zero hij) A s t

/-- Negative and positive numbered simple-root subgroups at distinct type-`B` nodes commute over
every commutative ring. -/
theorem commute_rootSubgroupPoints_inr_inl {i j : Fin (n + 1)} (hij : i ≠ j)
    (A : Type u) [CommRing A] (s t : Multiplicative A) :
    Commute (rootSubgroupPoints n (.inr i) A s) (rootSubgroupPoints n (.inl j) A t) :=
  (commute_rootSubgroupPoints_inl_inr hij.symm A t s).symm

/-! ## Single-bond nested commutators -/

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable abbrev rootOperator (k : Fin (n + 1) ⊕ Fin (n + 1)) :=
  kostantRootOperator (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ))
    (TauCeti.typeBSimpleCorootGenerator (K := ℚ)) (rep n) (lattice n).toAddSubgroup
    (rep_kostantForm_mem_lattice n) k

private noncomputable abbrev rootEnd (k : Fin (n + 1) ⊕ Fin (n + 1)) :=
  rep n (_root_.UniversalEnvelopingAlgebra.ι ℚ (rootGen k))

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
  have hf (k : Fin (n + 1) ⊕ Fin (n + 1)) : f (rootOperator k) = rootIntMatrix n k := by
    rw [rootIntMatrix_eq_toMatrix]
    ext i j
    simp only [f, AlgHom.toLieHom_apply, AlgEquiv.coe_toAlgHom,
      LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  have hAC' := congrArg f (kostantRootOperator_lie_eq_zero
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ)) TauCeti.typeBSimpleCorootGenerator
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) hAC)
  have hABC' := congrArg f (kostantRootOperator_lie_lie_eq
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ)) TauCeti.typeBSimpleCorootGenerator
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) hABC)
  have hAAB' := congrArg f (kostantRootOperator_lie_lie_eq_zero
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ)) TauCeti.typeBSimpleCorootGenerator
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) hAAB)
  have hBBA' := congrArg f (kostantRootOperator_lie_lie_eq_zero
    (TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ)) TauCeti.typeBSimpleCorootGenerator
    (rep n) (lattice n).toAddSubgroup (rep_kostantForm_mem_lattice n) hBBA)
  simp only [LieHom.map_lie, map_zero, hf] at hAC' hABC' hAAB' hBBA'
  apply (points n A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul
    (rootIntMatrix n a) (rootIntMatrix n b) (rootIntMatrix n c)
    (rootIntMatrix_mul_self_eq_zero n a) (rootIntMatrix_mul_self_eq_zero n b)
    (rootIntMatrix_mul_self_eq_zero n c) hAC' hABC' hAAB' hBBA' t s r _ _ _
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
