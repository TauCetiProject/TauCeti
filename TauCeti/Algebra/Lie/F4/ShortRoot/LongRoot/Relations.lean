/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Nested commutators at the long simple roots of the short-root F₄ carrier

The two long simple roots, Bourbaki nodes one and two (indices zero and one), form an
`A₂` subsystem. Their positive and negative root points satisfy
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` and its negative-root counterpart.
These nonzero Chevalley relations fix the normalization of the root at `αᵢ + αⱼ`
against the numbered simple-root parameters.

The identities hold over every commutative ring, including rings with two-torsion.
The long-root matrices square to zero; the integral Serre relations therefore allow the
square-zero unipotent commutator theorem to apply before changing coefficients. No assertion
is made here for the short simple roots, whose matrices have nonzero divided squares.
The explicit carrier is not identified with an independently pinned simply connected group
scheme, and these relations transfer to that group only along such an identification.

## Main results

* `TauCeti.F4ShortRoot.commutatorElement_commutatorElement_rootSubgroupPoints_inl_of_lt_two`
* `TauCeti.F4ShortRoot.commutatorElement_commutatorElement_rootSubgroupPoints_inr_of_lt_two`

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.

The proof specializes the integral unipotent calculation of
`TauCeti.LinearAlgebra.Matrix.UnipotentCommutator`, following the carrier-level transport in
`TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`.
-/

public section

namespace TauCeti.F4ShortRoot

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

private theorem cartanMatrix_eq_neg_one_of_lt_two {i j : Fin 4}
    (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) (hij : i ≠ j) :
    CartanMatrix.F₄ j i = -1 := by
  have hnodes : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    omega
  rcases hnodes with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide

/-- At the distinct long simple nodes, the positive nested commutator recovers the first
positive root point with parameter `t * s * r`, over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl_of_lt_two {i j : Fin 4}
    (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) (hij : i ≠ j)
    (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hCM := cartanMatrix_eq_neg_one_of_lt_two hi hj hij
  have hCM' := cartanMatrix_eq_neg_one_of_lt_two hj hi hij.symm
  have hABC : ⁅⁅raisingMatrix i, raisingMatrix j⁆, loweringMatrix j⁆ = raisingMatrix i := by
    rw [isSerreSystem.lie_lie_E_E_F_of_ne hij, Matrix.transpose_apply, hCM',
      neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inl_of_lt_two i hi, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (raisingMatrix i)
    (raisingMatrix j) (loweringMatrix j) (raisingMatrix_mul_self_of_lt_two i hi)
    (raisingMatrix_mul_self_of_lt_two j hj) (loweringMatrix_mul_self_of_lt_two j hj)
    (isSerreSystem.lie_E_F_of_ne i j hij) hABC
    (by simpa [hCM] using isSerreSystem.ad_pow_lie_E_E i j)
    (by simpa [hCM'] using isSerreSystem.ad_pow_lie_E_E j i) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inl_of_lt_two i hi, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inl_of_lt_two j hj, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inr_of_lt_two j hj, toAdd_ofAdd])

/-- At the distinct long simple nodes, the negative nested commutator recovers the first
negative root point with parameter `t * s * r`, over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr_of_lt_two {i j : Fin 4}
    (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) (hij : i ≠ j)
    (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hCM := cartanMatrix_eq_neg_one_of_lt_two hi hj hij
  have hCM' := cartanMatrix_eq_neg_one_of_lt_two hj hi hij.symm
  have hAC : ⁅loweringMatrix i, raisingMatrix j⁆ = 0 := by
    rw [← lie_skew, isSerreSystem.lie_E_F_of_ne j i hij.symm, neg_zero]
  have hABC : ⁅⁅loweringMatrix i, loweringMatrix j⁆, raisingMatrix j⁆ = loweringMatrix i := by
    rw [isSerreSystem.lie_lie_F_F_E_of_ne hij, Matrix.transpose_apply, hCM',
      neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inr_of_lt_two i hi, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (loweringMatrix i)
    (loweringMatrix j) (raisingMatrix j) (loweringMatrix_mul_self_of_lt_two i hi)
    (loweringMatrix_mul_self_of_lt_two j hj) (raisingMatrix_mul_self_of_lt_two j hj)
    hAC hABC
    (by simpa [hCM] using isSerreSystem.ad_pow_lie_F_F i j)
    (by simpa [hCM'] using isSerreSystem.ad_pow_lie_F_F j i) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inr_of_lt_two i hi, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inr_of_lt_two j hj, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inl_of_lt_two j hj, toAdd_ofAdd])

end TauCeti.F4ShortRoot
