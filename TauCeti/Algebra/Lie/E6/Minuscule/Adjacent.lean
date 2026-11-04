/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.Minuscule.GroupScheme
public import TauCeti.LinearAlgebra.Matrix.Cartan.Basic
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Nested commutators in the E₆ minuscule carrier

At adjacent simple nodes, the numbered root points satisfy
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)`, and the analogous identity with
all root signs reversed. These identities hold over every commutative ring, including rings
with torsion. They recover a simple-root parameter from the commutator at the sum of two
adjacent roots, without choosing a parametrization of that nonsimple root subgroup.

The statements use the Bourbaki Cartan matrix. The integral representation uses its transpose
(the coroot index precedes the root index); symmetry of the E₆ Cartan matrix supplies the
translation. No identification with the pinned simply connected group scheme is asserted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.
* The proofs adapt the nested-commutator argument in
  `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, using the shared integral matrix
  identity `Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul`.
-/

public section

namespace TauCeti.E6Minuscule

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem raising_lie_lie_eq_zero {i j : Fin 6} (hij : CartanMatrix.E 6 i j = -1) :
    ⁅raisingMatrix i, ⁅raisingMatrix i, raisingMatrix j⁆⁆ = 0 := by
  simpa only [Matrix.transpose_apply, (CartanMatrix.E_isSymm 6).apply i j, hij, neg_neg,
    Int.toNat_one, pow_one, LieAlgebra.ad_apply] using isSerreSystem.ad_pow_lie_E_E i j

private theorem lowering_lie_lie_eq_zero {i j : Fin 6} (hij : CartanMatrix.E 6 i j = -1) :
    ⁅loweringMatrix i, ⁅loweringMatrix i, loweringMatrix j⁆⁆ = 0 := by
  simpa only [Matrix.transpose_apply, (CartanMatrix.E_isSymm 6).apply i j, hij, neg_neg,
    Int.toNat_one, pow_one, LieAlgebra.ad_apply] using isSerreSystem.ad_pow_lie_F_F i j

/-- At adjacent nodes, the commutator of positive root points, followed by a commutator
with the opposite of the second root, recovers the first positive root parameter. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl {i j : Fin 6}
    (hij : CartanMatrix.E 6 i j = -1) (A : Type*) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji := ((CartanMatrix.E_isSymm 6).apply i j).trans hij
  have hAC := isSerreSystem.lie_E_F_of_ne i j (CartanMatrix.E_ne_of_eq_neg_one hij)
  have hABC : ⁅⁅raisingMatrix i, raisingMatrix j⁆, loweringMatrix j⁆ = raisingMatrix i := by
    simpa only [Matrix.transpose_apply, hij, neg_one_zsmul, neg_neg] using
      isSerreSystem.lie_lie_E_E_F_of_ne (CartanMatrix.E_ne_of_eq_neg_one hij)
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, weightTable_raisingMatrix]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (raisingMatrix i)
    (raisingMatrix j) (loweringMatrix j)
    (by simpa only [pow_two] using raisingMatrix_pow_two i)
    (by simpa only [pow_two] using raisingMatrix_pow_two j)
    (by simpa only [pow_two] using loweringMatrix_pow_two j)
    hAC hABC (raising_lie_lie_eq_zero hij) (raising_lie_lie_eq_zero hji)
    t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, weightTable_raisingMatrix])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, weightTable_raisingMatrix])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, weightTable_loweringMatrix])

/-- At adjacent nodes, the commutator of negative root points, followed by a commutator
with the opposite of the second root, recovers the first negative root parameter. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr {i j : Fin 6}
    (hij : CartanMatrix.E 6 i j = -1) (A : Type*) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji := ((CartanMatrix.E_isSymm 6).apply i j).trans hij
  have hAC : ⁅loweringMatrix i, raisingMatrix j⁆ = 0 := by
    rw [← lie_skew, isSerreSystem.lie_E_F_of_ne j i (CartanMatrix.E_ne_of_eq_neg_one hij).symm,
      neg_zero]
  have hABC : ⁅⁅loweringMatrix i, loweringMatrix j⁆, raisingMatrix j⁆ = loweringMatrix i := by
    simpa only [Matrix.transpose_apply, hij, neg_one_zsmul, neg_neg] using
      isSerreSystem.lie_lie_F_F_E_of_ne (CartanMatrix.E_ne_of_eq_neg_one hij)
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, weightTable_loweringMatrix]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (loweringMatrix i)
    (loweringMatrix j) (raisingMatrix j)
    (by simpa only [pow_two] using loweringMatrix_pow_two i)
    (by simpa only [pow_two] using loweringMatrix_pow_two j)
    (by simpa only [pow_two] using raisingMatrix_pow_two j)
    hAC hABC (lowering_lie_lie_eq_zero hij) (lowering_lie_lie_eq_zero hji)
    t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, weightTable_loweringMatrix])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, weightTable_loweringMatrix])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, weightTable_raisingMatrix])

end TauCeti.E6Minuscule
