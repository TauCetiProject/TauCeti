/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator
import Mathlib.Algebra.Lie.Matrix

/-!
# Adjacent-root relations in the doubled minuscule E₆ carrier

The numbered root subgroups on `V(ϖ₁) ⊕ V(ϖ₆)` satisfy the nested commutator identities
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` and their negative-root counterparts when
`i` and `j` are adjacent in the Bourbaki diagram. These are relations on the actual root
parametrizations over every commutative ring, including characteristic two and nonreduced rings.
They supply nonzero simple-root relations for comparing the carrier's numbered pinning.

The integral Serre relations are transported from block coordinates to the carrier's matrix
coordinates. Square-zero integral root matrices then allow the nested-unipotent identity to be
specialized without dividing by two in the value ring. No identification with an independently
pinned simply connected group is asserted.

## Main results

* `commutatorElement_commutatorElement_rootSubgroupPoints_inl`: the positive-root identity.
* `commutatorElement_commutatorElement_rootSubgroupPoints_inr`: the negative-root identity.

## References

The group-identity argument follows
`TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`.

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25–26.
-/

public section

namespace TauCeti.E6DoubledMinuscule

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "CM" => CartanMatrix.E 6
local notation "E" => fun i : Fin 6 ↦ rootIntMatrix (Sum.inl i)
local notation "F" => fun i : Fin 6 ↦ rootIntMatrix (Sum.inr i)

private theorem rootMatrix_isSerreSystem :
    IsSerreSystem ℤ CM
      (fun i ↦ Matrix.reindex matrixIndexEquiv matrixIndexEquiv (cartanGeneratorMatrix i))
      E F := by
  have h := isSerreSystem.map (Matrix.reindexLieEquiv matrixIndexEquiv).toLieHom
  -- The represented Serre system uses the transpose convention; E₆'s matrix is symmetric.
  simpa only [(CartanMatrix.E_isSymm 6).eq, Function.comp_def,
    LieEquiv.coe_toLieHom, Matrix.reindexLieEquiv_apply, ← rootIntMatrix_inl,
    ← rootIntMatrix_inr] using h

private theorem adjacent_ne {i j : Fin 6} (hij : CM i j = -1) : i ≠ j := by
  rintro rfl
  rw [CartanMatrix.E_diag] at hij
  norm_num at hij

private theorem raising_lie_lie_eq_zero {i j : Fin 6} (hij : CM i j = -1) :
    ⁅E i, ⁅E i, E j⁆⁆ = 0 := by
  simpa [hij] using rootMatrix_isSerreSystem.ad_pow_lie_E_E i j

private theorem lowering_lie_lie_eq_zero {i j : Fin 6} (hij : CM i j = -1) :
    ⁅F i, ⁅F i, F j⁆⁆ = 0 := by
  simpa [hij] using rootMatrix_isSerreSystem.ad_pow_lie_F_F i j

/-- At adjacent nodes, commuting a positive simple-root point with another positive point
and then the matching negative point recovers the first root with parameter `t * s * r`.
This identity holds over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl {i j : Fin 6}
    (hij : CM i j = -1) (A : Type*) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by rw [(CartanMatrix.E_isSymm 6).apply, hij]
  have hAC := rootMatrix_isSerreSystem.lie_E_F_of_ne i j (adjacent_ne hij)
  have hABC : ⁅⁅E i, E j⁆, F j⁆ = E i := by
    rw [rootMatrix_isSerreSystem.lie_lie_E_E_F_of_ne (adjacent_ne hij), hji,
      neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (E i) (E j) (F j)
    (rootIntMatrix_mul_self _) (rootIntMatrix_mul_self _) (rootIntMatrix_mul_self _)
    hAC hABC (raising_lie_lie_eq_zero hij) (raising_lie_lie_eq_zero hji) t s r _ _ _
    (coe_rootSubgroupPoints_eq_one_add_smul _ A _) (coe_rootSubgroupPoints_eq_one_add_smul _ A _)
    (coe_rootSubgroupPoints_eq_one_add_smul _ A _)

/-- At adjacent nodes, commuting two negative simple-root points and then the matching
positive point recovers the first negative root with parameter `t * s * r`.
This identity holds over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr {i j : Fin 6}
    (hij : CM i j = -1) (A : Type*) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by rw [(CartanMatrix.E_isSymm 6).apply, hij]
  have hAC : ⁅F i, E j⁆ = 0 := by
    rw [← lie_skew, rootMatrix_isSerreSystem.lie_E_F_of_ne j i (adjacent_ne hji), neg_zero]
  have hABC : ⁅⁅F i, F j⁆, E j⁆ = F i := by
    rw [rootMatrix_isSerreSystem.lie_lie_F_F_E_of_ne (adjacent_ne hij), hji,
      neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (F i) (F j) (E j)
    (rootIntMatrix_mul_self _) (rootIntMatrix_mul_self _) (rootIntMatrix_mul_self _)
    hAC hABC (lowering_lie_lie_eq_zero hij) (lowering_lie_lie_eq_zero hji) t s r _ _ _
    (coe_rootSubgroupPoints_eq_one_add_smul _ A _) (coe_rootSubgroupPoints_eq_one_add_smul _ A _)
    (coe_rootSubgroupPoints_eq_one_add_smul _ A _)

end TauCeti.E6DoubledMinuscule
