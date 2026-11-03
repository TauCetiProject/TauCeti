/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme
import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Adjacent-root nested commutators in the tripled D₄ carrier

The numbered root subgroups of the tripled representation satisfy
`⁅⁅xᵢ(t), xⱼ(s)⁆, x₋ⱼ(r)⁆ = xᵢ(t * s * r)` at adjacent nodes, and the corresponding identity
with all root signs reversed. These equations hold over every commutative coefficient ring,
including characteristic two. They supply nonzero Chevalley relations for the numbered root
parametrizations used to compare this explicit carrier with a pinned simply connected group.

The carrier is not identified here with the pinned simply connected group scheme of type `D₄`.
Transport of these equations to that group requires such an identification.

The integral Serre system and square-zero root matrices give the hypotheses of
`Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul`. In particular, vanishing of the
relevant triple products is established integrally, before passing to the coefficient ring;
there is no division by two in that ring.

## Main results

* `TauCeti.D4Tripled.commutatorElement_commutatorElement_rootSubgroupPoints_inl`: the
  positive-root identity at adjacent nodes.
* `TauCeti.D4Tripled.commutatorElement_commutatorElement_rootSubgroupPoints_inr`: the
  negative-root identity at adjacent nodes.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* The formal argument is adapted from the adjacent-root calculation in
  `TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`, using the integral tripled weight table
  instead of the E₇ minuscule table.
-/

public section

namespace TauCeti.D4Tripled

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

local notation "CM" => CartanMatrix.D 4

private theorem adjacent_ne {i j : Fin 4} (hij : CM i j = -1) : i ≠ j := by
  rintro rfl
  rw [CartanMatrix.D_diag] at hij
  norm_num at hij

private theorem raising_lie_lie_eq_zero {i j : Fin 4} (hij : CM i j = -1) :
    ⁅raisingMatrix i, ⁅raisingMatrix i, raisingMatrix j⁆⁆ = 0 := by
  simpa [hij] using isSerreSystem.ad_pow_lie_E_E i j

private theorem lowering_lie_lie_eq_zero {i j : Fin 4} (hij : CM i j = -1) :
    ⁅loweringMatrix i, ⁅loweringMatrix i, loweringMatrix j⁆⁆ = 0 := by
  simpa [hij] using isSerreSystem.ad_pow_lie_F_F i j

/-- At adjacent nodes, the commutator of two positive simple-root points, followed by the
commutator with the matching negative simple-root point, recovers the first positive root at the
product of the three parameters. This holds over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inl {i j : Fin 4}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inl i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by
    rw [(CartanMatrix.D_isSymm 4).apply, hij]
  have hAC := isSerreSystem.lie_E_F_of_ne i j (adjacent_ne hij)
  have hABC : ⁅⁅raisingMatrix i, raisingMatrix j⁆, loweringMatrix j⁆ = raisingMatrix i := by
    rw [isSerreSystem.lie_lie_E_E_F_of_ne (adjacent_ne hij), hji, neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (raisingMatrix i)
    (raisingMatrix j) (loweringMatrix j)
    (by simpa only [pow_two] using raisingMatrix_pow_two i)
    (by simpa only [pow_two] using raisingMatrix_pow_two j)
    (by simpa only [pow_two] using loweringMatrix_pow_two j)
    hAC hABC (raising_lie_lie_eq_zero hij) (raising_lie_lie_eq_zero hji) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd])

/-- At adjacent nodes, the commutator of two negative simple-root points, followed by the
commutator with the matching positive simple-root point, recovers the first negative root at the
product of the three parameters. This holds over every commutative ring. -/
theorem commutatorElement_commutatorElement_rootSubgroupPoints_inr {i j : Fin 4}
    (hij : CM i j = -1) (A : Type u) [CommRing A] (t s r : A) :
    ⁅⁅rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd t),
        rootSubgroupPoints (.inr j) A (Multiplicative.ofAdd s)⁆,
      rootSubgroupPoints (.inl j) A (Multiplicative.ofAdd r)⁆ =
        rootSubgroupPoints (.inr i) A (Multiplicative.ofAdd (t * s * r)) := by
  have hji : CM j i = -1 := by
    rw [(CartanMatrix.D_isSymm 4).apply, hij]
  have hAC : ⁅loweringMatrix i, raisingMatrix j⁆ = 0 := by
    rw [← lie_skew, isSerreSystem.lie_E_F_of_ne j i (adjacent_ne hji), neg_zero]
  have hABC : ⁅⁅loweringMatrix i, loweringMatrix j⁆, raisingMatrix j⁆ = loweringMatrix i := by
    rw [isSerreSystem.lie_lie_F_F_E_of_ne (adjacent_ne hij), hji, neg_one_zsmul, neg_neg]
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul (loweringMatrix i)
    (loweringMatrix j) (raisingMatrix j)
    (by simpa only [pow_two] using loweringMatrix_pow_two i)
    (by simpa only [pow_two] using loweringMatrix_pow_two j)
    (by simpa only [pow_two] using raisingMatrix_pow_two j)
    hAC hABC (lowering_lie_lie_eq_zero hij) (lowering_lie_lie_eq_zero hji) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd])

end TauCeti.D4Tripled
