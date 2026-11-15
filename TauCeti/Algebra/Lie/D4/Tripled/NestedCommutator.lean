/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.GroupScheme
import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.NestedCommutator

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

universe u

local notation "CM" => CartanMatrix.D 4

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
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, raisingMatrix_def]
  exact weightTable.coe_commutatorElement_commutatorElement_raisingMatrix
    (by simpa only [weightTable_cartanMatrix] using hij)
    (by simpa only [weightTable_cartanMatrix] using hji) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, raisingMatrix_def])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, raisingMatrix_def])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, loweringMatrix_def])

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
  apply (points A).subtype_injective
  simp only [map_commutatorElement, Subgroup.subtype_apply]
  apply Units.ext
  rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, loweringMatrix_def]
  exact weightTable.coe_commutatorElement_commutatorElement_loweringMatrix
    (by simpa only [weightTable_cartanMatrix] using hij)
    (by simpa only [weightTable_cartanMatrix] using hji) t s r _ _ _
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, loweringMatrix_def])
    (by rw [coe_rootSubgroupPoints_inr, toAdd_ofAdd, loweringMatrix_def])
    (by rw [coe_rootSubgroupPoints_inl, toAdd_ofAdd, raisingMatrix_def])

end TauCeti.D4Tripled
