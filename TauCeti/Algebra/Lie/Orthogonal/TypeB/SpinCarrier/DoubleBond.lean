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
# Double-bond commutators in the type-B spin carrier

This file computes the commutator of the numbered long and short simple-root points in the
full-weight spin carrier. Its matrix is `1 + st [X,Y] + st² YXY`, with `X` the long-root matrix
and `Y` the short-root matrix. The cubic matrix term is retained: discarding it would give the
single-bond formula, which is not the type-B double-bond relation.

The positive and negative formulas hold over every commutative value ring. The Serre relation
and cancellation of two are used on the integral lattice, before specialization, so no bad
prime is inverted in the value ring. These are matrix formulas for the existing root points;
no parametrization of nonsimple root subgroups is asserted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* The integral-lattice transport uses the existing Kostant root-operator construction
  `TauCeti.UniversalEnvelopingAlgebra.kostantRootOperator`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

universe u

variable {n : ℕ}

local notation "rootGen" k => TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) k

/-- If the numbered rational generators satisfy a double-bracket Serre relation, their root
subgroup commutator has matrix `1 + st [X,Y] + st² YXY` over every commutative ring. -/
theorem coe_commutatorElement_rootSubgroupPoints_of_lie_lie_eq_zero
    {i j : Fin (n + 1) ⊕ Fin (n + 1)}
    (hij : ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) i,
      ⁅TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) i,
        TauCeti.typeBSimpleRootGeneratorFamily (K := ℚ) j⁆⁆ = 0)
    (A : Type u) [CommRing A] (s t : A) :
    (((⁅rootSubgroupPoints n i A (Multiplicative.ofAdd s),
        rootSubgroupPoints n j A (Multiplicative.ofAdd t)⁆ : points n A) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + (s * t) • (⁅rootIntMatrix n i, rootIntMatrix n j⁆).map (Int.cast : ℤ → A) +
        (s * t ^ 2) • (rootIntMatrix n j * rootIntMatrix n i * rootIntMatrix n j).map
          (Int.cast : ℤ → A) := by
  have h := Matrix.coe_commutatorElement_eq_one_add_smul_lie_add_smul_mul_mul
    (rootIntMatrix n i) (rootIntMatrix n j) (rootIntMatrix_mul_self_eq_zero n i)
    (rootIntMatrix_mul_self_eq_zero n j) (rootIntMatrix_lie_lie_eq_zero hij) s t
    (rootSubgroupPoints n i A (Multiplicative.ofAdd s))
    (rootSubgroupPoints n j A (Multiplicative.ofAdd t))
    (by rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd])
    (by rw [coe_rootSubgroupPoints_eq_one_add_smul, toAdd_ofAdd])
  -- The subgroup inclusion preserves the group commutator; the outer coercion reads its matrix.
  rw [← (points n A).subtype_apply] at h ⊢
  rw [map_commutatorElement]
  exact h

/-- **Positive double-bond commutator, long root first.** If the Cartan entry with short-root
row `j` and long-root column `i` is `-1`, its commutator matrix has parameters `st` and `st²`.
The statement also applies to a single bond; there the cubic matrix term vanishes. -/
theorem coe_commutatorElement_rootSubgroupPoints_inl_inl_of_cartan_eq_neg_one
    {i j : Fin (n + 1)} (hji : CartanMatrix.B (n + 1) j i = -1)
    (A : Type u) [CommRing A] (s t : A) :
    (((⁅rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd s),
        rootSubgroupPoints n (.inl j) A (Multiplicative.ofAdd t)⁆ : points n A) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + (s * t) • (⁅rootIntMatrix n (.inl i), rootIntMatrix n (.inl j)⁆).map
        (Int.cast : ℤ → A) +
        (s * t ^ 2) • (rootIntMatrix n (.inl j) * rootIntMatrix n (.inl i) *
          rootIntMatrix n (.inl j)).map (Int.cast : ℤ → A) := by
  have hserre : ⁅rootGen (.inl i), ⁅rootGen (.inl i), rootGen (.inl j)⁆⁆ = 0 := by
    -- The represented Serre system uses the transpose of the root-row Cartan matrix.
    simpa [TauCeti.typeBSimpleRootGeneratorFamily_inl, hji] using
      TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator (K := ℚ) i j
  exact coe_commutatorElement_rootSubgroupPoints_of_lie_lie_eq_zero hserre A s t

/-- **Negative double-bond commutator, long root first.** The integral negative-root matrices
give the same parameter degrees `st` and `st²`, over every commutative ring. -/
theorem coe_commutatorElement_rootSubgroupPoints_inr_inr_of_cartan_eq_neg_one
    {i j : Fin (n + 1)} (hji : CartanMatrix.B (n + 1) j i = -1)
    (A : Type u) [CommRing A] (s t : A) :
    (((⁅rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd s),
        rootSubgroupPoints n (.inr j) A (Multiplicative.ofAdd t)⁆ : points n A) :
        Matrix.GeneralLinearGroup (Fin (dimension n)) A) :
        Matrix (Fin (dimension n)) (Fin (dimension n)) A) =
      1 + (s * t) • (⁅rootIntMatrix n (.inr i), rootIntMatrix n (.inr j)⁆).map
        (Int.cast : ℤ → A) +
        (s * t ^ 2) • (rootIntMatrix n (.inr j) * rootIntMatrix n (.inr i) *
          rootIntMatrix n (.inr j)).map (Int.cast : ℤ → A) := by
  have hserre : ⁅rootGen (.inr i), ⁅rootGen (.inr i), rootGen (.inr j)⁆⁆ = 0 := by
    simpa [TauCeti.typeBSimpleRootGeneratorFamily_inr, hji] using
      TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator
        (K := ℚ) i j
  exact coe_commutatorElement_rootSubgroupPoints_of_lie_lie_eq_zero hserre A s t

end TauCeti.TypeBSpinCarrier
