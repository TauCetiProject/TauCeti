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

For a long simple root `α` and the adjacent short simple root `β`, write `E` and `F` for their
integral matrices in the full-weight spin lattice. The group commutator of the corresponding
root points is

`1 + (s * t) • ⁅E, F⁆ + (s * t²) • (F * E * F)`.

The last summand is the `α + 2β` correction. It must not be discarded in characteristic two:
although the iterated Lie bracket is `-2 • (F * E * F)`, the group formula has no factor two.
The positive and negative formulas below require only `-1 ≤ B j i`, giving
`⁅E, ⁅E, F⁆⁆ = 0`, so they also apply to single bonds, nonadjacent nodes and coincident nodes.
At the terminal double bond, take `i` to be the long node and `j` the short node. The Cartan
matrix has roots as rows; the Serre system uses its transpose.

All vanishing products are proved in the integral lattice before changing coefficients. The
formulas therefore hold over arbitrary commutative rings, including nonreduced rings. They
compute matrices of actual carrier points, but do not construct the two nonsimple root subgroup
schemes or identify the carrier with an independently pinned simply connected group.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate II.

The integral-lattice transport uses the existing Kostant root-operator construction
`TauCeti.UniversalEnvelopingAlgebra.kostantRootOperator`; the group calculation uses
`Units.val_commutatorElement_eq_one_add_lie_add`.
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

/-- **Positive double-bond commutator, long root first.** If `-1 ≤ B j i`, the commutator
matrix has parameters `st` and `st²`. This includes single bonds, nonadjacent nodes and
coincident nodes; in those cases the cubic matrix term vanishes. -/
theorem coe_commutatorElement_rootSubgroupPoints_inl_inl_of_neg_one_le_cartan
    {i j : Fin (n + 1)} (hji : -1 ≤ CartanMatrix.B (n + 1) j i)
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
    -- Raise the vanishing Serre power to one using monotonicity of its kernel.
    have hexp : (-CartanMatrix.B (n + 1) j i).toNat ≤ 1 := by omega
    simpa [TauCeti.typeBSimpleRootGeneratorFamily_inl] using
      Module.End.pow_map_zero_of_le hexp
        (TauCeti.ad_pow_lie_typeBSimpleRootGenerator_typeBSimpleRootGenerator (K := ℚ) i j)
  exact coe_commutatorElement_rootSubgroupPoints_of_lie_lie_eq_zero hserre A s t

/-- **Negative double-bond commutator, long root first.** Under `-1 ≤ B j i`, the integral
negative-root matrices give the same parameter degrees `st` and `st²` over every commutative
ring, including single bonds, nonadjacent nodes and coincident nodes. -/
theorem coe_commutatorElement_rootSubgroupPoints_inr_inr_of_neg_one_le_cartan
    {i j : Fin (n + 1)} (hji : -1 ≤ CartanMatrix.B (n + 1) j i)
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
    have hexp : (-CartanMatrix.B (n + 1) j i).toNat ≤ 1 := by omega
    simpa [TauCeti.typeBSimpleRootGeneratorFamily_inr] using
      Module.End.pow_map_zero_of_le hexp
        (TauCeti.ad_pow_lie_typeBSimpleNegativeRootGenerator_typeBSimpleNegativeRootGenerator
          (K := ℚ) i j)
  exact coe_commutatorElement_rootSubgroupPoints_of_lie_lie_eq_zero hserre A s t

end TauCeti.TypeBSpinCarrier
