/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Commutator.ClassTwo

/-!
# The sum-root subgroup at a single bond of the Geck diagram

For simple roots joined by a single bond, the commutator of their positive root subgroups
is a one-parameter subgroup at the product parameter. This constructs the positive sum-root
subgroup inside the Geck carrier over every commutative ring. Its sign is fixed by the ordered
bracket of the two pinned simple root vectors, so reversing the nodes changes the normalization.
No reductivity or identification of the carrier with a pinned group is asserted here.

The construction uses the integral central-bracket exponential, and Serre's relations verify
its hypotheses without a restriction on the nilpotency degree of the Geck matrices.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups* (2017).
* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

open CategoryTheory WithConv
open scoped commutatorElement

namespace TauCeti.DynkinType

universe v

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)
  (i j : Fin t.rank) (hij : t.cartanMatrix i j = -1) (hji : t.cartanMatrix j i = -1)

include hji in
private theorem raising_bracket_central_left :
    ⁅(t.lieBasis ht).rootGenerator (.inl i),
      ⁅(t.lieBasis ht).rootGenerator (.inl i), (t.lieBasis ht).rootGenerator (.inl j)⁆⁆ = 0 := by
  simpa only [LieAlgebra.Basis.rootGenerator_inl, Matrix.transpose_apply, hji, neg_neg,
    Int.toNat_one, pow_one, LieAlgebra.ad_apply] using
    (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j

include hij in
private theorem raising_bracket_central_right :
    ⁅(t.lieBasis ht).rootGenerator (.inl j),
      ⁅(t.lieBasis ht).rootGenerator (.inl i), (t.lieBasis ht).rootGenerator (.inl j)⁆⁆ = 0 := by
  have hc := t.raising_bracket_central_left ht j i hij
  rw [← lie_skew ((t.lieBasis ht).rootGenerator (.inl i))
    ((t.lieBasis ht).rootGenerator (.inl j)), lie_neg, hc, neg_zero]

private theorem matrix_rootParam (A : Type v) [CommRing A] (k : Fin t.rank ⊕ Fin t.rank)
    (a : Multiplicative A) :
    Units.map (LinearMap.toMatrixAlgEquiv ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom
        (t.geckRootSubgroupParam ht k (CommAlgCat.of ℤ A) a) =
      (t.geckRootSubgroupPoints ht k A a :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) := by
  rw [coe_geckRootSubgroupPoints,
    UniversalEnvelopingAlgebra.kostantRootSubgroupParam_apply]
  simp only [geckRootSubgroupMatrix,
    UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_def, MonoidHom.comp_apply]

include hij hji

/-- At a single bond the positive-root commutator depends only on the product parameter. -/
private theorem commutator_mul_one
    (A : Type v) [CommRing A] (a b : A) :
    ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd b)⁆ =
      ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a * b)),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd 1)⁆ := by
  have h := UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupParam_eq_mul_one
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.raising_bracket_central_left ht i j hji) (t.raising_bracket_central_right ht i j hij)
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl j)) (CommAlgCat.of ℤ A) a b
  have hm := congrArg
    (Units.map
      (LinearMap.toMatrixAlgEquiv ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom) h
  apply Subtype.coe_injective
  simpa only [commutatorElement_def, map_mul, map_inv, t.matrix_rootParam ht A,
    Subgroup.coe_mul, Subgroup.coe_inv] using hm

private theorem commutator_add (A : Type v) [CommRing A] (a b : A) :
    ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd (a + b)),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd 1)⁆ =
      ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd 1)⁆ *
      ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd b),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd 1)⁆ := by
  have h := UniversalEnvelopingAlgebra.commutatorElement_kostantRootSubgroupParam_add_one
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.raising_bracket_central_left ht i j hji) (t.raising_bracket_central_right ht i j hij)
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i))
    (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl j)) (CommAlgCat.of ℤ A) a b
  have hm := congrArg
    (Units.map
      (LinearMap.toMatrixAlgEquiv ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom) h
  apply Subtype.coe_injective
  simpa only [commutatorElement_def, map_mul, map_inv, t.matrix_rootParam ht A,
    Subgroup.coe_mul, Subgroup.coe_inv] using hm

/-- The positive sum-root subgroup at a single bond, normalized by the ordered bracket of
its pinned simple roots. The parameter is in the multiplicative copy of the additive ring. -/
noncomputable def geckAdjacentRootSubgroupPoints (A : Type v) [CommRing A] :
    Multiplicative A →* t.geckPoints ht A where
  toFun a := ⁅t.geckRootSubgroupPoints ht (.inl i) A a,
    t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd 1)⁆
  map_one' := by simp
  map_mul' a b := t.commutator_add ht i j hij hji A a.toAdd b.toAdd

/-- The sum-root subgroup is the commutator with the second simple-root parameter fixed at one. -/
@[simp]
theorem geckAdjacentRootSubgroupPoints_apply (A : Type v) [CommRing A]
    (a : Multiplicative A) :
    t.geckAdjacentRootSubgroupPoints ht i j hij hji A a =
      ⁅t.geckRootSubgroupPoints ht (.inl i) A a,
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd 1)⁆ := (rfl)

/-- The positive single-bond Chevalley commutator relation in the actual Geck carrier. -/
theorem commutatorElement_geckSimpleRaising_eq_adjacentRoot
    (A : Type v) [CommRing A] (a b : A) :
    ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd b)⁆ =
      t.geckAdjacentRootSubgroupPoints ht i j hij hji A (Multiplicative.ofAdd (a * b)) := by
  rw [geckAdjacentRootSubgroupPoints_apply]
  exact t.commutator_mul_one ht i j hij hji A a b

end

end TauCeti.DynkinType
