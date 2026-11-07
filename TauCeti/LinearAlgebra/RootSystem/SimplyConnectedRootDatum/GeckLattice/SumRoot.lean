/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.ClassTwo

/-!
# The sum-root subgroup at a single bond of the Geck diagram

For simple roots joined by a single bond, the commutator of their positive root subgroups
is a one-parameter subgroup at the product parameter. This constructs the positive sum-root
subgroup inside the Geck carrier over every commutative ring. Its sign is fixed by the ordered
bracket of the two pinned simple root vectors, so reversing the nodes changes the normalization.
No reductivity or identification of the carrier with a pinned group is asserted here.

The construction specializes `kostantToralBracketRootSubgroupPoints`, the integral
central-bracket exponential in the toral carrier. Serre's relations verify its hypotheses
without a restriction on the nilpotency degree of the Geck matrices.

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

/-- The positive sum-root subgroup at a single bond, normalized by the ordered bracket of
its pinned simple roots. The parameter is in the multiplicative copy of the additive ring. -/
noncomputable def geckSumRootSubgroupPoints (A : Type v) [CommRing A] :
    Multiplicative A →* t.geckPoints ht A :=
  (MulEquiv.subgroupCongr (t.geckPoints_eq_kostantToralPointsSubgroup ht A).symm).toMonoidHom.comp
    (UniversalEnvelopingAlgebra.kostantToralBracketRootSubgroupPoints
      (i := Sum.inl i) (j := Sum.inl j)
      (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
      (t.geckCoordinateLattice ht).toAddSubgroup
      (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
      (t.isNilpotent_geckRepresentation_rootGenerator ht)
      (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
      (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
        (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_of_eq_neg_one hji)
      (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
        (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_swap_of_eq_neg_one hij) A)

/-- The sum-root matrix is the image of the integral exponential of the ordered bracket. -/
@[simp]
theorem coe_geckSumRootSubgroupPoints (A : Type v) [CommRing A] (a : Multiplicative A) :
    (t.geckSumRootSubgroupPoints ht i j hij hji A a :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) =
      Units.map
        (LinearMap.toMatrixAlgEquiv ((t.geckCoordinateBasisFin ht).baseChange A)).toMonoidHom
        (UniversalEnvelopingAlgebra.kostantBracketRootSubgroupParam
          (i := Sum.inl i) (j := Sum.inl j)
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
          (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
            (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_of_eq_neg_one hji)
          (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
            (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_swap_of_eq_neg_one hij)
          (t.isNilpotent_geckRepresentation_rootGenerator ht (.inl i)) (CommAlgCat.of ℤ A) a) := by
  simp only [geckSumRootSubgroupPoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.subgroupCongr_apply,
    UniversalEnvelopingAlgebra.coe_kostantToralBracketRootSubgroupPoints]

/-- The positive single-bond Chevalley commutator relation in the actual Geck carrier. -/
theorem commutatorElement_geckSimpleRaising_eq_sumRoot
    (A : Type v) [CommRing A] (a b : A) :
    ⁅t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd a),
        t.geckRootSubgroupPoints ht (.inl j) A (Multiplicative.ofAdd b)⁆ =
      t.geckSumRootSubgroupPoints ht i j hij hji A (Multiplicative.ofAdd (a * b)) := by
  have heq := UniversalEnvelopingAlgebra.commutatorElement_kostantToralRootSubgroupPoints_eq_bracket
    (i := Sum.inl i) (j := Sum.inl j)
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
      (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_of_eq_neg_one hji)
    (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
      (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_swap_of_eq_neg_one hij) A a b
  apply Subtype.ext
  simpa only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    coe_geckRootSubgroupPoints, coe_geckSumRootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralRootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralBracketRootSubgroupPoints] using
    congrArg Subtype.val heq

/-- The positive sum-root subgroup has torus weight equal to the sum of the two
numbered simple-root weights. -/
@[simp]
theorem geckWeightTorusPoints_conj_geckSumRootSubgroupPoints
    (A : Type v) [CommRing A] (s : Fin t.rank → Aˣ) (u : Multiplicative A) :
    t.geckWeightTorusPoints ht A s * t.geckSumRootSubgroupPoints ht i j hij hji A u *
        (t.geckWeightTorusPoints ht A s)⁻¹ =
      t.geckSumRootSubgroupPoints ht i j hij hji A
        (Multiplicative.ofAdd
          ((torusCharacter s (t.rootGeneratorWeight ht (.inl i) +
            t.rootGeneratorWeight ht (.inl j)) : A) * u.toAdd)) := by
  have heq :=
    UniversalEnvelopingAlgebra.kostantToralWeightTorusPoints_conj_bracketRootSubgroupPoints
    (i := Sum.inl i) (j := Sum.inl j)
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.isNilpotent_geckRepresentation_rootGenerator ht)
    (t.geckCoordinateBasisFin ht) (t.geckWeightFin ht)
    (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
      (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_of_eq_neg_one hji)
    (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
      (t.isSerreSystem_lieBasis ht).lie_E_lie_E_E_swap_of_eq_neg_one hij)
    (t.isCartanWeightVector_geckCoordinateBasisFin ht)
    (fun k ↦ t.lie_lieBasis_h_rootGenerator ht (.inl i) k)
    (fun k ↦ t.lie_lieBasis_h_rootGenerator ht (.inl j) k) A s u
  apply Subtype.ext
  simpa only [Subgroup.coe_mul, Subgroup.coe_inv, coe_geckWeightTorusPoints,
    coe_geckSumRootSubgroupPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralWeightTorusPoints,
    UniversalEnvelopingAlgebra.coe_kostantToralBracketRootSubgroupPoints,
    geckTorusMatrix] using congrArg Subtype.val heq

end

end TauCeti.DynkinType
