/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations

/-!
# Commuting simple-root subgroups of the Geck carrier

The pinned raising and lowering root subgroups of the Geck carrier satisfy the zero-pairing
Chevalley relation over every commutative ring. When two distinct Bourbaki nodes have zero Cartan
pairing, both raising subgroups commute, both lowering subgroups commute, and each raising subgroup
commutes with the other node's lowering subgroup. The last relation holds for any distinct nodes.

The statements concern the pinned Serre generators and their Kostant root-subgroup points.
These relations are used in the presentation of the pinned split group by its simple-root
subgroups; relations among nonorthogonal roots require the higher root-string formulas.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §5.2.
-/

public section

namespace TauCeti.DynkinType

universe v

noncomputable section

-- The concrete Geck Lie algebra is a matrix Lie algebra.
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance] TauCeti.moduleNNRat
attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- The pinned raising generators at nodes with zero Cartan pairing have zero Lie bracket. -/
@[simp]
theorem lie_geckSimpleRaising_eq_zero (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) :
    ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ = 0 := by
  have hji := (t.cartanMatrix_apply_eq_zero_iff_symm i j).mp hij
  have h := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  simpa [hji] using h

/-- The pinned lowering generators at nodes with zero Cartan pairing have zero Lie bracket. -/
@[simp]
theorem lie_geckSimpleLowering_eq_zero (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) :
    ⁅(t.lieBasis ht).f i, (t.lieBasis ht).f j⁆ = 0 := by
  have hji := (t.cartanMatrix_apply_eq_zero_iff_symm i j).mp hij
  have h := (t.isSerreSystem_lieBasis ht).ad_pow_lie_F_F i j
  simpa [hji] using h

/-- Raising at one node and lowering at a distinct node have zero Lie bracket. -/
@[simp]
theorem lie_geckSimpleRaising_lowering_eq_zero (i j : Fin t.rank) (hij : i ≠ j) :
    ⁅(t.lieBasis ht).e i, (t.lieBasis ht).f j⁆ = 0 :=
  (t.isSerreSystem_lieBasis ht).lie_E_F_of_ne i j hij

/-- Two numbered Geck root-subgroup points commute when their pinned Lie generators commute. -/
theorem commute_geckRootSubgroupPoints_of_lie_eq_zero
    (i j : Fin t.rank ⊕ Fin t.rank)
    (hij : ⁅(t.lieBasis ht).rootGenerator i, (t.lieBasis ht).rootGenerator j⁆ = 0)
    (A : Type v) [CommRing A] (u w : Multiplicative A) :
    Commute (t.geckRootSubgroupPoints ht i A u) (t.geckRootSubgroupPoints ht j A w) := by
  apply (commute_iff_eq ..).2
  apply Subtype.coe_injective
  simp only [Subgroup.coe_mul, t.coe_geckRootSubgroupPoints ht]
  exact (TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix
    (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
    (t.geckCoordinateLattice ht).toAddSubgroup
    (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht)
    (t.geckCoordinateBasisFin ht) hij
    (t.isNilpotent_geckRepresentation_rootGenerator ht i)
    (t.isNilpotent_geckRepresentation_rootGenerator ht j)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm w)).eq

/-- Raising subgroups at orthogonal simple roots commute over every commutative ring. -/
theorem commute_geckSimpleRaisingPoints (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) (A : Type v) [CommRing A]
    (u w : Multiplicative A) :
    Commute (t.geckRootSubgroupPoints ht (.inl i) A u)
      (t.geckRootSubgroupPoints ht (.inl j) A w) :=
  t.commute_geckRootSubgroupPoints_of_lie_eq_zero ht _ _
    (by simpa only [LieAlgebra.Basis.rootGenerator_inl] using
      t.lie_geckSimpleRaising_eq_zero ht i j hij) A u w

/-- Lowering subgroups at orthogonal simple roots commute over every commutative ring. -/
theorem commute_geckSimpleLoweringPoints (i j : Fin t.rank)
    (hij : t.cartanMatrix i j = 0) (A : Type v) [CommRing A]
    (u w : Multiplicative A) :
    Commute (t.geckRootSubgroupPoints ht (.inr i) A u)
      (t.geckRootSubgroupPoints ht (.inr j) A w) :=
  t.commute_geckRootSubgroupPoints_of_lie_eq_zero ht _ _
    (by simpa only [LieAlgebra.Basis.rootGenerator_inr] using
      t.lie_geckSimpleLowering_eq_zero ht i j hij) A u w

/-- The raising subgroup at one node commutes with the lowering subgroup at another node. -/
theorem commute_geckSimpleRaising_loweringPoints (i j : Fin t.rank) (hij : i ≠ j)
    (A : Type v) [CommRing A] (u w : Multiplicative A) :
    Commute (t.geckRootSubgroupPoints ht (.inl i) A u)
      (t.geckRootSubgroupPoints ht (.inr j) A w) :=
  t.commute_geckRootSubgroupPoints_of_lie_eq_zero ht _ _
    (by simpa only [LieAlgebra.Basis.rootGenerator_inl,
      LieAlgebra.Basis.rootGenerator_inr] using
      t.lie_geckSimpleRaising_lowering_eq_zero ht i j hij) A u w

/-- The lowering subgroup at one node commutes with the raising subgroup at another node. -/
theorem commute_geckSimpleLowering_raisingPoints (i j : Fin t.rank) (hij : i ≠ j)
    (A : Type v) [CommRing A] (u w : Multiplicative A) :
    Commute (t.geckRootSubgroupPoints ht (.inr i) A u)
      (t.geckRootSubgroupPoints ht (.inl j) A w) :=
  (t.commute_geckSimpleRaising_loweringPoints ht j i hij.symm A w u).symm

end

end TauCeti.DynkinType
