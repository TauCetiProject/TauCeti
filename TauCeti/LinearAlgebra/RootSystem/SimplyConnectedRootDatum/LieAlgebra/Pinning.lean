/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.ChevalleyRelations
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.GeckLattice.GroupScheme
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Basic
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.SerrePresentation

/-!
# Uniform Chevalley pinning for the Demazure construction

The pinned rational Lie algebra of a valid Dynkin type carries Bourbaki-numbered generators
(`TauCeti.DynkinType.lieBasis`): raising generators `e i` and lowering generators `f i` that
are nilpotent matrices, Cartan generators `h i`, satisfying the Cartan-matrix relations
(`TauCeti.DynkinType.lie_lieBasis_h_e`, `TauCeti.DynkinType.lie_lieBasis_h_f`) and exchanged
by the Chevalley involution (`TauCeti.DynkinType.chevalleyInvolution_lieBasis_e`).

This module establishes the Serre-relation bracket vanishings that underlie the Chevalley
commutator formulas, and applies them through the existing Kostant root-subgroup
machinery. The uniform exponentials `u ↦ exp(u • e_i)` over any commutative ring are the
existing Geck root-subgroup points `t.geckRootSubgroupPoints ht (.inl i) A
(Multiplicative.ofAdd u)`, taking values in the general linear group as the Geck
root-subgroup matrices. This module contributes only the bracket relations and their
direct transfer to the represented pinning.

## Main results

* `TauCeti.DynkinType.lie_lieBasis_e_e_of_cartan_eq_zero`: when the Cartan matrix entry
  vanishes (`A_{ji} = 0`), the Lie bracket `⁅e_i, e_j⁆ = 0` — the Serre relation.
* `TauCeti.DynkinType.geckRootSubgroupMatrix_comm_of_cartan_eq_zero`: the Chevalley
  commutator relation (commuting case) for the represented pinning.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.
-/

public section

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-- When the Cartan matrix entry vanishes (`A_{ji} = 0`), the Lie bracket of the
corresponding simple raising generators vanishes: `⁅e_i, e_j⁆ = 0`. -/
@[simp]
theorem lie_lieBasis_e_e_of_cartan_eq_zero (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = 0) :
    ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ = 0 := by
  have hserre := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  -- The Cartan matrix in the Serre system is the transpose: (Aᵀ)_{ij} = A_{ji}
  have hCM : (-(t.cartanMatrix.transpose i j)).toNat = 0 := by
    rw [Matrix.transpose_apply, hA]
    simp
  rw [hCM, pow_zero] at hserre
  simpa using hserre

/-- The Chevalley commutator relation (commuting case) for the represented pinning: when
the Cartan matrix entry is zero, the corresponding numbered root subgroups commute. -/
@[simp]
theorem geckRootSubgroupMatrix_comm_of_cartan_eq_zero (A : Type*) [CommRing A]
    (i j : Fin t.rank) (hA : t.cartanMatrix j i = 0)
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Commute (t.geckRootSubgroupMatrix ht (.inl i) f)
      (t.geckRootSubgroupMatrix ht (.inl j) g) := by
  have hbracket : ⁅(t.lieBasis ht).rootGenerator (.inl i),
      (t.lieBasis ht).rootGenerator (.inl j)⁆ = 0 := by
    simp only [LieAlgebra.Basis.rootGenerator_inl]
    exact t.lie_lieBasis_e_e_of_cartan_eq_zero ht i j hA
  -- The Geck root-subgroup matrices are the Kostant matrices at the pinning data.
  have hident (k : Fin t.rank ⊕ Fin t.rank)
      (q : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
      t.geckRootSubgroupMatrix ht k q =
        TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
          (t.lieBasis ht).rootGenerator (t.lieBasis ht).h (t.geckRepresentation ht)
          (t.geckCoordinateLattice ht).toAddSubgroup
          (t.geckRepresentation_kostantForm_mem_geckCoordinateLattice ht) k
          (t.isNilpotent_geckRepresentation_rootGenerator ht k)
          (t.geckCoordinateBasisFin ht) q := rfl
  rw [hident, hident]
  exact TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix
    _ _ _ _ _ _ hbracket _ _ _ _

end

end TauCeti.DynkinType
