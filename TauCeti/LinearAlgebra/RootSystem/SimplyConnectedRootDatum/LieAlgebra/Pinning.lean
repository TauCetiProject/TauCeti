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
machinery. The uniform exponentials themselves are provided by
`TauCeti.DynkinType.geckRootSubgroupMatrix`; this module contributes only the bracket
relations and their direct transfer to the represented pinning.

## Main results

* `TauCeti.DynkinType.lie_lieBasis_e_e_of_cartan_eq_zero`: when the Cartan matrix entry
  vanishes (`A_{ji} = 0`), the Lie bracket `⁅e_i, e_j⁆ = 0` — the Serre relation.
* `TauCeti.DynkinType.coe_lieBasis_e_comm_of_cartan_eq_zero`: the corresponding matrix
  commutativity.
* `TauCeti.DynkinType.geckRootSubgroupMatrix_comm_of_cartan_eq_zero`: the Chevalley
  commutator relation (commuting case) for the represented pinning — the existing Kostant
  commutativity lemma applied through `geckRootSubgroupMatrix`.
* `TauCeti.DynkinType.lie_lieBasis_e_e_e_of_cartan_eq_neg_one`: for a length-one root
  string (`A_{ji} = -1`), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes — the Heisenberg
  Lie-algebra structure underlying the non-commuting Chevalley commutator formula.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247.
* R. W. Carter, *Simple Groups of Lie Type*, §4.4.
* J. E. Humphreys, *Linear Algebraic Groups*, §26.

Roadmap: ReductiveGroups (Layer 9, uniform pinned Chevalley-Demazure construction).
-/

public section

namespace TauCeti.DynkinType

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

variable (t : DynkinType) (ht : t.Valid)

/-- The Lie bracket of distinct simple raising generators vanishes when the corresponding
Cartan matrix entry is zero. This is the Serre relation: when `A_{ji} = 0`, the exponent
`(-Aᵀ_{ij}).toNat = 0`, so `(ad e_i)^0 [e_i, e_j] = [e_i, e_j] = 0`. -/
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

/-- When the Cartan matrix entry vanishes, the simple raising generators commute as matrices.
The Lie bracket in the matrix Lie algebra is the commutator, so a vanishing bracket gives
commuting matrices, via `commute_iff_lie_eq`. -/
theorem coe_lieBasis_e_comm_of_cartan_eq_zero (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = 0) :
    ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
     ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
    ((t.lieBasis ht).e j : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) *
     ((t.lieBasis ht).e i : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) := by
  have hbracket := t.lie_lieBasis_e_e_of_cartan_eq_zero ht i j hA
  -- The inclusion of the Lie subalgebra preserves brackets
  have hcoe : ((((⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆ : t.lieAlgebra ht))) :
      Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ) =
      ⁅(((t.lieBasis ht).e i) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ),
       (((t.lieBasis ht).e j) : Matrix (t.GeckIndex ht) (t.GeckIndex ht) ℚ)⁆ :=
    LieSubalgebra.coe_bracket (t.lieAlgebra ht) _ _
  rw [hbracket, ZeroMemClass.coe_zero] at hcoe
  exact (commute_iff_lie_eq.mpr hcoe.symm).eq

/-- The Chevalley commutator relation (commuting case) for the represented pinning: when
the Cartan matrix entry is zero — i.e., when `α_i + α_j` is not a root — the corresponding
numbered root subgroups commute. This is the existing Kostant commutativity lemma
`TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix` applied to the
pinning matrices `TauCeti.DynkinType.geckRootSubgroupMatrix`, with the bracket hypothesis
supplied by the Serre relation
`TauCeti.DynkinType.lie_lieBasis_e_e_of_cartan_eq_zero`. -/
theorem geckRootSubgroupMatrix_comm_of_cartan_eq_zero (A : Type*) [CommRing A]
    (i j : Fin t.rank) (hA : t.cartanMatrix j i = 0)
    (f g : WithConv (SymmetricAlgebra ℤ ℤ →ₐ[ℤ] A)) :
    Commute (t.geckRootSubgroupMatrix ht (.inl i) f)
      (t.geckRootSubgroupMatrix ht (.inl j) g) := by
  have hbracket : ⁅(t.lieBasis ht).rootGenerator (.inl i),
      (t.lieBasis ht).rootGenerator (.inl j)⁆ = 0 := by
    simp only [LieAlgebra.Basis.rootGenerator_inl]
    exact t.lie_lieBasis_e_e_of_cartan_eq_zero ht i j hA
  exact TauCeti.UniversalEnvelopingAlgebra.commute_kostantRootSubgroupMatrix
    _ _ _ _ _ _ hbracket _ _ _ _

/-! ## Length-one root strings: Heisenberg Lie algebra structure -/

/-- For a length-one root string (`A_{ji} = -1`, i.e., `α_i + α_j` is a root but
`2α_i + α_j` is not), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes. This is the Serre
relation: `(ad e_i)^{-A_{ji}}(⁅e_i, e_j⁆) = (ad e_i)(⁅e_i, e_j⁆) = 0`. Together with the symmetric
statement, this says the subalgebra generated by `e_i, e_j` is Heisenberg, the Lie-algebra
input to the Chevalley commutator formula
`[x_{α_i}(u), x_{α_j}(v)] = x_{α_i+α_j}(N_{ij} uv)`. -/
theorem lie_lieBasis_e_e_e_of_cartan_eq_neg_one (i j : Fin t.rank)
    (hA : t.cartanMatrix j i = -1) :
    ⁅(t.lieBasis ht).e i, ⁅(t.lieBasis ht).e i, (t.lieBasis ht).e j⁆⁆ = 0 := by
  have hserre := (t.isSerreSystem_lieBasis ht).ad_pow_lie_E_E i j
  -- The Cartan matrix in the Serre system is the transpose: (Aᵀ)_{ij} = A_{ji} = -1
  -- So (-(Aᵀ)_{ij}).toNat = (-(-1)).toNat = 1
  have hCM : (-(t.cartanMatrix.transpose i j)).toNat = 1 := by
    rw [Matrix.transpose_apply, hA]
    simp
  rw [hCM] at hserre
  -- (ad e_i)^1(⁅e_i, e_j⁆) = ⁅e_i, ⁅e_i, e_j⁆⁆
  simpa using hserre

end

end TauCeti.DynkinType
