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
machinery. The uniform exponentials `u ↦ exp(u • e_i)` over any `ℚ`-algebra are provided by
`TauCeti.DynkinType.pinnedExp`, a thin wrapper over the existing
`TauCeti.DynkinType.geckRootSubgroupMatrix` that converts the scalar to a `𝔾ₐ`-point; this
module contributes only the bracket relations and their direct transfer to the represented
pinning.

## Main results

* `TauCeti.DynkinType.lie_lieBasis_e_e_of_cartan_eq_zero`: when the Cartan matrix entry
  vanishes (`A_{ji} = 0`), the Lie bracket `⁅e_i, e_j⁆ = 0` — the Serre relation.
* `TauCeti.DynkinType.coe_lieBasis_e_comm_of_cartan_eq_zero`: the corresponding matrix
  commutativity.
* `TauCeti.DynkinType.geckRootSubgroupMatrix_comm_of_cartan_eq_zero`: the Chevalley
  commutator relation (commuting case) for the represented pinning — the existing Kostant
  commutativity lemma applied through `geckRootSubgroupMatrix`.
* `TauCeti.DynkinType.pinnedExp`: the uniform exponential `u ↦ exp(u • e_i)` over any
  `ℚ`-algebra, as a thin wrapper over `TauCeti.DynkinType.geckRootSubgroupMatrix`; with the
  root-subgroup identification
  `TauCeti.DynkinType.pinnedExp_eq_coe_geckRootSubgroupPoints`, the one-parameter law,
  and the commuting-case Chevalley relation
  `TauCeti.DynkinType.pinnedExp_comm_of_cartan_eq_zero`.
* `TauCeti.DynkinType.lie_lieBasis_e_e_e_of_cartan_eq_neg_one`: for a length-one root
  string (`A_{ji} = -1`), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes — the one-sided
  Serre relation.

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

/-! ## The uniform exponential -/

/-- The uniform exponential `u ↦ exp(u • e_i)` of the `i`-th simple raising generator, as a
thin wrapper over `TauCeti.DynkinType.geckRootSubgroupMatrix`: the scalar `u : A` in any
`ℚ`-algebra is converted to a `𝔾ₐ`-point through `Multiplicative.ofAdd` and
`TauCeti.AdditiveGroup.gaPointsMulEquiv`. No exponential matrix is re-implemented here; the
divided-power exponential nature of the underlying matrix is recorded in
`TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix_eq_sum`, and the
identification with the root-subgroup construction in
`TauCeti.DynkinType.pinnedExp_eq_coe_geckRootSubgroupPoints`. -/
noncomputable def pinnedExp (A : Type*) [CommRing A] [Algebra ℚ A]
    (i : Fin t.rank) (u : A) :
    Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A :=
  t.geckRootSubgroupMatrix ht (.inl i)
    ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (Multiplicative.ofAdd u))

/-- **Identification of the uniform exponential with the root-subgroup construction.**
`pinnedExp` is the coercion to the general linear group of the parametrized Geck
root-subgroup point `TauCeti.DynkinType.geckRootSubgroupPoints` at the corresponding
`𝔾ₐ`-parameter. -/
theorem pinnedExp_eq_coe_geckRootSubgroupPoints (A : Type*) [CommRing A] [Algebra ℚ A]
    (i : Fin t.rank) (u : A) :
    t.pinnedExp ht A i u =
      (t.geckRootSubgroupPoints ht (.inl i) A (Multiplicative.ofAdd u) :
        Matrix.GeneralLinearGroup (Fin (t.geckDim ht)) A) := by
  rw [t.coe_geckRootSubgroupPoints ht]
  rfl

/-- The uniform exponential at `u = 0` is the identity matrix. -/
theorem pinnedExp_zero (A : Type*) [CommRing A] [Algebra ℚ A] (i : Fin t.rank) :
    t.pinnedExp ht A i 0 = 1 := by
  simp [pinnedExp]

/-- The one-parameter subgroup law: `exp(u • e_i) * exp(v • e_i) = exp((u + v) • e_i)`,
inherited from the monoid-hom structure of the root-subgroup matrix. -/
theorem pinnedExp_mul (A : Type*) [CommRing A] [Algebra ℚ A]
    (i : Fin t.rank) (u v : A) :
    t.pinnedExp ht A i u * t.pinnedExp ht A i v = t.pinnedExp ht A i (u + v) := by
  simp only [pinnedExp, ← map_mul]
  rfl

/-- The Chevalley commutator relation (commuting case) for the uniform exponentials: when
the Cartan matrix entry is zero, the corresponding exponentials commute. This is
`TauCeti.DynkinType.geckRootSubgroupMatrix_comm_of_cartan_eq_zero` through the
`pinnedExp` interface. -/
theorem pinnedExp_comm_of_cartan_eq_zero (A : Type*) [CommRing A] [Algebra ℚ A]
    (i j : Fin t.rank) (hA : t.cartanMatrix j i = 0) (u v : A) :
    Commute (t.pinnedExp ht A i u) (t.pinnedExp ht A j v) :=
  t.geckRootSubgroupMatrix_comm_of_cartan_eq_zero ht A i j hA _ _

/-! ## Length-one root strings: one-sided Serre vanishing -/

/-- For a length-one root string (`A_{ji} = -1`, i.e., `α_i + α_j` is a root but
`2α_i + α_j` is not), the double bracket `⁅e_i, ⁅e_i, e_j⁆⁆` vanishes. This is the Serre
relation: `(ad e_i)^{-A_{ji}}(⁅e_i, e_j⁆) = (ad e_i)(⁅e_i, e_j⁆) = 0`. Only this one-sided
vanishing is proved: no symmetric statement is claimed, since in multiply-laced types
(`B₂`, `C₂`, `G₂`) the reverse Cartan entry `A_{ij}` may be `-2` or `-3`, and the
Chevalley commutator formula can then involve further root factors beyond
`x_{α_i+α_j}`. -/
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
