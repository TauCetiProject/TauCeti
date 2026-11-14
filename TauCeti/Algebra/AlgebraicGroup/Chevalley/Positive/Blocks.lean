/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Positive.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Blocks
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Weight-space block unitriangularity of positive Chevalley points

In the weight basis of a Chevalley datum `D`, `orderedWeightBlock (t.weightDegree ht) D.weight`
groups basis indices by their distinct weights and numbers those weight spaces by decreasing
root-height degree. Every positive root has strictly positive degree, so each positive root
subgroup acts by block upper unitriangular matrices with identity diagonal blocks on every weight
space. Closure of `Matrix.BlockUnitriangular` under products and inverses extends this shape to
the entire positive point subgroup `D.positivePoints A`, over every commutative ring `A`.

This module also packages the induced numbering of `Set.range D.weight` as an equivalence
`weightBlockEquiv`, matching the distinct-weight block convention of
`TauCeti.DynkinType.ChevalleyDatum.isUnit_leading_weight_minors_weylWord_iff` and
`TauCeti.DynkinType.ChevalleyDatum.exists_blockLDU_weylWord_iff`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17, and Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

-- Match the tensor product with the integral algebra structure on the value ring.
attribute [local instance high] Algebra.toModule

/-- The distinct weights of a Chevalley datum numbered by decreasing height degree, specializing
`TauCeti.UniversalEnvelopingAlgebra.weightBlockEquiv`. -/
noncomputable def weightBlockEquiv :
    Set.range D.weight ≃ Fin (Nat.card (Set.range D.weight)) :=
  UniversalEnvelopingAlgebra.weightBlockEquiv (t.weightDegree ht) D.weight

/-- Evaluating `weightBlockEquiv` at the weight of a basis vector recovers `orderedWeightBlock`. -/
theorem weightBlockEquiv_weight (j : Fin D.dim) :
    D.weightBlockEquiv ⟨D.weight j, Set.mem_range_self j⟩ =
      orderedWeightBlock (t.weightDegree ht) D.weight j :=
  weightBlockEquiv_mk (t.weightDegree ht) D.weight j (Set.mem_range_self j)

/-- Every positive root element acts by a block upper unitriangular matrix in the distinct-weight
blocks ordered by decreasing height degree, over every commutative ring. -/
theorem blockUnitriangular_orderedWeightBlock_rootSubgroupPoints
    (A : Type v) [CommRing A] {γ : Fin t.numRoots}
    (hγ : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : Multiplicative A) :
    (((D.rootSubgroupPoints γ A u : D.points A) :
      Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A).BlockUnitriangular
        (orderedWeightBlock (t.weightDegree ht) D.weight) := by
  have hmat : ((D.rootSubgroupPoints γ A u : D.points A) :
      Matrix.GeneralLinearGroup (Fin D.dim) A) =
      kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h D.representation
        D.lattice (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
          D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
        γ (isNilpotent_apply_ι_chevalleySystem D.representation
          D.isNilpotent_representation_rootGenerator γ) D.basis
        ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm u) := by
    rw [D.coe_rootSubgroupPoints γ A u,
      ← kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator]
    exact (matrix_kostantRootSubgroupParam (t.chevalleySystem ht) (t.lieBasis ht).h
      D.representation D.lattice (kostantForm_chevalleySystem_smul_mem D.representation
        D.lattice D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      (isNilpotent_apply_ι_chevalleySystem D.representation
        D.isNilpotent_representation_rootGenerator)
      D.basis D.coordinateWeight A γ u).trans
      (coe_kostantToralRootSubgroupPoints _ _ _ _ _ _ _ _ γ A u)
  rw [hmat]
  exact blockUnitriangular_kostantRootSubgroupMatrix (t.chevalleySystem ht) (t.lieBasis ht).h
    D.representation D.lattice
    (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
    D.basis D.weight (t.weightDegree ht) γ
    (isNilpotent_apply_ι_chevalleySystem D.representation
      D.isNilpotent_representation_rootGenerator γ)
    D.isCartanWeightVector_basis (t.lie_lieBasis_h_chevalleySystem ht γ)
    (t.weightDegree_root_pos ht hγ) _

/-- Every element of `D.positivePoints A` acts by a block upper unitriangular matrix in the
distinct-weight blocks ordered by decreasing height degree, over every commutative ring. -/
theorem blockUnitriangular_orderedWeightBlock_of_mem_positivePoints
    {A : Type v} [CommRing A] {g : D.points A} (hg : g ∈ D.positivePoints A) :
    ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A).BlockUnitriangular
        (orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.positivePoints_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨γ, hγ, u, rfl⟩ := hx
    exact D.blockUnitriangular_orderedWeightBlock_rootSubgroupPoints A hγ u
  | one =>
    simpa only [Subgroup.coe_one, Units.val_one] using Matrix.blockUnitriangular_one
  | mul x y _ _ hx hy =>
    simpa only [Subgroup.coe_mul, Units.val_mul] using hx.mul hy
  | inv x _ hx =>
    have hinv : (((x⁻¹ : D.points A) : Matrix.GeneralLinearGroup (Fin D.dim) A) :
        Matrix (Fin D.dim) (Fin D.dim) A) =
        (((x : Matrix.GeneralLinearGroup (Fin D.dim) A) :
          Matrix (Fin D.dim) (Fin D.dim) A))⁻¹ := by
      rw [Subgroup.coe_inv, Matrix.coe_units_inv]
    rw [hinv]
    exact hx.inv

end TauCeti.DynkinType.ChevalleyDatum
