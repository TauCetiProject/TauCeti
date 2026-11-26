/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Weight.Blocks
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.WeightDegree

/-!
# Weight blocks of positive and negative Chevalley points

Every positive point of a Chevalley datum is upper unitriangular in the blocks of its
actual weight spaces. In particular, its restriction to each weight block is the identity,
including weight spaces of multiplicity greater than one. This is useful for separating
the positive subgroup from the torus centralizer, without assuming root coordinates or
Bruhat decomposition. Dually, every negative point is lower unitriangular for the same
numbering of the weight blocks (and upper unitriangular when ordered by negated height degree),
which places the big-cell factors `U⁻`, `T` and `U` in the block `LDU` shape.

The root-matrix calculations are `blockUnitriangular_kostantRootSubgroupMatrix` and
`blockUnitriangular_toDual_kostantRootSubgroupMatrix`; closure under group operations extends
them to all positive and all negative points. The results hold over every commutative value
ring.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 17.
* J. C. Jantzen, *Representations of Algebraic Groups*, Part II, Chapter 1.
-/

public section

open TauCeti.UniversalEnvelopingAlgebra

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type v) [CommRing A]

attribute [local instance high] Algebra.toModule

/-- Every root element whose root is strictly positive under an additive rational weight functional
`degree` is upper unitriangular in the weight-space blocks ordered by `degree`. -/
theorem blockUnitriangular_rootSubgroupPoints_of_degree_pos
    (degree : (Fin t.rank → ℤ) →+ ℚ) {γ : Fin t.numRoots}
    (hdeg : 0 < degree ((t.simplyConnectedRootDatum ht).root γ))
    (u : Multiplicative A) :
    ((D.rootSubgroupPoints γ A u : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A).BlockUnitriangular
        (orderedWeightBlock degree D.weight) := by
  rw [D.coe_rootSubgroupPoints,
    ← kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
      D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
    basisMatrix_kostantRootSubgroupParam]
  exact blockUnitriangular_kostantRootSubgroupMatrix
    (t.chevalleySystem ht) (t.lieBasis ht).h D.representation D.lattice _ D.basis D.weight
    degree γ _ D.isCartanWeightVector_basis
    (t.lie_lieBasis_h_chevalleySystem ht γ) hdeg _

/-- A positive root subgroup is upper unitriangular in the blocks of distinct weights ordered by
decreasing height degree, using the datum's original weight basis. -/
theorem blockUnitriangular_rootSubgroupPoints_of_mem_posRoots {γ : Fin t.numRoots}
    (hγ : γ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : Multiplicative A) :
    ((D.rootSubgroupPoints γ A u : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A).BlockUnitriangular
        (orderedWeightBlock (t.weightDegree ht) D.weight) :=
  D.blockUnitriangular_rootSubgroupPoints_of_degree_pos A (t.weightDegree ht)
    (t.weightDegree_root_pos ht hγ) u

/-- A negative root subgroup is upper unitriangular in the weight-space blocks ordered by negated
height degree. -/
theorem blockUnitriangular_rootSubgroupPoints_of_mem_negRoots {γ : Fin t.numRoots}
    (hγ : γ ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht))
    (u : Multiplicative A) :
    ((D.rootSubgroupPoints γ A u : Matrix.GeneralLinearGroup (Fin D.dim) A) :
      Matrix (Fin D.dim) (Fin D.dim) A).BlockUnitriangular
        (orderedWeightBlock (-t.weightDegree ht) D.weight) :=
  D.blockUnitriangular_rootSubgroupPoints_of_degree_pos A (-t.weightDegree ht)
    (neg_pos.mpr (t.weightDegree_root_neg ht hγ)) u

/-- Positive Chevalley points are upper unitriangular in their weight-space blocks.
The blocks are indexed by distinct weights, not by individual basis vectors. -/
theorem blockUnitriangular_of_mem_positivePoints {g : D.points A}
    (hg : g ∈ D.positivePoints A) :
    Matrix.BlockUnitriangular
      ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)
      (orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.positivePoints_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨γ, hγ, u, rfl⟩ := hg
    exact D.blockUnitriangular_rootSubgroupPoints_of_mem_posRoots A hγ u
  -- The characterization also reconciles the order instances on the finite block index.
  | one => simpa only [Subgroup.coe_one, Units.val_one, Matrix.blockUnitriangular_iff] using
      (Matrix.blockUnitriangular_one
        (R := A) (b := orderedWeightBlock (t.weightDegree ht) D.weight))
  | mul g h _ _ hg hh =>
    simpa only [Subgroup.coe_mul, Units.val_mul, Matrix.blockUnitriangular_iff] using hg.mul hh
  | inv g _ hg =>
    simpa only [Subgroup.coe_inv, Matrix.coe_units_inv, Matrix.blockUnitriangular_iff] using hg.inv

/-- On each entire weight space, a positive point has the identity matrix block. -/
theorem coe_apply_eq_one_apply_of_mem_positivePoints_of_weight_eq {g : D.points A}
    (hg : g ∈ D.positivePoints A) {i j : Fin D.dim} (hij : D.weight i = D.weight j) :
    ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) i j =
      (1 : Matrix (Fin D.dim) (Fin D.dim) A) i j :=
  (D.blockUnitriangular_of_mem_positivePoints A hg).apply_of_eq
    ((orderedWeightBlock_eq_iff _ _).mpr hij)

/-- Negative Chevalley points are lower unitriangular in their weight-space blocks, for the same
numbering of the blocks as the positive points. -/
theorem blockUnitriangular_toDual_of_mem_negativePoints {g : D.points A}
    (hg : g ∈ D.negativePoints A) :
    Matrix.BlockUnitriangular
      ((g : Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)
      (OrderDual.toDual ∘ orderedWeightBlock (t.weightDegree ht) D.weight) := by
  rw [D.negativePoints_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨γ, hγ, u, rfl⟩ := hg
    rw [D.coe_rootSubgroupPoints,
      ← kostantRootSubgroupParam_chevalleySystem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator,
      basisMatrix_kostantRootSubgroupParam]
    exact blockUnitriangular_toDual_kostantRootSubgroupMatrix (t.chevalleySystem ht)
      (t.lieBasis ht).h D.representation D.lattice
      (kostantForm_chevalleySystem_smul_mem D.representation D.lattice
        D.representation_mem_lattice D.isNilpotent_representation_rootGenerator)
      D.basis D.weight (t.weightDegree ht) γ _ D.isCartanWeightVector_basis
      (t.lie_lieBasis_h_chevalleySystem ht γ) (t.weightDegree_root_neg ht hγ) _
  -- As for positive points, the characterization reconciles the order instances on the blocks.
  | one => simpa only [Subgroup.coe_one, Units.val_one, Matrix.blockUnitriangular_iff] using
      (Matrix.blockUnitriangular_one
        (R := A) (b := OrderDual.toDual ∘ orderedWeightBlock (t.weightDegree ht) D.weight))
  | mul g h _ _ hg hh =>
    simpa only [Subgroup.coe_mul, Units.val_mul, Matrix.blockUnitriangular_iff] using hg.mul hh
  | inv g _ hg =>
    simpa only [Subgroup.coe_inv, Matrix.coe_units_inv, Matrix.blockUnitriangular_iff] using hg.inv

end TauCeti.DynkinType.ChevalleyDatum
