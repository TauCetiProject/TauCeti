/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Canonical.GraphSteinberg
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.DiagramAutomorphism.Root.Subgroup
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected.Frobenius

/-!
# The indexed Steinberg action on every root subgroup

The independently constructed full-weight Steinberg map of an ordinary or graph-twisted index
sends the root parameter `u` at `α` to `ε u ^ q` at the diagram image of `α`. Here `ε` is the
sign of the pinned diagram action on the named Chevalley root vector. At nonsimple roots this
sign need not be one; replacing it by one would not in general define a homomorphism.

The formula holds over every commutative ring of the indexed exponential characteristic,
including nonreduced rings. It applies in particular over the algebraic closure attached to
the index, without a point-generation assumption or a comparison with a represented family model.

The construction combines the all-root diagram equation
`DynkinType.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints` with naturality of the
Chevalley datum's root subgroups under Frobenius. The point group and root enumeration are those
of the existing full-weight Kostant construction; no new carrier or root maps are introduced.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 10, Theorem 29, and Chapter 11.
* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
-/

public section

namespace TauCeti.GraphTwistedIndex

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

attribute [local instance high] Algebra.toModule

variable (d : GraphTwistedIndex) (A : Type v) [CommRing A] [ExpChar A d.1.characteristic]

/-- On every root subgroup, the indexed Steinberg map applies field-order Frobenius to the
parameter and then the signed diagram action. The sign is indexed on the source root. -/
@[simp]
theorem scSteinberg_chevalleyToralRootSubgroupPoints
    (α : Fin d.1.dynkinType.numRoots) (u : A) :
    d.scSteinberg A
      (DynkinType.chevalleyToralRootSubgroupPoints
        (representation ℚ (d.1.dynkinType.lieAlgebra d.1.dynkinType_valid)
          (d.1.dynkinType.scModule d.1.dynkinType_valid))
        (d.1.dynkinType.scLattice d.1.dynkinType_valid).toAddSubgroup
        (d.1.dynkinType.kostantForm_apply_mem_scLattice d.1.dynkinType_valid)
        (d.1.dynkinType.isNilpotent_representation_scModule_rootGenerator d.1.dynkinType_valid)
        (d.1.dynkinType.scWeightBasis d.1.dynkinType_valid)
        (d.1.dynkinType.scWeight d.1.dynkinType_valid) α A (Multiplicative.ofAdd u)) =
      DynkinType.chevalleyToralRootSubgroupPoints _ _ _ _ _ _
        (d.1.dynkinType.diagramRootPerm d.1.dynkinType_valid
          d.diagramPerm_mem_diagramSymmetry α) A
        (Multiplicative.ofAdd
          (((d.1.dynkinType.chevalleyDiagramSign d.1.dynkinType_valid
            d.diagramPerm_mem_diagramSymmetry α : ℤ) : A) * u ^ d.1.fieldOrder)) := by
  have hγ := congrArg Subtype.val
    (d.1.dynkinType.scToralDiagramAutPoints_chevalleyToralRootSubgroupPoints
      d.1.dynkinType_valid d.diagramPerm_mem_diagramSymmetry α A
        (u ^ d.1.characteristic ^ d.1.fieldExponent))
  simp only [DynkinType.coe_scToralDiagramAutPoints] at hγ
  have hp := d.1.dynkinType.map_iterateFrobenius_chevalleyToralRootSubgroupPoints
    d.1.dynkinType_valid d.1.characteristic d.1.fieldExponent A α u
  apply Subtype.ext
  refine (d.coe_scSteinberg A _).trans ?_
  simpa only [d.1.fieldOrder_eq_characteristic_pow] using
    (congrArg (fun g => _ * g * _) hp).trans hγ

end

end TauCeti.GraphTwistedIndex
