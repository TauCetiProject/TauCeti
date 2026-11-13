/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Frobenius
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.SimplyConnected

/-!
# Frobenius on the full-weight root-subgroup matrices

The Frobenius equation for a Chevalley datum specializes to the unbundled full-weight
root-subgroup points. This matrix-level equation uses the original lattice and weight basis,
so it applies directly to the independently constructed full-weight Steinberg map.
-/

public section

namespace TauCeti.DynkinType

open _root_.TauCeti.UniversalEnvelopingAlgebra

universe v

noncomputable section

attribute [local instance high] Algebra.toModule

variable (t : DynkinType) (ht : t.Valid)

/-- Entrywise Frobenius raises every full-weight root parameter to its `p ^ k`-th power,
over any commutative ring of exponential characteristic `p`. -/
@[simp]
theorem map_iterateFrobenius_chevalleyToralRootSubgroupPoints
    (p k : ℕ) (A : Type v) [CommRing A] [ExpChar A p]
    (α : Fin t.numRoots) (u : A) :
    Matrix.GeneralLinearGroup.map (iterateFrobenius A p k)
        (chevalleyToralRootSubgroupPoints
          (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
          (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
          (t.isNilpotent_representation_scModule_rootGenerator ht)
          (t.scWeightBasis ht) (t.scWeight ht) α A (Multiplicative.ofAdd u) :
            Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) =
      (chevalleyToralRootSubgroupPoints
        (representation ℚ (t.lieAlgebra ht) (t.scModule ht))
        (t.scLattice ht).toAddSubgroup (t.kostantForm_apply_mem_scLattice ht)
        (t.isNilpotent_representation_scModule_rootGenerator ht)
        (t.scWeightBasis ht) (t.scWeight ht) α A (Multiplicative.ofAdd (u ^ p ^ k)) :
          Matrix.GeneralLinearGroup (Fin (t.scWeightBasisCard ht)) A) := by
  have hf := congrArg Subtype.val
    ((t.scChevalleyDatum ht).frobenius_rootSubgroupPoints p k A α u)
  simp only [ChevalleyDatum.coe_frobenius, ChevalleyDatum.coe_rootSubgroupPoints] at hf
  -- Reduce the dependent datum fields together: rewriting the lattice alone would leave
  -- its stability proof and the basis indexed by the old lattice.
  dsimp only [scChevalleyDatum] at hf
  simp only [coe_chevalleyToralRootSubgroupPoints]
  exact hf

end

end TauCeti.DynkinType
