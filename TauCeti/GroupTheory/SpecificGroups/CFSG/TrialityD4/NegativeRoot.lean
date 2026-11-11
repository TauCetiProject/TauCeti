/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TrialityD4.Basic

/-!
# Negative simple roots of the triality Steinberg map

On the tripled D₄ carrier, triality sends the negative simple root subgroup at `i` to the one
at `σ i`, for the native source-node cycle `σ = (0 2 3)`. The Steinberg composite sends its
additive parameter `u` to `u^q`, with `q` the small-field parameter. The node action here is the
forward permutation, not the inverse permutation used for character pullback.

These equations complement the positive-root equations in `TrialityD4.Basic`, supplying both
signs for root-compatible Steinberg comparisons. They specialize the existing signed-root
triality and Frobenius equations of `D4Tripled`, retaining its 24-dimensional carrier and the
native rank identification. No ambient-group comparison is assumed or asserted.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §§12.2 and 14.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
-/

public section

namespace TauCeti.TypeTrialityD4LieIndex

variable (d : TypeTrialityD4LieIndex) (i : Fin d.1.rank) (u : Multiplicative d.1.Closure)

/-- Triality permutes the negative simple roots by the selected forward node cycle, with no
sign or change of additive parameter. -/
-- Match the indexed node before simp expands its dependent rank transport.
@[simp↓]
theorem graphAut_rootSubgroupPoints_inr :
    d.graphAut (D4Tripled.rootSubgroupPoints (.inr (finCongr d.rank_eq_four i)) d.1.Closure u) =
      D4Tripled.rootSubgroupPoints
        (.inr (finCongr d.rank_eq_four
          (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i))) d.1.Closure u := by
  rw [graphAut_def, D4Tripled.trialityPoints_rootSubgroupPoints,
    MinusculeWeightTable.Symmetry.rootPerm_inr, D4Tripled.trialitySymmetry_nodePerm,
    diagramPerm_toGraphTwistedIndex]
  -- The rank transports are inverse even though their equality proofs are written separately.
  have hcast (j : Fin 4) : finCongr d.rank_eq_four (finCongr d.rank_eq_four.symm j) = j :=
    Fin.ext rfl
  rw [hcast]

/-- The `³D₄(q)` Steinberg map applies the selected forward triality cycle to negative simple
roots and raises their additive parameters to the small-field order `q`. -/
@[simp↓]
theorem steinberg_rootSubgroupPoints_inr :
    d.steinberg (D4Tripled.rootSubgroupPoints (.inr (finCongr d.rank_eq_four i)) d.1.Closure u) =
      D4Tripled.rootSubgroupPoints
        (.inr (finCongr d.rank_eq_four
          (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i))) d.1.Closure
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    frobenius_def, D4Tripled.frobenius_rootSubgroupPoints,
    ← d.1.fieldOrder_eq_characteristic_pow, graphAut_rootSubgroupPoints_inr]

end TauCeti.TypeTrialityD4LieIndex
