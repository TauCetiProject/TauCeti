/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD.Basic

/-!
# Negative simple roots of the graph-twisted type-D Steinberg map

The fork-exchange graph factor and Steinberg map of `²Dₙ(q)` act on the spin carrier's lowering
subgroups through the selected diagram permutation. The graph factor preserves the additive
parameter; the Steinberg map raises it to the small-field order `q`.

These are the negative-simple-root counterparts of the equations in `TypeD.Basic`, needed when
identifying Steinberg maps by their values on both signs of the simple roots. The root maps are
the existing `TypeDSpinCarrier.rootSubgroupPoints`; the formulas specialize the carrier's signed
graph and Frobenius equations without asserting a comparison with a different ambient group.

## References

* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
-/

public section

namespace TauCeti.TypeTwistedDLieIndex

variable (d : TypeTwistedDLieIndex) (i : Fin d.1.rank) (u : Multiplicative d.1.Closure)

/-- The fork-exchange graph factor permutes negative simple roots without changing their
additive parameters. -/
@[simp]
theorem graphAut_rootSubgroupPoints_inr :
    d.graphAut (TypeDSpinCarrier.rootSubgroupPoints d.1.rank
      d.toTypeDDiagramLieIndex.four_le_rank (.inr i) d.1.Closure u) =
      TypeDSpinCarrier.rootSubgroupPoints d.1.rank d.toTypeDDiagramLieIndex.four_le_rank
        (.inr (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i)) d.1.Closure u := by
  rw [graphAut_def, TypeDSpinCarrier.graphAutPoints_rootSubgroupPoints,
    TypeDSpinCarrier.graphRootPerm_inr, diagramPerm_toGraphTwistedIndex]

/-- The `²Dₙ(q)` Steinberg map exchanges the fork nodes on negative simple roots and raises
their additive parameters to `q`. -/
@[simp]
theorem steinberg_rootSubgroupPoints_inr :
    d.steinberg (TypeDSpinCarrier.rootSubgroupPoints d.1.rank
      d.toTypeDDiagramLieIndex.four_le_rank (.inr i) d.1.Closure u) =
      TypeDSpinCarrier.rootSubgroupPoints d.1.rank d.toTypeDDiagramLieIndex.four_le_rank
        (.inr (d.toTypeDDiagramLieIndex.toGraphTwistedIndex.diagramPerm i)) d.1.Closure
        (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_def, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    TypeDDiagramLieIndex.frobenius_def, TypeDSpinCarrier.frobenius_rootSubgroupPoints,
    ← d.1.fieldOrder_eq_characteristic_pow, graphAut_rootSubgroupPoints_inr]

end TauCeti.TypeTwistedDLieIndex
