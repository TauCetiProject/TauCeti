/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeA.Basic

/-!
# Negative simple roots of the type-A Steinberg maps

The graph factor and Steinberg map of a type-A index act on the standard carrier's lowering
subgroups by the index's diagram permutation. The additive parameter is unchanged by the graph
factor and raised to the field order by the Steinberg map. This includes both the untwisted and
twisted families, with the identity and chain reversal respectively.

These equations complement the positive-simple-root equations in `TypeA.Basic`. Together they
supply the signed simple-root values needed to compare the represented Steinberg map with an
independently constructed map. We use `SlStd.rootSubgroupPoints` directly, without introducing
another family of root maps. The proof uses the standard carrier's signed graph and Frobenius
formulas and the native index's diagram permutation.

## References

* R. W. Carter, *Finite Groups of Lie Type*, §§1.15–1.17.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 10–11.
-/

public section

namespace TauCeti.TypeALieIndex

variable (d : TypeALieIndex) (i : Fin d.1.rank) (u : Multiplicative d.1.Closure)

/-- The type-A graph factor sends the lowering subgroup at `i` to the lowering subgroup at the
selected diagram image, with no sign or change of additive parameter. -/
@[simp]
theorem graphAut_rootSubgroupPoints_inr :
    d.graphAut (SlStd.rootSubgroupPoints d.1.rank (.inr i) d.1.Closure u) =
      SlStd.rootSubgroupPoints d.1.rank (.inr (d.toGraphTwistedIndex.diagramPerm i))
        d.1.Closure u := by
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [graphAut_ofA, MulAut.one_apply, GraphTwistedIndex.diagramPerm_A,
      Equiv.Perm.one_apply]
  · rw [graphAut_ofTwistedA, SlStd.graphAutomorphismPoints_rootSubgroupPoints,
      GraphTwistedIndex.diagramPerm_twistedA]
    -- The constructor's rank reduces to `rank`; the carrier and diagram lemmas use that
    -- reduced node type rather than `Fin (ofTwistedA rank q hvalid).1.rank`.
    change Fin rank at i
    change SlStd.rootSubgroupPoints rank (SlStd.graphRootPerm rank (.inr i)) _ _ =
      SlStd.rootSubgroupPoints rank (.inr (graphPermA rank i)) _ _
    rw [SlStd.graphRootPerm_inr, graphPermA_apply]

/-- The type-A Steinberg map applies the selected diagram permutation to negative simple roots
and raises their additive parameters to the indexed field order. -/
@[simp]
theorem steinberg_rootSubgroupPoints_inr :
    d.steinberg (SlStd.rootSubgroupPoints d.1.rank (.inr i) d.1.Closure u) =
      SlStd.rootSubgroupPoints d.1.rank (.inr (d.toGraphTwistedIndex.diagramPerm i))
        d.1.Closure (Multiplicative.ofAdd (Multiplicative.toAdd u ^ d.1.fieldOrder)) := by
  rw [steinberg_eq_graphAut_comp_frobenius, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    frobenius_def, SlStd.frobenius_rootSubgroupPoints,
    ← d.1.fieldOrder_eq_characteristic_pow, graphAut_rootSubgroupPoints_inr]

end TauCeti.TypeALieIndex
