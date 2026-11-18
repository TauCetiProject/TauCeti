/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Additive
public import TauCeti.MeasureTheory.Group.Foelner.Int

/-!
# Amenability of the integer group

The intervals `{0, …, n}` in `ℤ` have cardinality `n + 1` and translation boundary at most
`2 * |k|`, so their relative boundaries tend to zero (`TauCeti.isAddFoelner_int_Icc`). This gives
additive Følner sets on `ℤ` (`TauCeti.hasAddFoelnerSets_int`) and hence additive amenability of `ℤ`
for every additive group topology (`TauCeti.AddAmenable.int`). The multiplicative counterparts for
`Multiplicative ℤ` follow directly from `TauCeti.hasFoelnerSets_multiplicative_iff` and
`TauCeti.amenable_multiplicative_iff`.

## Main results

* `TauCeti.hasAddFoelnerSets_int`, `TauCeti.hasFoelnerSets_multiplicative_int`: `ℤ` and
  `Multiplicative ℤ` have Følner sets.
* `TauCeti.AddAmenable.int`, `TauCeti.Amenable.multiplicative_int`: `ℤ` and `Multiplicative ℤ` are
  amenable for every compatible group topology.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

open Filter Finset Topology
open scoped Pointwise symmDiff

namespace TauCeti

/-- The additive group of integers has Følner sets, witnessed by the intervals `{0, …, n}`. -/
theorem hasAddFoelnerSets_int : HasAddFoelnerSets ℤ := by
  refine .of_tendsto_card_vadd_symmDiff_div_card (l := atTop)
    (F := fun n : ℕ => Icc 0 (n : ℤ))
    (Eventually.of_forall fun n => nonempty_Icc.mpr (Int.natCast_nonneg n)) fun k => ?_
  simpa only [vadd_finset_def, vadd_eq_add] using
    Int.tendsto_card_image_add_left_Icc_symmDiff_div_card k

/-- The additive group of integers is additively amenable for every additive group topology. -/
instance AddAmenable.int
    {integerTopology : TopologicalSpace ℤ}
    [hTopology : letI := integerTopology; IsTopologicalAddGroup ℤ] :
    letI := integerTopology; AddAmenable ℤ := by
  let := integerTopology
  exact .of_hasAddFoelnerSets hasAddFoelnerSets_int

/-- The integer group has Følner sets, viewed multiplicatively through `Multiplicative ℤ`. -/
theorem hasFoelnerSets_multiplicative_int : HasFoelnerSets (Multiplicative ℤ) :=
  hasFoelnerSets_multiplicative_iff.2 hasAddFoelnerSets_int

/-- The integer group is amenable for every group topology. -/
instance Amenable.multiplicative_int
    {integerTopology : TopologicalSpace (Multiplicative ℤ)}
    [hTopology : letI := integerTopology; IsTopologicalGroup (Multiplicative ℤ)] :
    letI := integerTopology; Amenable (Multiplicative ℤ) := by
  let := integerTopology
  exact .of_hasFoelnerSets hasFoelnerSets_multiplicative_int

end TauCeti
