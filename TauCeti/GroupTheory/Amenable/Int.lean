/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Average
public import TauCeti.MeasureTheory.Group.Foelner.Int

/-!
# Amenability of the integers

The integer intervals `{0, …, n}` form a counting-measure additive Følner sequence
(`TauCeti.isAddFoelner_int_Icc`), so `ℤ` has additive Følner sets (`TauCeti.hasAddFoelnerSets_int`)
and is amenable for every additive group topology (`TauCeti.AddAmenable.int`). Transporting across
`Multiplicative` gives `TauCeti.hasFoelnerSets_multiplicative_int` and
`TauCeti.Amenable.multiplicative_int`.

Amenability of the integers is the starting example for proving amenability of finitely generated
abelian groups using finite products and surjective homomorphisms.

## Main results

* `TauCeti.hasAddFoelnerSets_int`, `TauCeti.hasFoelnerSets_multiplicative_int`: `ℤ` and
  `Multiplicative ℤ` have Følner sets.
* `TauCeti.AddAmenable.int`, `TauCeti.Amenable.multiplicative_int`: `ℤ` and `Multiplicative ℤ` are
  amenable for every group topology.

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
  let : MeasurableSpace ℤ := ⊤
  exact ((isAddFoelner_iff_tendsto _ _).1 isAddFoelner_int_Icc).neBot

/-- The additive group of integers is amenable for every additive group topology. -/
instance AddAmenable.int
    {integerTopology : TopologicalSpace ℤ}
    [hTopology : letI := integerTopology; IsTopologicalAddGroup ℤ] :
    letI := integerTopology; AddAmenable ℤ := by
  let := integerTopology
  exact .of_hasAddFoelnerSets hasAddFoelnerSets_int

/-- The integer group has Følner sets, viewed multiplicatively through `Multiplicative.ofAdd`. -/
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
