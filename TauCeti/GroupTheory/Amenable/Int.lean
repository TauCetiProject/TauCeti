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

The integer intervals `{0, …, n}` form an additive Følner sequence for counting measure
(`TauCeti.isAddFoelner_int_Icc`), so `ℤ` has additive Følner sets (`TauCeti.hasAddFoelnerSets_int`)
and is amenable as an additive topological group for every additive group topology
(`TauCeti.AddAmenable.int`). Transporting across `Multiplicative` yields
`TauCeti.hasFoelnerSets_multiplicative_int` and `TauCeti.Amenable.multiplicative_int`.

Amenability of the integers is the starting example for proving amenability of finitely generated
abelian groups using finite products and surjective homomorphisms.

## Main results

* `TauCeti.hasAddFoelnerSets_int`: `ℤ` has additive Følner sets.
* `TauCeti.AddAmenable.int`: `ℤ` is amenable for every additive group topology.
* `TauCeti.hasFoelnerSets_multiplicative_int`: `Multiplicative ℤ` has Følner sets.
* `TauCeti.Amenable.multiplicative_int`: `Multiplicative ℤ` is amenable for every group topology.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

namespace TauCeti

/-- The additive group of integers has Følner sets, witnessed by the intervals `{0, …, n}`. -/
theorem hasAddFoelnerSets_int : HasAddFoelnerSets ℤ :=
  hasAddFoelnerSets_iff.2 fun K _ hε =>
    isAddFoelner_int_Icc.exists_finset_card_vadd_symmDiff_lt K hε

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
