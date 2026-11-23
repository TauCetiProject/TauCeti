/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Additive
public import TauCeti.MeasureTheory.Group.Foelner.Int

/-!
# Amenability of the integers

The intervals `{0, …, n}` form an additive Følner sequence on `ℤ` for counting measure
(`TauCeti.isAddFoelner_int_Icc`), hence witness `TauCeti.HasAddFoelnerSets ℤ` and transport across
`Multiplicative.ofAdd` to `TauCeti.HasFoelnerSets (Multiplicative ℤ)`. The averaging criterion then
makes `ℤ` an amenable additive topological group for every additive-group topology, and
`Multiplicative ℤ` an amenable topological group for every group topology.

Amenability of `ℤ` is the base case for proving amenability of finitely generated abelian groups
via finite products of `ℤ` and surjective homomorphisms.

## Main results

* `TauCeti.hasAddFoelnerSets_int`: `ℤ` has additive Følner sets.
* `TauCeti.isFoelner_multiplicative_int_Icc`: the images of `{0, …, n}` under
  `Multiplicative.ofAdd` form a counting-measure Følner sequence on `Multiplicative ℤ`.
* `TauCeti.hasFoelnerSets_multiplicative_int`: `Multiplicative ℤ` has Følner sets.
* `TauCeti.AddAmenable.int`: `ℤ` is additively amenable for every additive-group topology.
* `TauCeti.Amenable.multiplicative_int`: `Multiplicative ℤ` is amenable for every group topology.

## References

* A. Garrido, *An introduction to amenable groups*, Example 3.5.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Example G.5.4.
-/

public section

open Filter Finset MeasureTheory
open scoped Pointwise symmDiff

namespace TauCeti

/-- The additive group `ℤ` has Følner sets, witnessed by the intervals `{0, …, n}`. -/
theorem hasAddFoelnerSets_int : HasAddFoelnerSets ℤ :=
  isAddFoelner_int_Icc.hasAddFoelnerSets

/-- Transporting the intervals `{0, …, n}` along `Multiplicative.ofAdd` gives a counting-measure
Følner sequence on `Multiplicative ℤ`. -/
theorem isFoelner_multiplicative_int_Icc :
    IsFoelner (Multiplicative ℤ) Measure.count atTop
      (fun n : ℕ => Multiplicative.ofAdd '' (Icc 0 (n : ℤ) : Set ℤ)) :=
  isFoelner_count_image_ofAdd_iff.2 isAddFoelner_int_Icc

/-- The multiplicative integer group `Multiplicative ℤ` has Følner sets. -/
theorem hasFoelnerSets_multiplicative_int : HasFoelnerSets (Multiplicative ℤ) :=
  hasFoelnerSets_multiplicative_iff.2 hasAddFoelnerSets_int

/-- The additive group of integers is amenable for every additive-group topology. -/
instance AddAmenable.int
    {integerTopology : TopologicalSpace ℤ}
    [hTopology : letI := integerTopology; IsTopologicalAddGroup ℤ] :
    letI := integerTopology; AddAmenable ℤ := by
  let := integerTopology
  exact .of_hasAddFoelnerSets hasAddFoelnerSets_int

/-- The multiplicative integer group is amenable for every group topology. -/
instance Amenable.multiplicative_int
    {integerTopology : TopologicalSpace (Multiplicative ℤ)}
    [hTopology : letI := integerTopology; IsTopologicalGroup (Multiplicative ℤ)] :
    letI := integerTopology; Amenable (Multiplicative ℤ) := by
  let := integerTopology
  exact .of_hasFoelnerSets hasFoelnerSets_multiplicative_int

end TauCeti
