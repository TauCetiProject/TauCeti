/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.Topology.Sets.Compacts

/-!
# Local compactness of model spaces from compact coordinate pieces

If an extended chart target `(extChartAt I x).target` contains a compact subset `S` with nonempty
relative interior, then because `(extChartAt I x).target` lies in the closure of its interior in
`E` (`extChartAt_target_subset_closure_interior`), the compact image `Subtype.val '' S` is a
neighbourhood of a point of `E`, so `E` is locally compact by
`IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup`
(`ModelWithCorners.locallyCompactSpace_of_nonempty_interior_extChartAt_target`). In particular,
whenever a nonempty manifold is covered by the relative interiors of compact subsets of inherited
extended chart targets, the model space is locally compact
(`ModelWithCorners.locallyCompactSpace_of_extChartAt_interior_cover`).

No smoothness, Hausdorffness, or boundarylessness assumption is needed.

## Main results

* `ModelWithCorners.locallyCompactSpace_of_nonempty_interior_extChartAt_target`: a compact subset
  with nonempty relative interior in an extended chart target forces local compactness of the model
  space.
* `ModelWithCorners.locallyCompactSpace_of_extChartAt_interior_cover`: a covering family of compact
  pieces with covering relative interiors in inherited extended chart targets on a nonempty manifold
  forces local compactness of the model space.
-/

public section

open Set Topology TopologicalSpace

namespace ModelWithCorners

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- If an extended chart target contains a compact subset with nonempty relative interior, then the
model vector space is locally compact. -/
theorem locallyCompactSpace_of_nonempty_interior_extChartAt_target
    {x : M} {S : Set (extChartAt I x).target}
    (hS : IsCompact S) (hne : (interior S).Nonempty) :
    LocallyCompactSpace E := by
  obtain ⟨z, hz⟩ := hne
  obtain ⟨U, hU, hSU⟩ := isOpen_induced_iff.mp (isOpen_interior (s := S))
  have hzU : (z : E) ∈ U := by rwa [← mem_preimage, hSU]
  have hcl : (z : E) ∈ closure (interior (extChartAt I x).target) :=
    extChartAt_target_subset_closure_interior z.property
  obtain ⟨w, hwU, hwint⟩ := mem_closure_iff.mp hcl U hU hzU
  have hsub : U ∩ interior (extChartAt I x).target ⊆ Subtype.val '' S :=
    fun v ⟨hvU, hvint⟩ ↦ ⟨⟨v, interior_subset hvint⟩, interior_subset (hSU ▸ hvU), rfl⟩
  exact (hS.image continuous_subtypeVal).locallyCompactSpace_of_mem_nhds_of_addGroup
    (Filter.mem_of_superset ((hU.inter isOpen_interior).mem_nhds ⟨hwU, hwint⟩) hsub)

/-- If a nonempty manifold is covered by the relative interiors of compact subsets of inherited
extended chart targets, then the model vector space is locally compact. -/
theorem locallyCompactSpace_of_extChartAt_interior_cover
    [Nonempty M] {ι : Type*} {U : ι → Opens M} {c : ∀ i, U i}
    {K : ∀ i, Compacts (extChartAt I (c i)).target}
    (hK : ∀ y : M, ∃ i, ∃ hyU : y ∈ U i,
      ∃ hy : (⟨y, hyU⟩ : U i) ∈ (extChartAt I (c i)).source,
        (⟨extChartAt I (c i) ⟨y, hyU⟩, (extChartAt I (c i)).map_source hy⟩ :
          (extChartAt I (c i)).target) ∈ interior (K i : Set (extChartAt I (c i)).target)) :
    LocallyCompactSpace E := by
  obtain ⟨y⟩ := ‹Nonempty M›
  obtain ⟨i, _, _, hz⟩ := hK y
  exact I.locallyCompactSpace_of_nonempty_interior_extChartAt_target (K i).isCompact ⟨_, hz⟩

end ModelWithCorners
