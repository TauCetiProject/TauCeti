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

If an extended chart target `(extChartAt I x).target` contains a compact subset with nonempty
relative interior, the corresponding open subset of the manifold is nonempty and locally compact,
so by `LocallyCompactSpace.of_locallyCompact_manifold` the model vector space `E` is locally
compact (`ModelWithCorners.locallyCompactSpace_of_nonempty_interior_extChartAt_target`). In
particular, whenever a nonempty manifold is covered by the relative interiors of compact subsets of
inherited extended chart targets, the model space is locally compact
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
  obtain ⟨U, hU, hSU⟩ := isOpen_induced_iff.mp (isOpen_interior (s := S))
  let O : Opens M := ⟨(extChartAt I x).source ∩ extChartAt I x ⁻¹' U,
    (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x) hU⟩
  have hmem : ∀ y : O, (⟨extChartAt I x y, (extChartAt I x).map_source y.property.1⟩ :
      (extChartAt I x).target) ∈ interior S :=
    fun y ↦ hSU ▸ y.property.2
  have : Nonempty O := by
    obtain ⟨z, hz⟩ := hne
    refine ⟨⟨(extChartAt I x).symm z, (extChartAt I x).map_target z.property, ?_⟩⟩
    rw [mem_preimage, (extChartAt I x).right_inv z.property]
    exact (hSU ▸ hz : z ∈ Subtype.val ⁻¹' U)
  have : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let V : Set S := {z | (z.val : E) ∈ U}
  have hV_open : IsOpen V := hU.preimage (continuous_subtypeVal.comp continuous_subtypeVal)
  have : LocallyCompactSpace V := hV_open.locallyCompactSpace
  let e : O ≃ₜ V :=
    { toFun y := ⟨⟨⟨extChartAt I x y, (extChartAt I x).map_source y.property.1⟩,
        interior_subset (hmem y)⟩, y.property.2⟩
      invFun z := ⟨(extChartAt I x).symm z.val.val, (extChartAt I x).map_target z.val.val.property,
        by rw [mem_preimage, (extChartAt I x).right_inv z.val.val.property]; exact z.property⟩
      left_inv y := Subtype.ext ((extChartAt I x).left_inv y.property.1)
      right_inv z := Subtype.ext (Subtype.ext (Subtype.ext
        ((extChartAt I x).right_inv z.val.val.property)))
      continuous_toFun := Continuous.subtype_mk (Continuous.subtype_mk (Continuous.subtype_mk
        ((continuousOn_extChartAt x).comp_continuous continuous_subtypeVal
          fun y ↦ y.property.1) _) _) _
      continuous_invFun := Continuous.subtype_mk
        ((continuousOn_extChartAt_symm x).comp_continuous
          (continuous_subtypeVal.comp (continuous_subtypeVal.comp continuous_subtypeVal))
          fun z ↦ z.val.val.property) _ }
  have : LocallyCompactSpace O := e.isOpenEmbedding.locallyCompactSpace
  exact LocallyCompactSpace.of_locallyCompact_manifold O I

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
