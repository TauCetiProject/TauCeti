/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Countability and local compactness of glued spaces

A space obtained by gluing open charts is second countable when the chart family is countable
and every chart is second countable. It is locally compact when every chart is locally compact.
These results apply to gluing data without any separation assumption on the glued space.
-/

public section

open CategoryTheory Set Topology

namespace TopCat.GlueData

variable (D : TopCat.GlueData)

/-- A glued space with countably many second-countable charts is second countable. -/
theorem secondCountableTopology [Countable D.J]
    [∀ i, SecondCountableTopology (D.U i)] : SecondCountableTopology D.toGlueData.glued := by
  let U : D.J → Set D.toGlueData.glued := fun i ↦ range (D.toGlueData.ι i)
  have hU (i : D.J) : IsOpen (U i) := (D.ι_isOpenEmbedding i).isOpen_range
  have hcover : ⋃ i, U i = univ := by
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
    exact ⟨i, y, rfl⟩
  have hCount : ∀ i : D.J, SecondCountableTopology (U i) := fun i ↦
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  exact @TopologicalSpace.secondCountableTopology_of_countable_cover _ _ _ _ U hCount hU hcover

/-- A glued space with locally compact charts is locally compact. -/
theorem locallyCompactSpace [∀ i, LocallyCompactSpace (D.U i)] :
    LocallyCompactSpace D.toGlueData.glued := by
  refine ⟨fun x W hW ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  let f := D.toGlueData.ι i
  have hf : IsOpenEmbedding f := D.ι_isOpenEmbedding i
  obtain ⟨K, hKy, hKW, hKc⟩ := local_compact_nhds
    (hf.continuous.continuousAt hW : f ⁻¹' W ∈ 𝓝 y)
  refine ⟨f '' K, hf.isOpenMap.image_mem_nhds hKy, ?_, hKc.image hf.continuous⟩
  exact image_subset_iff.mpr hKW

end TopCat.GlueData
