/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import Mathlib.Topology.Bases
public import TauCeti.Topology.Compactness.LocallyCompact

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
instance secondCountableTopology [Countable D.J]
    [∀ i, SecondCountableTopology (D.U i)] : SecondCountableTopology D.toGlueData.glued := by
  let U : D.J → Set D.toGlueData.glued := fun i ↦ range (D.toGlueData.ι i)
  have hU (i : D.J) : IsOpen (U i) := (D.ι_isOpenEmbedding i).isOpen_range
  have hcover : ⋃ i, U i = univ := iUnion_eq_univ_iff.2 fun x ↦ D.ι_jointly_surjective x
  let hCount : ∀ i : D.J, SecondCountableTopology (U i) := fun i ↦
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph.symm.isEmbedding.secondCountableTopology
  exact TopologicalSpace.secondCountableTopology_of_countable_cover hU hcover

/-- A glued space with locally compact charts is locally compact. -/
instance locallyCompactSpace [∀ i, LocallyCompactSpace (D.U i)] :
    LocallyCompactSpace D.toGlueData.glued := by
  let U : D.J → Set D.toGlueData.glued := fun i ↦ range (D.toGlueData.ι i)
  have hU (i : D.J) : IsOpen (U i) := (D.ι_isOpenEmbedding i).isOpen_range
  have hcover : ⋃ i, U i = univ := iUnion_eq_univ_iff.2 fun x ↦ D.ι_jointly_surjective x
  let hCompact : ∀ i : D.J, LocallyCompactSpace (U i) := fun i ↦
    (D.ι_isOpenEmbedding i).isEmbedding.toHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  exact TauCeti.locallyCompactSpace_of_isOpen_cover hU hcover

end TopCat.GlueData
