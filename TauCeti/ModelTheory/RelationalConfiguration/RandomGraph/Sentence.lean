/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.RelationalConfiguration
public import TauCeti.ModelTheory.Graph.Random
public import TauCeti.ModelTheory.RelationalConfiguration.ModelsOf
import TauCeti.ModelTheory.Scott.RandomGraph

/-!
# The random-graph model class

On `ℕ`, the configurations satisfying the conjunction of the simple-graph and extension axioms
are exactly the codes of graphs isomorphic to the Rado graph.
-/

public section

open FirstOrder FirstOrder.Language

namespace TauCeti.RelationalConfiguration

/-- The model class of the conjunction of the simple-graph and extension axioms is exactly the
graph coding of the Rado isomorphism class. -/
theorem modelsOf_randomGraphSentence :
    modelsOf randomGraphSentence =
      SimpleGraph.toRelationalConfiguration '' {G : SimpleGraph ℕ | Nonempty (G ≃g radoGraph)} := by
  ext c
  simp only [mem_modelsOf, Set.mem_image, Set.mem_ofPred_eq]
  constructor
  · intro hc
    let _ := c.toStructure
    have hmodel : ℕ ⊨ Theory.randomGraph := realize_randomGraphSentence_iff.mp hc
    have _ : ℕ ⊨ Theory.simpleGraph := hmodel.mono Theory.simpleGraph_subset_randomGraph
    let G := simpleGraphOfStructure ℕ
    have hstructure : G.structure = c.toStructure := structure_simpleGraphOfStructure
    refine ⟨G, nonempty_iso_radoGraph_iff.mpr (G.randomGraph_model_iff.mp ?_), ?_⟩
    · rw [hstructure]
      exact hmodel
    · apply equivStructure.injective
      simpa only [equivStructure_apply, G.toStructure_toRelationalConfiguration] using hstructure
  · rintro ⟨G, hG, rfl⟩
    rw [SimpleGraph.toStructure_toRelationalConfiguration]
    exact (@realize_randomGraphSentence_iff ℕ G.structure).mpr
      (G.randomGraph_model_iff.mpr (nonempty_iso_radoGraph_iff.mp hG))

end TauCeti.RelationalConfiguration
