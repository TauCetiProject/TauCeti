/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Polyad.Density

/-!
# Regression example for relative color densities over polyads

This downstream example checks `relativeDensity` through the public API. Over a concrete polyad
with singleton cells, exactly one injection is supported, so every coloring has relative density
`1` in the color of its triple.
-/

namespace TauCeti

open Colored3Graph Finset

-- Over the polyad with singleton cells `{0}`, `{1}`, `{2}` in the discrete partition of `Fin 3`,
-- with all pair colors trivial, exactly one injection is supported, so every coloring has relative
-- density `1` in the color of the triple `{0, 1, 2}`.
example (H : Colored3Graph Bool (Fin 3)) :
    let S : PairSkeleton3 (Unit × Unit) (Fin 3) := ⟨⊥, PairColorSystem.ofRaw fun _ => ()⟩
    let P : Polyad3 S := Polyad3.ofData {0} {1} {2}
      (Finpartition.mem_bot_iff.2 ⟨0, mem_univ _, rfl⟩)
      (Finpartition.mem_bot_iff.2 ⟨1, mem_univ _, rfl⟩)
      (Finpartition.mem_bot_iff.2 ⟨2, mem_univ _, rfl⟩) ((), ()) ((), ()) ((), ())
    H.relativeDensity (H.color ⟨univ, by simp⟩) P = 1 := by
  intro S P
  let x₀ : {x : Fin 3 → Fin 3 // Function.Injective x} := ⟨![0, 1, 2], by decide⟩
  -- The only supported injection is `![0, 1, 2]`.
  have hsupp : P.support = {x₀} := by
    ext x
    simp only [Polyad3.mem_support, mem_singleton, P, Polyad3.ofData_c₀, Polyad3.ofData_c₁,
      Polyad3.ofData_c₂, Polyad3.ofData_color₀₁, Polyad3.ofData_color₀₂, Polyad3.ofData_color₁₂]
    constructor
    · rintro ⟨h0, h1, h2, -⟩
      exact Subtype.ext (funext fun i => by fin_cases i <;> simp [x₀, h0, h1, h2])
    · rintro rfl
      refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> simp [S, x₀, PairColorSystem.colorOfPair_of_ne]
  have htriple : Set.powersetCard.ofFinEmb 3 (Fin 3) ⟨x₀.1, x₀.2⟩ = ⟨univ, by simp⟩ :=
    Subtype.ext (by decide)
  rw [relativeDensity_def, hsupp, relDensityOn_def, filter_singleton, htriple]
  simp

end TauCeti
