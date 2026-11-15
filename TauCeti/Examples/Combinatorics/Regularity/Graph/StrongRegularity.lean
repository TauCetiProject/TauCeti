/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Regularity.Graph.StrongRegularity

/-!
# Regression examples: induced counting for strong regularity witnesses

These examples specialize `SimpleGraph.StrongRegular.inducedGraphCount3_estimate` to the triangle
and to the edgeless pattern on three vertices, through public statements only, with the coarse
prediction written out. The triangle is predicted by the product of the three edge densities
between distinct coarse parts, and the edgeless pattern by the product of the three nonedge
densities `1 - d`: induced counting controls the absence of edges as well as their presence.
-/

open Finset SimpleGraph
open Function (Injective)

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ m : ℕ}

-- A strong regularity witness predicts the labelled triangles of `G` from the edge densities
-- between three distinct coarse parts.
example (h : G.StrongRegular P Q ε F l₀) (hF : 0 < F #P.parts) (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |((⊤ : SimpleGraph (Fin 3)).inducedGraphCount3 G : ℝ) -
        ∑ φ : Fin 3 → P.parts with Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
          ((G.edgeDensity (φ 0 : Finset V) (φ 1) : ℝ) * G.edgeDensity (φ 0 : Finset V) (φ 2) *
            G.edgeDensity (φ 1 : Finset V) (φ 2))| ≤
      (15 * F #P.parts + 3 * √ε) * Fintype.card V ^ 3 + 6 * m * Fintype.card V ^ 2 := by
  convert h.inducedGraphCount3_estimate ⊤ hF hm using 4
  rw [coarseInducedGraphEstimate_def]
  refine sum_congr rfl fun φ _ ↦ ?_
  rw [← prod_subtype ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) (by decide)
    fun p ↦ (G.patternDensity ((⊤ : SimpleGraph (Fin 3)).Adj p.1 p.2) (φ p.1 : Finset V)
      (φ p.2) : ℝ)]
  simp [mul_assoc]

-- A strong regularity witness predicts the labelled induced copies of the edgeless pattern, the
-- independent triples of `G`, from three nonedge densities between distinct coarse parts.
example (h : G.StrongRegular P Q ε F l₀) (hF : 0 < F #P.parts) (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |((⊥ : SimpleGraph (Fin 3)).inducedGraphCount3 G : ℝ) -
        ∑ φ : Fin 3 → P.parts with Injective φ, (∏ i, (#(φ i : Finset V) : ℝ)) *
          ((1 - G.edgeDensity (φ 0 : Finset V) (φ 1) : ℝ) *
            (1 - G.edgeDensity (φ 0 : Finset V) (φ 2)) *
            (1 - G.edgeDensity (φ 1 : Finset V) (φ 2)))| ≤
      (15 * F #P.parts + 3 * √ε) * Fintype.card V ^ 3 + 6 * m * Fintype.card V ^ 2 := by
  convert h.inducedGraphCount3_estimate ⊥ hF hm using 4
  rw [coarseInducedGraphEstimate_def]
  refine sum_congr rfl fun φ _ ↦ ?_
  rw [← prod_subtype ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) (by decide)
    fun p ↦ (G.patternDensity ((⊥ : SimpleGraph (Fin 3)).Adj p.1 p.2) (φ p.1 : Finset V)
      (φ p.2) : ℝ)]
  simp [mul_assoc]
