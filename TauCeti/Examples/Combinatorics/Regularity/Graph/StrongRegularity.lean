/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Regularity.Graph.StrongRegularity.Counting
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Three-vertex induced counting examples

The strong counting estimate applies to both triangles and independent triples. Their predictions
use three edge densities and three nonedge densities, respectively. Exact three-vertex counts
are checked separately in `TauCeti/Examples/Combinatorics/Regularity/Graph/InducedCount.lean`.
-/

open Finset SimpleGraph

namespace TauCeti

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  {P Q : Finpartition (univ : Finset V)} {ε : ℝ} {F : ℕ → ℝ} {l₀ m : ℕ}

-- The complete three-vertex pattern has three edge-density factors.
example (A : Fin 3 → Finset V) :
    (∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (G.patternDensity ((⊤ : SimpleGraph (Fin 3)).Adj p.1.1 p.1.2) (A p.1.1) (A p.1.2) : ℝ)) =
      G.edgeDensity (A 0) (A 1) * G.edgeDensity (A 0) (A 2) * G.edgeDensity (A 1) (A 2) := by
  rw [← prod_subtype ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) (by decide)
    (fun p ↦ (G.patternDensity ((⊤ : SimpleGraph (Fin 3)).Adj p.1 p.2) (A p.1) (A p.2) : ℝ))]
  simp [patternDensity_def, mul_assoc]

-- The independent triple has three nonedge-density factors.
example (A : Fin 3 → Finset V) :
    (∏ p : {p : Fin 3 × Fin 3 // p.1 < p.2},
      (G.patternDensity ((⊥ : SimpleGraph (Fin 3)).Adj p.1.1 p.1.2) (A p.1.1) (A p.1.2) : ℝ)) =
      (1 - G.edgeDensity (A 0) (A 1)) * (1 - G.edgeDensity (A 0) (A 2)) *
        (1 - G.edgeDensity (A 1) (A 2)) := by
  rw [← prod_subtype ({(0, 1), (0, 2), (1, 2)} : Finset (Fin 3 × Fin 3)) (by decide)
    (fun p ↦ (G.patternDensity ((⊥ : SimpleGraph (Fin 3)).Adj p.1 p.2) (A p.1) (A p.2) : ℝ))]
  simp [mul_assoc]

example (h : G.StrongRegular P Q ε F l₀) (hF : 0 < F #P.parts)
    (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |((⊤ : SimpleGraph (Fin 3)).inducedGraphCount3 G : ℝ) -
        (⊤ : SimpleGraph (Fin 3)).coarseInducedGraphEstimate3 G P| ≤
      (16 * F #P.parts + 3 * √ε) * (Fintype.card V : ℝ) ^ 3 +
        6 * m * (Fintype.card V : ℝ) ^ 2 :=
  inducedGraphCount3_estimate_of_strongRegular h ⊤ hF hm

example (h : G.StrongRegular P Q ε F l₀) (hF : 0 < F #P.parts)
    (hm : ∀ A ∈ P.parts, #A ≤ m) :
    |((⊥ : SimpleGraph (Fin 3)).inducedGraphCount3 G : ℝ) -
        (⊥ : SimpleGraph (Fin 3)).coarseInducedGraphEstimate3 G P| ≤
      (16 * F #P.parts + 3 * √ε) * (Fintype.card V : ℝ) ^ 3 +
        6 * m * (Fintype.card V : ℝ) ^ 2 :=
  inducedGraphCount3_estimate_of_strongRegular h ⊥ hF hm

end TauCeti
