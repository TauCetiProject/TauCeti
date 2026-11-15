/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Combinatorics.SimpleGraph.Hasse
import TauCeti.Combinatorics.Regularity.Graph.FriezeKannan

/-!
# Regression example: the finite Frieze–Kannan theorem on a concrete graph

At `ε = 1 / 2` the part bound `4 ^ ⌈1 / ε²⌉` of `SimpleGraph.frieze_kannan` evaluates to
`4 ^ 4 = 256`, and the rectangle error `ε * (card V) ^ 2` on a four-vertex host is `8`. The
example reads both off the public statement for the path `0 - 1 - 2 - 3`.
-/

open Finset SimpleGraph

-- The path on four vertices has a partition into at most `256` parts predicting the number of
-- edges of every rectangle up to `8`.
example : ∃ P : Finpartition (univ : Finset (Fin 4)), #P.parts ≤ 256 ∧ ∀ A B : Finset (Fin 4),
    |(#((pathGraph 4).interedges A B) : ℝ) - (pathGraph 4).steppedCount P A B| ≤ 8 := by
  obtain ⟨P, hcard, hP⟩ := (pathGraph 4).frieze_kannan (ε := 1 / 2) (by norm_num)
  have hceil : ⌈1 / (1 / 2 : ℝ) ^ 2⌉₊ = 4 := by norm_num
  refine ⟨P, by rwa [hceil] at hcard, fun A B ↦ (hP A B).trans_eq ?_⟩
  norm_num
