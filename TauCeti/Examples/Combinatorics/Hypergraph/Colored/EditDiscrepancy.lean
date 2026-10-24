/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
import Mathlib.Tactic.NormNum

/-!
# Regression examples for the edit discrepancy of colored three-graphs

These downstream examples check the normalization of the edit discrepancy through the public API:
hosts with fewer than three vertices, including the empty host, have no triples and hence
discrepancy `0`, while recoloring the one triple of a three-vertex host gives `6 / 3³ = 2 / 9`,
not the fraction `1` of disagreeing unordered triples.
-/

namespace TauCeti

open Colored3Graph

-- The empty host has no triples to disagree on.
example (H H' : Colored3Graph Bool Empty) : H.editDiscrepancy3 H' = 0 := by
  simp [editDiscrepancy3_def]

-- A two-vertex host has no triples either.
example (H H' : Colored3Graph Bool (Fin 2)) : H.editDiscrepancy3 H' = 0 := by
  have : IsEmpty (Set.powersetCard (Fin 2) 3) := by
    rw [← not_nonempty_iff, Set.powersetCard.nonempty_iff]
    simp
  simp [editDiscrepancy3_def, Set.eq_empty_of_isEmpty]

-- Recoloring the single triple of a three-vertex host has discrepancy `6 / 27`.
example : (const true : Colored3Graph Bool (Fin 3)).editDiscrepancy3 (const false) = 2 / 9 := by
  have : {s : Set.powersetCard (Fin 3) 3 | true ≠ false} = Set.univ := by simp
  rw [editDiscrepancy3_def]
  simp only [color_const]
  rw [this, Set.ncard_univ, Set.powersetCard.card]
  norm_num

-- Approximations compose with their errors added.
example {V : Type*} (H₁ H₂ H₃ : Colored3Graph Bool V) (h₁₂ : H₁.Approximates3 H₂ (1 / 10))
    (h₃₂ : H₃.Approximates3 H₂ (1 / 5)) : H₁.Approximates3 H₃ (3 / 10) := by
  exact (h₁₂.trans h₃₂.symm).mono (by norm_num)

end TauCeti
