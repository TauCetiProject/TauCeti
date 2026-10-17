/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Density
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.NormNum

/-!
# Pair-color density examples

Recording the source vertex as a raw color on two vertices gives two genuinely oriented
colors, exchanged by reversal. The whole square has two distinct pairs, so each of these
colors has density one half. A coincident singleton has no distinct pairs and density zero,
whereas two different singletons have density one in their prescribed color.
-/

open Finset

namespace TauCeti

private def directedTwo : PairColorSystem (Fin 2 × Fin 2) (Fin 2) :=
  PairColorSystem.ofRaw (fun p => p.val.1)

example : directedTwo.rev (0, 1) = (1, 0) := by
  simp [directedTwo]

example : directedTwo.colorOfPair 0 1 = some (0, 1) := by
  simp [directedTwo]

example : directedTwo.colorOfPair 1 0 = some (1, 0) := by
  simp [directedTwo]

example : pairColorDensity directedTwo (0, 1) {0} {1} = 1 := by
  norm_num [pairColorDensity_def, Finset.filter_singleton, directedTwo]

example : pairColorDensity directedTwo (1, 0) {0} {1} = 0 := by
  norm_num [pairColorDensity_def, Finset.filter_singleton, directedTwo]

/-- Recording the source vertex as a raw color gives density one half for the oriented
color `(0, 1)` on the full two-vertex square. -/
public theorem pairColorDensity_ofRaw_fst_fin_two :
    pairColorDensity (PairColorSystem.ofRaw
      (fun p : {p : Fin 2 × Fin 2 // p.1 ≠ p.2} => p.val.1)) (0, 1) univ univ = 1 / 2 := by
  classical
  simp only [pairColorDensity_def, card_eq_sum_ones, sum_filter, sum_product]
  norm_num [Fin.univ_succ, filter_insert, filter_singleton]

example : pairColorDensity directedTwo (1, 0) univ univ = 1 / 2 := by
  have h := pairColorDensity_swap directedTwo (0, 1) univ univ
  simp only [directedTwo, PairColorSystem.ofRaw_rev] at h ⊢
  exact h.trans pairColorDensity_ofRaw_fst_fin_two

example : ∑ c, pairColorDensity directedTwo c {0} {1} = 1 := by
  classical
  apply sum_pairColorDensity
  exact ⟨(0, 1), by simp⟩

example : ∑ c, pairColorDensity directedTwo c {0} {0} = 0 := by
  simp

end TauCeti
