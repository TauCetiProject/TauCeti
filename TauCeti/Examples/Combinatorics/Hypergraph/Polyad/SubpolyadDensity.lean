/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Polyad.Density
import TauCeti.Combinatorics.Hypergraph.Polyad.Subpolyad
import Mathlib.Tactic.NormNum

/-!
# Regression example: relative density on a subpolyad

On four vertices with one vertex cell and one pair color, color only the unordered triple
`{0, 1, 2}` by `true`. The parent polyad supports all `24` injective triples, six of which order
`{0, 1, 2}`, so its relative density of `true` is `1 / 4`. Keeping only the zero-one pairs
`(0, 1)` and `(1, 2)` gives a subpolyad supporting the four triples `(0, 1, 2)`, `(0, 1, 3)`,
`(1, 2, 0)` and `(1, 2, 3)`, two of which order `{0, 1, 2}`, so its relative density is `1 / 2`.
This exercises unordered coloring, ordered support, pair pruning and normalization together.
-/

namespace TauCeti

open Finset Colored3Graph

example :
    let S : PairSkeleton3 Unit (Fin 4) :=
      ⟨Finpartition.indiscrete univ_nonempty.ne_empty,
        ⟨fun _ ↦ (), id, fun _ ↦ rfl, fun _ ↦ rfl⟩⟩
    let P : Polyad3 S := Polyad3.ofData univ univ univ (by simp [S]) (by simp [S]) (by simp [S])
      () () ()
    let Q : Subpolyad3 P :=
      ⟨P.pairSupport₀₁.filter fun p ↦ p.1 = (0, 1) ∨ p.1 = (1, 2), P.pairSupport₀₂,
        P.pairSupport₁₂, filter_subset _ _, Subset.rfl, Subset.rfl⟩
    let H : Colored3Graph Bool (Fin 4) := ⟨fun s ↦ decide ((s : Finset (Fin 4)) = {0, 1, 2})⟩
    H.relativeDensity true P = 1 / 4 ∧ H.relDensityOn true Q.support = 1 / 2 := by
  intro S P Q H
  -- Every injective triple is supported by the parent polyad.
  have hP : P.support = univ := by
    ext x
    simp only [Polyad3.mem_support, mem_univ, iff_true, P, S, Polyad3.ofData_c₀,
      Polyad3.ofData_c₁, Polyad3.ofData_c₂, Polyad3.ofData_color₀₁, Polyad3.ofData_color₀₂,
      Polyad3.ofData_color₁₂, true_and]
    refine ⟨?_, ?_, ?_⟩ <;> exact PairColorSystem.colorOfPair_of_ne _ (x.2.ne (by decide))
  -- The subpolyad supports exactly the triples whose first two entries are `(0, 1)` or `(1, 2)`.
  have hQ : Q.support = univ.filter fun x : {x : Fin 3 → Fin 4 // Function.Injective x} ↦
      (x.1 0 = 0 ∧ x.1 1 = 1) ∨ (x.1 0 = 1 ∧ x.1 1 = 2) := by
    ext x
    rw [Subpolyad3.mem_support_iff_coordPair_mem]
    simp [Q, P, S, coe_coordPair]
  refine ⟨?_, ?_⟩
  · have htrue : #{x ∈ (univ : Finset {x : Fin 3 → Fin 4 // Function.Injective x}) |
        H.color (Set.powersetCard.ofFinEmb 3 (Fin 4) ⟨x.1, x.2⟩) = true} = 6 := by decide
    have hcard : #(univ : Finset {x : Fin 3 → Fin 4 // Function.Injective x}) = 24 := by decide
    rw [relativeDensity_def, hP, relDensityOn_def, htrue, hcard]
    norm_num
  · rw [hQ, relDensityOn_def]
    have htrue : #{x ∈ univ.filter fun x : {x : Fin 3 → Fin 4 // Function.Injective x} ↦
        (x.1 0 = 0 ∧ x.1 1 = 1) ∨ (x.1 0 = 1 ∧ x.1 1 = 2) |
          H.color (Set.powersetCard.ofFinEmb 3 (Fin 4) ⟨x.1, x.2⟩) = true} = 2 := by decide
    have hcard : #(univ.filter fun x : {x : Fin 3 → Fin 4 // Function.Injective x} ↦
        (x.1 0 = 0 ∧ x.1 1 = 1) ∨ (x.1 0 = 1 ∧ x.1 1 = 2)) = 4 := by decide
    rw [htrue, hcard]
    norm_num

end TauCeti
