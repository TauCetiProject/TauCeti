/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Colored.Density
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Regression examples for relative color densities

These downstream examples check relative densities through the public API. On the empty support
every density is `0`, so the densities sum to `0` rather than `1`. A constant coloring has density
`1` in its color and `0` in any other. On a mixed support, colors are read through the underlying
unordered triple and normalized by the number of ordered injections: two orderings of one triple
count twice.
-/

namespace TauCeti

open Colored3Graph Finset

-- On the empty support the densities sum to `0`, so nonemptiness is needed for them to sum to `1`.
example (H : Colored3Graph Bool (Fin 4)) : ∑ c, H.relDensityOn c ∅ = 0 := by
  simp

-- A constant coloring has density `1` in its own color on a nonempty support.
example {V : Type*} (c : Bool) {supp : Finset {x : Fin 3 → V // Function.Injective x}}
    (h : supp.Nonempty) : (const c : Colored3Graph Bool V).relDensityOn c supp = 1 := by
  rw [relDensityOn_def]
  simp [h.card_pos.ne']

-- A constant coloring has density `0` in any other color.
example {V : Type*} (c : Bool) (supp : Finset {x : Fin 3 → V // Function.Injective x}) :
    (const c : Colored3Graph Bool V).relDensityOn (!c) supp = 0 := by
  simp [relDensityOn_def]

-- Color the triples avoiding `3` by `true`. On the support consisting of two orderings of
-- `{0, 1, 2}` and one ordering of `{0, 1, 3}`, the density of `true` is `2 / 3`.
example :
    let H : Colored3Graph Bool (Fin 4) := ⟨fun s => decide ((3 : Fin 4) ∉ (s : Finset (Fin 4)))⟩
    let supp : Finset {x : Fin 3 → Fin 4 // Function.Injective x} :=
      {⟨![0, 1, 2], by decide⟩, ⟨![1, 0, 2], by decide⟩, ⟨![0, 1, 3], by decide⟩}
    H.relDensityOn true supp = 2 / 3 := by
  intro H supp
  have htrue : #{x ∈ supp | H.color (Set.powersetCard.ofFinEmb 3 (Fin 4) ⟨x.1, x.2⟩) = true} = 2 :=
    by decide
  have hsupp : #supp = 3 := by decide
  rw [relDensityOn_def, htrue, hsupp]
  norm_num

end TauCeti
