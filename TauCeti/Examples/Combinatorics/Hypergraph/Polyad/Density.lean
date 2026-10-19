/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Combinatorics.Hypergraph.Polyad.Density

/-!
# Regression examples for relative color densities

These downstream examples check relative densities through the public API. On the empty support
every density is `0`, so the densities sum to `0` rather than `1`. A constant coloring has density
`1` in its color and `0` in any other. On a mixed support, colors are read through the underlying
unordered triple and normalized by the number of ordered injections: two orderings of one triple
count twice. Over a concrete polyad with singleton cells, exactly one injection is supported, so
every coloring has relative density `1` in the color of its triple.
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
