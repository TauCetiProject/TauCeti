/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Combinatorics.SimpleGraph.Clique.Tag

/-!
# Examples of clique-tagged graphs

* The tagged graph of a single edge `{0, 1}` coloured `(0, 1)` has `2 + 3 + 4 = 9` vertices.
* A vertex of colour `0` and a vertex of colour `1` have non-isomorphic tagged graphs: the first
  tag is a triangle, the second a `K₄`.
* Triangle-freeness is needed to recognise the tags: in the tagged graph of a triangle, the
  original vertices lie in triangles too.
-/

open SimpleGraph

-- The single edge on `Fin 2`, coloured by `Fin.val` (so `(0, 1)`), has a tagged graph on
-- `2 + 3 + 4 = 9` vertices.
example : Fintype.card (Fin 2 ⊕ Σ x : Fin 2, Fin ((x : ℕ) + 3)) = 9 := by
  simp [Fin.sum_univ_two]

-- A single vertex of colour `0` and a single vertex of colour `1`: the tagged graphs (a triangle
-- and a `K₄`, each with a pendant vertex) are not isomorphic.
example :
    IsEmpty ((⊥ : SimpleGraph Unit).cliqueTag (fun _ ↦ 0) ≃g
      (⊥ : SimpleGraph Unit).cliqueTag (fun _ ↦ 1)) := by
  have hbot : (⊥ : SimpleGraph Unit).CliqueFree 3 := cliqueFree_bot (by decide)
  rw [← not_nonempty_iff, nonempty_iso_cliqueTag_iff hbot hbot]
  simp

-- Without triangle-freeness the recognition of tags fails: in the tagged graph of the triangle
-- `⊤` on `Fin 3`, the original vertex `0` lies in a triangle.
example : ∃ s, ((⊤ : SimpleGraph (Fin 3)).cliqueTag (fun _ ↦ 0)).IsNClique 3 s ∧
    Sum.inl 0 ∈ s :=
  exists_isNClique_three_mem_iff.2 ⟨.inl 1, .inl 2, by simp, by simp, by simp⟩
