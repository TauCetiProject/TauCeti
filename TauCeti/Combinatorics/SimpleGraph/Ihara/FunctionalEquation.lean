/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Hashimoto
import TauCeti.Combinatorics.SimpleGraph.Degree
import TauCeti.Combinatorics.SimpleGraph.Ihara.Regular

/-!
# The functional equation of the Ihara zeta function of a regular graph

Let `G` be a finite `(q + 1)`-regular simple graph with `q ≥ 1`, with `n` vertices, `e` edges,
adjacency matrix `A` and Hashimoto matrix `B`. The Ihara zeta function of `G` is
`ζ(u) = det (1 - u B)⁻¹` (`SimpleGraph.iharaZeta_eq_inv_charpolyRev`). With
`ξ(u) = (1 + u) ^ (e - n) (1 - u) ^ e (1 - q u) ^ n ζ(u)`, the functional equation is
`ξ(u) = ξ(1 / (q u))`. This file proves it cross-multiplied, so that no determinant is inverted:

`(1 + u) ^ (e - n) (1 - u) ^ e (1 - q u) ^ n det (1 - w B)`
`  = (1 + w) ^ (e - n) (1 - w) ^ e (1 - u⁻¹) ^ n det (1 - u B)` for `w = (q u)⁻¹`.

The identity holds over every field in which `q` is nonzero. Bass's formula for a regular graph
gives `det (1 - u B) = (1 - u²) ^ (e - n) det ((1 + q u²) - u A)` over every commutative ring
(`SimpleGraph.det_one_sub_smul_hashimotoMatrix_of_isRegularOfDegree`). At
`w` the vertex matrix is `(1 + q w²) - w A = (q u²)⁻¹ ((1 + q u²) - u A)`, and
`(1 - w) (1 - q w) = (1 - u) (1 - q u) / (q u²)`; these two facts give the identity. At `u = 0`
both sides are `1`, by the convention `0⁻¹ = 0`. Connectivity is not used. The hypothesis on `q`
is needed: for `K₂` (`q = 0`) at `u = 2` the left side is `-1` and the right side is `1 / 4`.

## Main results

* `SimpleGraph.functional_equation_of_isRegularOfDegree`: the functional equation, over every field
  in which `q` is nonzero, for instance over `ℂ` for `q ≥ 1`.

## References

* A. Terras, *A Stroll Through the Garden of Graph Zeta Functions*, draft of 29 December 2009:
  Proposition 3 (2), p. 28, for connected regular graphs, with its proof as Exercise 21, p. 29.
  The book *Zeta Functions of Graphs: A Stroll through the Garden* (Cambridge University Press,
  2011) grew from this draft.
-/

public section

open Finset Matrix Polynomial

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {q : ℕ}

/-- **The functional equation of the Ihara zeta function of a regular graph.** If `G` is
`(q + 1)`-regular and `q` is nonzero in the field `K`, then for every `u : K`, with
`w = (q u)⁻¹`, `n` vertices and `e` edges,
`(1 + u) ^ (e - n) (1 - u) ^ e (1 - q u) ^ n det (1 - w B)`
`  = (1 + w) ^ (e - n) (1 - w) ^ e (1 - u⁻¹) ^ n det (1 - u B)`.
For `u ≠ 0` this is `ξ(u) = ξ(w)`, cross-multiplied, for
`ξ(u) = (1 + u) ^ (e - n) (1 - u) ^ e (1 - q u) ^ n ζ(u)`. At `u = 0` both sides are `1`, since
`0⁻¹ = 0`. Over `ℂ`, or any field of characteristic zero, the hypothesis on `q` is `1 ≤ q`. -/
theorem functional_equation_of_isRegularOfDegree {K : Type*} [Field K] (hq : (q : K) ≠ 0)
    (hG : G.IsRegularOfDegree (q + 1)) (u : K) :
    (1 + u) ^ (#G.edgeFinset - Fintype.card V) * (1 - u) ^ #G.edgeFinset *
        (1 - q * u) ^ Fintype.card V * Matrix.det (1 - (q * u)⁻¹ • G.hashimotoMatrix K) =
      (1 + (q * u)⁻¹) ^ (#G.edgeFinset - Fintype.card V) * (1 - (q * u)⁻¹) ^ #G.edgeFinset *
        (1 - u⁻¹) ^ Fintype.card V * Matrix.det (1 - u • G.hashimotoMatrix K) := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.2 fun h ↦ hq (by simp [h])
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (hG.card_le_card_edgeFinset (by omega))
  set c : K := (q * u ^ 2)⁻¹
  -- The vertex matrix at `w = (q u)⁻¹` is the vertex matrix at `u` scaled by `(q u²)⁻¹`.
  have hscale : scalar V (1 + q * (q * u)⁻¹ ^ 2) - (q * u)⁻¹ • G.adjMatrix K =
      c • (scalar V (1 + q * u ^ 2) - u • G.adjMatrix K) := by
    simp only [c, scalar_apply, ← smul_one_eq_diagonal, smul_sub, smul_smul]
    congr 2 <;> field_simp
    ring
  have hkey : (1 - (q * u)⁻¹) * (1 - u⁻¹) = (1 - u) * (1 - q * u) * c := by
    simp only [c]
    field_simp
    ring
  have hsq : ∀ x : K, 1 - x ^ 2 = (1 + x) * (1 - x) := fun x ↦ by ring
  rw [det_one_sub_smul_hashimotoMatrix_of_isRegularOfDegree hG hq1,
    det_one_sub_smul_hashimotoMatrix_of_isRegularOfDegree hG hq1, hscale, det_smul, hk,
    Nat.add_sub_cancel_left]
  simp only [hsq]
  -- Make every base an atom, so that `ring` splits no power with a variable exponent.
  generalize (scalar V (1 + q * u ^ 2) - u • G.adjMatrix K).det = P
  generalize 1 + u = a
  generalize 1 + (q * u)⁻¹ = a'
  generalize 1 - (q * u)⁻¹ = b' at hkey ⊢
  generalize 1 - u⁻¹ = d' at hkey ⊢
  generalize 1 - q * u = d at hkey ⊢
  generalize 1 - u = b at hkey ⊢
  calc _ = a ^ k * b ^ k * a' ^ k * b' ^ k * P * (b * d * c) ^ Fintype.card V := by ring
    _ = _ := by rw [← hkey]; ring

end SimpleGraph
