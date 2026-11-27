/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.Combinatorics.SimpleGraph.Hashimoto
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.Combinatorics.SimpleGraph.Degree
import TauCeti.Combinatorics.SimpleGraph.Ihara.Bass
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# The Hashimoto matrix of a regular graph

Let `G` be a finite `(q + 1)`-regular simple graph with `q ≥ 1`, with `n` vertices, `e` edges and
adjacency eigenvalues `λ_v` (counted with multiplicity, indexed by the vertices). Its Hashimoto
(non-backtracking edge) matrix `B` has characteristic polynomial

`det (X - B) = (X² - 1) ^ (e - n) ∏ᵥ (X² - λ_v X + q)`.

So the eigenvalues of `B` are `1` and `-1`, each at least `e - n = n (q - 1) / 2` times, and for
each adjacency eigenvalue `λ` the two roots of `μ² - λ μ + q`, whose product is `q`. This is the
starting point of the functional equation of the Ihara zeta function of a regular graph and of the
equivalence between the Ramanujan property and the Riemann hypothesis for it.

For a regular graph `D - 1 = q`, so Bass's three-term formula
(`SimpleGraph.charpolyRev_eq_of_add_dartSymmMatrix_eq_of_card_le`) reads
`det (1 - X B) = (1 - X²) ^ (e - n) det ((1 + q X²) - X A)`, and the spectral theorem factors the
vertex side as `∏ᵥ (1 - λ_v X + q X²)`. Reversing, at the dimension `2e` of `B`, gives the
characteristic polynomial. Connectivity is not used. The hypothesis `q ≥ 1` gives `n ≤ e`, which
makes the natural subtraction `e - n` the true difference; for `q = 0` (a perfect matching, for
instance `K₂`) `B = 0` and the formulas fail.

## Main results

* `SimpleGraph.charpolyRev_hashimotoMatrix_of_isRegularOfDegree`:
  `det (1 - X B) = (1 - X²) ^ (e - n) ∏ᵥ (1 - λ_v X + q X²)`.
* `SimpleGraph.charpoly_hashimotoMatrix_of_isRegularOfDegree`:
  `det (X - B) = (X² - 1) ^ (e - n) ∏ᵥ (X² - λ_v X + q)`.

## References

* A. Terras, *A Stroll Through the Garden of Graph Zeta Functions*, draft of 29 December 2009: the
  proof of Theorem 3 in §7, for connected regular graphs. The book *Zeta Functions of Graphs: A
  Stroll through the Garden* (Cambridge University Press, 2011) grew from this draft.
-/

public section

open Finset Matrix Polynomial

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {q : ℕ}

/-- **The reversed characteristic polynomial of the Hashimoto matrix of a regular graph.** If `G`
is `(q + 1)`-regular with `q ≥ 1`, then `det (1 - X B) = (1 - X²) ^ (e - n) ∏ᵥ (1 - λ_v X + q X²)`,
where `n` is the number of vertices, `e` the number of edges and `λ_v` the adjacency
eigenvalues. -/
theorem charpolyRev_hashimotoMatrix_of_isRegularOfDegree (hG : G.IsRegularOfDegree (q + 1))
    (hq : 1 ≤ q) :
    (G.hashimotoMatrix ℝ).charpolyRev = (1 - X ^ 2) ^ (#G.edgeFinset - Fintype.card V) *
      ∏ v, (1 - C ((G.isHermitian_adjMatrix ℝ).eigenvalues v) * X + C (q : ℝ) * X ^ 2) := by
  rw [charpolyRev_eq_of_add_dartSymmMatrix_eq_of_card_le G hashimotoMatrix_add_dartSymmMatrix
    (hG.card_le_card_edgeFinset (by omega)), hG.degMatrix_eq ℝ[X]]
  congr 1
  refine Polynomial.funext fun t ↦ ?_
  have hM : (evalRingHom t).mapMatrix
      (1 - (X : ℝ[X]) • G.adjMatrix ℝ[X] + (X ^ 2 : ℝ[X]) • (((q + 1 : ℕ) : Matrix V V ℝ[X]) - 1)) =
      scalar V (1 + q * t ^ 2) - t • G.adjMatrix ℝ := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.natCast_apply, mul_comm]
    · simp [one_apply_ne hij, Matrix.natCast_apply, hij, apply_ite (eval t)]
  -- `c - t A = c (1 - (t / c) A)` for the unit `c = 1 + q t²`, and `1 - s A` is diagonalised by
  -- the spectral theorem.
  have hc : (1 + q * t ^ 2 : ℝ) ≠ 0 := by positivity
  have hsmul : scalar V (1 + q * t ^ 2) - t • G.adjMatrix ℝ =
      (1 + q * t ^ 2) • (1 - (t / (1 + q * t ^ 2)) • G.adjMatrix ℝ) := by
    rw [smul_sub, smul_smul, mul_div_cancel₀ _ hc, smul_one_eq_diagonal, scalar_apply]
  rw [← coe_evalRingHom, RingHom.map_det, hM, hsmul, det_smul,
    (G.isHermitian_adjMatrix ℝ).det_one_sub_smul, ← card_univ, ← prod_const, ← prod_mul_distrib,
    map_prod]
  refine prod_congr rfl fun v _ ↦ ?_
  simp only [RCLike.ofReal_real_eq_id, id_eq, map_natCast, coe_evalRingHom, eval_add, eval_sub,
    eval_one, eval_mul, eval_C, eval_X, eval_natCast, eval_pow]
  field_simp
  ring

/-- **The characteristic polynomial of the Hashimoto matrix of a regular graph.** If `G` is
`(q + 1)`-regular with `q ≥ 1`, then `det (X - B) = (X² - 1) ^ (e - n) ∏ᵥ (X² - λ_v X + q)`,
where `n` is the number of vertices, `e` the number of edges and `λ_v` the adjacency eigenvalues.
So the eigenvalues of `B` are `±1`, each at least `e - n` times, and the roots of `μ² - λ_v μ + q`
for each vertex `v`. -/
theorem charpoly_hashimotoMatrix_of_isRegularOfDegree (hG : G.IsRegularOfDegree (q + 1))
    (hq : 1 ≤ q) :
    (G.hashimotoMatrix ℝ).charpoly = (X ^ 2 - 1) ^ (#G.edgeFinset - Fintype.card V) *
      ∏ v, (X ^ 2 - C ((G.isHermitian_adjMatrix ℝ).eigenvalues v) * X + C (q : ℝ)) := by
  set B := G.hashimotoMatrix ℝ
  have hcard : Fintype.card G.Dart =
      2 * (#G.edgeFinset - Fintype.card V) + 2 * Fintype.card V := by
    rw [dart_card_eq_twice_card_edges]
    have := hG.card_le_card_edgeFinset (by omega)
    omega
  -- Both sides agree at every `t ≠ 0`: `det (t - B) = t ^ (2e) det (1 - t⁻¹ B)`.
  refine eq_of_infinite_eval_eq _ _ ((Set.finite_singleton (0 : ℝ)).infinite_compl.mono
    fun t ht ↦ ?_)
  have ht : t ≠ 0 := Set.mem_compl_singleton_iff.1 ht
  have hpow : (t ^ 2) ^ Fintype.card V = ∏ _v : V, t ^ 2 := by
    rw [prod_const, card_univ]
  rw [Set.mem_ofPred_eq, B.eval_charpoly_eq_pow_mul_eval_charpolyRev (mul_inv_cancel₀ ht),
    charpolyRev_hashimotoMatrix_of_isRegularOfDegree hG hq, hcard, pow_add, pow_mul, pow_mul, hpow]
  simp only [eval_mul, eval_pow, eval_prod]
  rw [mul_mul_mul_comm, ← mul_pow, ← prod_mul_distrib]
  congr 1
  · congr 1
    simp only [eval_sub, eval_one, eval_pow, eval_X, inv_pow]
    field_simp
  · refine prod_congr rfl fun v _ ↦ ?_
    simp only [map_natCast, eval_add, eval_sub, eval_one, eval_mul, eval_C, eval_X, eval_natCast,
      eval_pow, inv_pow]
    field_simp

end SimpleGraph
