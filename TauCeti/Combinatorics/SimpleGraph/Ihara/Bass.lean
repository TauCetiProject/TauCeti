/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.AdjMatrix
public import TauCeti.Combinatorics.SimpleGraph.Dart.Matrix
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import TauCeti.Algebra.Polynomial.XPow.Regular

/-!
# Bass's three-term determinant formula

Let `G` be a finite simple graph with `n` vertices and `e` edges, adjacency matrix `A` and degree
matrix `D`, and let `S`, `T`, `J` be its dart start, end and reversal matrices. The Hashimoto
(non-backtracking edge) matrix `M` of `G` is characterised by `M + J = Tᵀ S`. Bass's three-term
determinant formula for the Ihara zeta function states, in `R[X]`,

`(1 - X²) ^ n det (1 - X M) = (1 - X²) ^ e det (1 - X A + X² (D - 1))`.

It holds for every finite simple graph, without connectivity or degree hypotheses; this
multiplied form avoids the negative exponent `e - n` of the usual statement for forests. With
`c = 1 - X²`, the incidence identities give `(1 - X J) (1 - X M) = c - P S` for
`P = X (Tᵀ - X Sᵀ)`, Sylvester's identity turns `cⁿ det (c - P S)` into `c^(2e) det (c - S P)`,
and `S P = X A - X² D`. The reversal matrix contributes `det (1 - X J) = cᵉ`, and `c` is regular
in `R[X]`, so it can be cancelled.

## Main results

* `SimpleGraph.bass_determinant_formula_of_add_dartSymmMatrix_eq`: **Bass's three-term formula**
  `(1 - X²) ^ n det (1 - X M) = (1 - X²) ^ e det (1 - X A + X² (D - 1))` for the matrix `M` with
  `M + J = Tᵀ S`, that is, for the Hashimoto matrix.
* `SimpleGraph.charpolyRev_eq_of_add_dartSymmMatrix_eq_of_card_le`: the formula after
  cancellation when `n ≤ e`.
* `SimpleGraph.one_sub_X_sq_pow_mul_charpolyRev_of_add_dartSymmMatrix_eq_of_le_card`: the formula
  after cancellation when `e ≤ n`.

## References

* H. Bass, *The Ihara–Selberg zeta function of a tree lattice*, Internat. J. Math. 3 (1992),
  717–797.
* A. Terras, *A Stroll Through the Garden of Graph Zeta Functions*, draft of 29 December 2009:
  Theorem 1 (the three-term formula), and Bass's proof of it in §11.1 with the incidence
  identities of Proposition 4. The book *Zeta Functions of Graphs: A Stroll through the Garden*
  (Cambridge University Press, 2011) grew from this draft.
-/

public section

open Finset Matrix Polynomial

namespace SimpleGraph

variable {V R : Type*} (G : SimpleGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
  [CommRing R]

/-- Bass's factorization: for `M = Tᵀ S - J` and `c = 1 - t²`,
`(1 - t J) (1 - t M) = c - (t Tᵀ - t² Sᵀ) S`. -/
private theorem one_sub_smul_dartSymmMatrix_mul_one_sub_smul {M : Matrix G.Dart G.Dart R}
    (hM : M + G.dartSymmMatrix R = (G.dartSndMatrix R)ᵀ * G.dartFstMatrix R) (t : R) :
    (1 - t • G.dartSymmMatrix R) * (1 - t • M) =
      scalar G.Dart (1 - t ^ 2) -
        (t • (G.dartSndMatrix R)ᵀ - t ^ 2 • (G.dartFstMatrix R)ᵀ) * G.dartFstMatrix R := by
  rw [eq_sub_of_add_eq hM]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_sub, smul_smul, ← Matrix.mul_assoc,
    dartSymmMatrix_mul_transpose_dartSndMatrix, dartSymmMatrix_mul_self, scalar_apply,
    ← smul_one_eq_diagonal, sub_smul, one_smul, sq]
  abel

/-- Bass's identity before cancellation: for `M` with `M + J = Tᵀ S` and `c = 1 - t²`,
`cⁿ cᵉ det (1 - t M) = c ^ (2e) det (1 - t A + t² (D - 1))`. -/
private theorem bass_identity {M : Matrix G.Dart G.Dart R}
    (hM : M + G.dartSymmMatrix R = (G.dartSndMatrix R)ᵀ * G.dartFstMatrix R) (t : R) :
    (1 - t ^ 2) ^ Fintype.card V * ((1 - t ^ 2) ^ #G.edgeFinset * (1 - t • M).det) =
      (1 - t ^ 2) ^ (2 * #G.edgeFinset) *
        (1 - t • G.adjMatrix R + t ^ 2 • (G.degMatrix R - 1)).det := by
  have hsyl := congrArg (eval (1 - t ^ 2)) (charpoly_mul_comm'
    (t • (G.dartSndMatrix R)ᵀ - t ^ 2 • (G.dartFstMatrix R)ᵀ) (G.dartFstMatrix R))
  simp only [eval_mul, eval_pow, eval_X, eval_charpoly] at hsyl
  rw [← det_one_sub_smul_dartSymmMatrix, ← det_mul, one_sub_smul_dartSymmMatrix_mul_one_sub_smul
    G hM, hsyl, ← dart_card_eq_twice_card_edges]
  congr 2
  simp only [Matrix.mul_sub, Matrix.mul_smul, dartFstMatrix_mul_transpose_dartSndMatrix,
    dartFstMatrix_mul_transpose_dartFstMatrix, scalar_apply, ← smul_one_eq_diagonal, sub_smul,
    one_smul, smul_sub]
  abel

/-- **Bass's three-term determinant formula.** If `M + J = Tᵀ S`, so that `M` is the Hashimoto
(non-backtracking edge) matrix of `G`, then in `R[X]`
`(1 - X²) ^ n det (1 - X M) = (1 - X²) ^ e det (1 - X A + X² (D - 1))`, where `n` is the number of
vertices, `e` the number of edges, `A` the adjacency matrix and `D` the degree matrix of `G`. -/
theorem bass_determinant_formula_of_add_dartSymmMatrix_eq {M : Matrix G.Dart G.Dart R}
    (hM : M + G.dartSymmMatrix R = (G.dartSndMatrix R)ᵀ * G.dartFstMatrix R) :
    (1 - X ^ 2 : R[X]) ^ Fintype.card V * M.charpolyRev =
      (1 - X ^ 2) ^ #G.edgeFinset *
        (1 - (X : R[X]) • G.adjMatrix R[X] + (X ^ 2 : R[X]) • (G.degMatrix R[X] - 1)).det := by
  have hM' : M.map C + G.dartSymmMatrix R[X] =
      (G.dartSndMatrix R[X])ᵀ * G.dartFstMatrix R[X] := by
    have h := congrArg (RingHom.mapMatrix (C : R →+* R[X])) hM
    rw [map_add] at h
    simpa [Matrix.map_mul, transpose_map] using h
  have hc := (isRegular_one_sub_X_pow (R := R) two_ne_zero).pow #G.edgeFinset
  rw [← hc.left.eq_iff]
  rw [mul_left_comm, charpolyRev, bass_identity G hM' X, two_mul, pow_add, mul_assoc]

/-- Bass's formula when the graph has at least as many edges as vertices, for instance when it is
connected and not a tree: `det (1 - X M) = (1 - X²) ^ (e - n) det (1 - X A + X² (D - 1))` for the
matrix `M` with `M + J = Tᵀ S`. -/
theorem charpolyRev_eq_of_add_dartSymmMatrix_eq_of_card_le {M : Matrix G.Dart G.Dart R}
    (hM : M + G.dartSymmMatrix R = (G.dartSndMatrix R)ᵀ * G.dartFstMatrix R)
    (h : Fintype.card V ≤ #G.edgeFinset) :
    M.charpolyRev = (1 - X ^ 2) ^ (#G.edgeFinset - Fintype.card V) *
      (1 - (X : R[X]) • G.adjMatrix R[X] + (X ^ 2 : R[X]) • (G.degMatrix R[X] - 1)).det := by
  have hc := (isRegular_one_sub_X_pow (R := R) two_ne_zero).pow (Fintype.card V)
  rw [← hc.left.eq_iff]
  rw [bass_determinant_formula_of_add_dartSymmMatrix_eq G hM, ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' h]

/-- Bass's formula when the graph has at most as many edges as vertices, for instance when it is a
forest: `(1 - X²) ^ (n - e) det (1 - X M) = det (1 - X A + X² (D - 1))` for the matrix `M` with
`M + J = Tᵀ S`. -/
theorem one_sub_X_sq_pow_mul_charpolyRev_of_add_dartSymmMatrix_eq_of_le_card
    {M : Matrix G.Dart G.Dart R}
    (hM : M + G.dartSymmMatrix R = (G.dartSndMatrix R)ᵀ * G.dartFstMatrix R)
    (h : #G.edgeFinset ≤ Fintype.card V) :
    (1 - X ^ 2 : R[X]) ^ (Fintype.card V - #G.edgeFinset) * M.charpolyRev =
      (1 - (X : R[X]) • G.adjMatrix R[X] + (X ^ 2 : R[X]) • (G.degMatrix R[X] - 1)).det := by
  have hc := (isRegular_one_sub_X_pow (R := R) two_ne_zero).pow #G.edgeFinset
  rw [← hc.left.eq_iff]
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h,
    bass_determinant_formula_of_add_dartSymmMatrix_eq G hM]

end SimpleGraph
