/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.LapMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import TauCeti.LinearAlgebra.Charpoly.Permutation
import TauCeti.LinearAlgebra.Matrix.Charpoly.Reverse

/-!
# Incidence matrices on the darts of a simple graph

For a simple graph `G` on a finite vertex type, this file introduces three `0`–`1` matrices
indexed by the darts (ordered pairs of adjacent vertices) of `G`:

* the start matrix `S = G.dartFstMatrix R : Matrix V G.Dart R`, with `S v a = 1` iff `a` starts
  at `v`;
* the end matrix `T = G.dartSndMatrix R : Matrix V G.Dart R`, with `T v a = 1` iff `a` ends at `v`;
* the reversal matrix `J = G.dartSymmMatrix R : Matrix G.Dart G.Dart R`, with `J a b = 1` iff
  `b` is the reversal of `a`.

They factor the adjacency matrix `A` and the degree matrix `D` of `G`: `S Tᵀ = A`,
`S Sᵀ = T Tᵀ = D`, `S J = T`, `T J = S` and `J² = 1`, while `(Tᵀ S) a b = 1` exactly when `a`
ends where `b` starts. Removing the backtracking steps `J` from `Tᵀ S` gives the Hashimoto
(non-backtracking edge) matrix `B = Tᵀ S - J` of the graph, and these identities are what Bass's
proof of the three-term determinant formula for the Ihara zeta function needs:

`(1 - X²) ^ n det (1 - X B) = (1 - X²) ^ e det (1 - X A + X² (D - 1))`,

with `n` vertices and `e` edges. It holds for every finite simple graph, without connectivity or
degree hypotheses; this multiplied form avoids the negative exponent `e - n` of the usual
statement for forests. With `c = 1 - X²`, the identities give `(1 - X J) (1 - X B) = c - P S` for
`P = X (Tᵀ - X Sᵀ)`, Sylvester's identity turns `cⁿ det (c - P S)` into `c^(2e) det (c - S P)`,
and `S P = X A - X² D`. The reversal matrix contributes `det (1 - X J) = cᵉ`, because `J` swaps
the two darts of each edge.

## Main definitions

* `SimpleGraph.dartFstMatrix`, `SimpleGraph.dartSndMatrix`: the start and end matrices.
* `SimpleGraph.dartSymmMatrix`: the reversal matrix.

## Main results

* `SimpleGraph.dartFstMatrix_mul_transpose_dartSndMatrix`: `S Tᵀ = A`.
* `SimpleGraph.dartFstMatrix_mul_transpose_dartFstMatrix`,
  `SimpleGraph.dartSndMatrix_mul_transpose_dartSndMatrix`: `S Sᵀ = D` and `T Tᵀ = D`.
* `SimpleGraph.dartFstMatrix_mul_dartSymmMatrix`, `SimpleGraph.dartSndMatrix_mul_dartSymmMatrix`:
  `S J = T` and `T J = S`.
* `SimpleGraph.dartSymmMatrix_mul_self`: `J² = 1`.
* `SimpleGraph.transpose_dartSndMatrix_mul_dartFstMatrix_apply`: `(Tᵀ S) a b = 1` iff
  `a.snd = b.fst`.
* `SimpleGraph.dartSymmMatrix_eq_permMatrix`: `J` is the permutation matrix of the reversal.
* `SimpleGraph.charpolyRev_dartSymmMatrix`, `SimpleGraph.det_one_sub_smul_dartSymmMatrix`:
  `det (1 - X J) = (1 - X²) ^ e`, and `det (1 - t J) = (1 - t²) ^ e` for every scalar `t`.
* `SimpleGraph.bass_determinant_formula_of_add_dartSymmMatrix_eq`: **Bass's three-term formula**
  `(1 - X²) ^ n det (1 - X M) = (1 - X²) ^ e det (1 - X A + X² (D - 1))` for the matrix `M` with
  `M + J = Tᵀ S`, that is, for the Hashimoto matrix; its forms after cancellation are
  `SimpleGraph.charpolyRev_eq_of_add_dartSymmMatrix_eq_of_card_le` (when `n ≤ e`) and
  `SimpleGraph.one_sub_X_sq_pow_mul_charpolyRev_of_add_dartSymmMatrix_eq_of_le_card` (when
  `e ≤ n`).

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

variable {V : Type*} (R : Type*) (G : SimpleGraph V) [DecidableEq V]

section Defs

variable [Zero R] [One R]

/-- The start matrix of `G`: the entry at `(v, a)` is `1` when the dart `a` starts at `v`, and
`0` otherwise. -/
def dartFstMatrix : Matrix V G.Dart R := of fun v a => if a.fst = v then 1 else 0

/-- The end matrix of `G`: the entry at `(v, a)` is `1` when the dart `a` ends at `v`, and `0`
otherwise. -/
def dartSndMatrix : Matrix V G.Dart R := of fun v a => if a.snd = v then 1 else 0

/-- The reversal matrix of `G`: the entry at `(a, b)` is `1` when the dart `b` is the reversal of
the dart `a`, and `0` otherwise. -/
def dartSymmMatrix : Matrix G.Dart G.Dart R := of fun a b => if b = a.symm then 1 else 0

variable {R G}

@[simp]
theorem dartFstMatrix_apply (v : V) (a : G.Dart) :
    G.dartFstMatrix R v a = if a.fst = v then 1 else 0 :=
  (rfl)

@[simp]
theorem dartSndMatrix_apply (v : V) (a : G.Dart) :
    G.dartSndMatrix R v a = if a.snd = v then 1 else 0 :=
  (rfl)

@[simp]
theorem dartSymmMatrix_apply (a b : G.Dart) :
    G.dartSymmMatrix R a b = if b = a.symm then 1 else 0 :=
  (rfl)

/-- The reversal matrix has zero diagonal: no dart is its own reversal. -/
theorem dartSymmMatrix_apply_self (a : G.Dart) : G.dartSymmMatrix R a a = 0 := by
  simp [(Dart.symm_ne a).symm]

/-- The entry of the reversal matrix at a dart and its reversal is `1`. -/
theorem dartSymmMatrix_apply_symm (a : G.Dart) : G.dartSymmMatrix R a a.symm = 1 := by
  simp

/-- The reversal matrix is symmetric. -/
@[simp]
theorem transpose_dartSymmMatrix : (G.dartSymmMatrix R)ᵀ = G.dartSymmMatrix R := by
  ext a b
  simp [eq_comm.trans Dart.symm_involutive.eq_iff]

/-- The reversal matrix is the permutation matrix of the reversal of darts. -/
theorem dartSymmMatrix_eq_permMatrix :
    G.dartSymmMatrix R = (Function.Involutive.toPerm _ Dart.symm_involutive).permMatrix R := by
  ext a b
  simp [PEquiv.toMatrix_apply, eq_comm]

end Defs

section Map

variable {R G} {S : Type*} [Zero R] [One R] [Zero S] [One S]

/-- The start matrix is preserved by any map sending `0` to `0` and `1` to `1`. -/
@[simp]
theorem dartFstMatrix_map {F : Type*} [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S]
    (f : F) : (G.dartFstMatrix R).map f = G.dartFstMatrix S := by
  ext v a
  simp [apply_ite f]

/-- The end matrix is preserved by any map sending `0` to `0` and `1` to `1`. -/
@[simp]
theorem dartSndMatrix_map {F : Type*} [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S]
    (f : F) : (G.dartSndMatrix R).map f = G.dartSndMatrix S := by
  ext v a
  simp [apply_ite f]

/-- The reversal matrix is preserved by any map sending `0` to `0` and `1` to `1`. -/
@[simp]
theorem dartSymmMatrix_map {F : Type*} [FunLike F R S] [ZeroHomClass F R S] [OneHomClass F R S]
    (f : F) : (G.dartSymmMatrix R).map f = G.dartSymmMatrix S := by
  ext a b
  simp [apply_ite f]

end Map

section Products

variable [Fintype V]

/-- `(Tᵀ S) a b = 1` exactly when the dart `a` ends where the dart `b` starts. Removing the
reversal matrix from `Tᵀ S` leaves the non-backtracking steps. -/
theorem transpose_dartSndMatrix_mul_dartFstMatrix_apply [NonAssocSemiring R] (a b : G.Dart) :
    ((G.dartSndMatrix R)ᵀ * G.dartFstMatrix R) a b = if a.snd = b.fst then 1 else 0 := by
  simp [Matrix.mul_apply, eq_comm (a := b.fst)]

variable [DecidableRel G.Adj]

section NonAssocSemiring

variable [NonAssocSemiring R]

/-- The start matrix times the transposed end matrix is the adjacency matrix: `S Tᵀ = A`. -/
theorem dartFstMatrix_mul_transpose_dartSndMatrix :
    G.dartFstMatrix R * (G.dartSndMatrix R)ᵀ = G.adjMatrix R := by
  ext u w
  simp only [Matrix.mul_apply, transpose_apply, dartFstMatrix_apply, dartSndMatrix_apply,
    ite_zero_mul_ite_zero, mul_one, sum_boole, adjMatrix_apply]
  split_ifs with h
  · rw [Finset.card_eq_one.2 ⟨⟨(u, w), h⟩, ?_⟩, Nat.cast_one]
    ext a
    simp [Dart.ext_iff, Prod.ext_iff]
  · rw [Finset.card_eq_zero.2 ?_, Nat.cast_zero]
    ext a
    simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
    rintro rfl rfl
    exact h a.adj

/-- The start matrix times its transpose is the degree matrix: `S Sᵀ = D`. -/
theorem dartFstMatrix_mul_transpose_dartFstMatrix :
    G.dartFstMatrix R * (G.dartFstMatrix R)ᵀ = G.degMatrix R := by
  ext u w
  simp only [Matrix.mul_apply, transpose_apply, dartFstMatrix_apply, ite_zero_mul_ite_zero,
    mul_one, sum_boole, degMatrix, diagonal_apply]
  split_ifs with h
  · subst h
    simp [dart_fst_fiber_card_eq_degree]
  · rw [Finset.card_eq_zero.2 ?_, Nat.cast_zero]
    ext a
    simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false, not_and]
    rintro rfl rfl
    exact h rfl

/-- The start matrix times the reversal matrix is the end matrix: `S J = T`. -/
theorem dartFstMatrix_mul_dartSymmMatrix :
    G.dartFstMatrix R * G.dartSymmMatrix R = G.dartSndMatrix R := by
  ext v b
  have (a : G.Dart) : b = a.symm ↔ a = b.symm := eq_comm.trans Dart.symm_involutive.eq_iff
  simp [Matrix.mul_apply, this]

/-- The end matrix times the reversal matrix is the start matrix: `T J = S`. -/
theorem dartSndMatrix_mul_dartSymmMatrix :
    G.dartSndMatrix R * G.dartSymmMatrix R = G.dartFstMatrix R := by
  ext v b
  have (a : G.Dart) : b = a.symm ↔ a = b.symm := eq_comm.trans Dart.symm_involutive.eq_iff
  simp [Matrix.mul_apply, this]

/-- Reversing a dart twice gives it back: `J² = 1`. -/
@[simp]
theorem dartSymmMatrix_mul_self : G.dartSymmMatrix R * G.dartSymmMatrix R = 1 := by
  ext a c
  have (b : G.Dart) : c = b.symm ↔ b = c.symm := eq_comm.trans Dart.symm_involutive.eq_iff
  simp [Matrix.mul_apply, this, Matrix.one_apply, Dart.symm_involutive.injective.eq_iff, eq_comm]

end NonAssocSemiring

section CommSemiring

variable [CommSemiring R]

/-- The reversal matrix times the transposed end matrix is the transposed start matrix:
`J Tᵀ = Sᵀ`. -/
theorem dartSymmMatrix_mul_transpose_dartSndMatrix :
    G.dartSymmMatrix R * (G.dartSndMatrix R)ᵀ = (G.dartFstMatrix R)ᵀ := by
  rw [← dartSndMatrix_mul_dartSymmMatrix, transpose_mul, transpose_dartSymmMatrix]

/-- The end matrix times its transpose is the degree matrix: `T Tᵀ = D`. -/
theorem dartSndMatrix_mul_transpose_dartSndMatrix :
    G.dartSndMatrix R * (G.dartSndMatrix R)ᵀ = G.degMatrix R := by
  rw [← dartFstMatrix_mul_dartSymmMatrix, transpose_mul, transpose_dartSymmMatrix, Matrix.mul_assoc,
    ← Matrix.mul_assoc (G.dartSymmMatrix R), dartSymmMatrix_mul_self, Matrix.one_mul,
    dartFstMatrix_mul_transpose_dartFstMatrix]

end CommSemiring

end Products

section Det

variable {R} [Fintype V] [DecidableRel G.Adj] [CommRing R]

/-- **`det (1 - X J)`.** The reversal of darts is a fixed-point-free involution, made of one
transposition for each edge, so `det (1 - X J) = (1 - X²) ^ e` for `e` the number of edges. -/
theorem charpolyRev_dartSymmMatrix :
    (G.dartSymmMatrix R).charpolyRev = (1 - X ^ 2) ^ #G.edgeFinset := by
  set σ := Function.Involutive.toPerm _ (Dart.symm_involutive (G := G))
  have hσ : σ⁻¹ = σ := Function.Involutive.toPerm_symm _
  have hsupp : σ.support = univ := by
    ext d
    simpa [σ] using Dart.symm_ne d
  have hcyc : σ.cycleType = Multiset.replicate σ.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one (Equiv.ext fun d => by simp [σ, sq])
  have hcard : σ.cycleType.card = #G.edgeFinset := by
    have h := σ.sum_cycleType
    rw [hcyc, Multiset.sum_replicate, hsupp, card_univ, dart_card_eq_twice_card_edges,
      smul_eq_mul] at h
    omega
  have hJ : G.dartSymmMatrix R = permMatrixHom σ := by
    rw [permMatrixHom_apply, hσ]
    exact dartSymmMatrix_eq_permMatrix
  rw [hJ, charpolyRev_permMatrixHom,
    Equiv.Perm.fullCycleType_eq_cycleType hsupp, hcyc, hcard,
    Multiset.map_replicate, Multiset.prod_replicate]

/-- **The determinant of `1 - t J`.** The reversal matrix swaps the two darts of each edge, so
`det (1 - t J) = (1 - t²) ^ e` for `e` the number of edges. -/
theorem det_one_sub_smul_dartSymmMatrix (t : R) :
    (1 - t • G.dartSymmMatrix R).det = (1 - t ^ 2) ^ #G.edgeFinset := by
  rw [← eval_charpolyRev_eq_det_one_sub_smul, charpolyRev_dartSymmMatrix]
  simp

end Det

section Bass

variable {R} [Fintype V] [DecidableRel G.Adj] [CommRing R]

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

/-- `1 - X²` is not a zero divisor in `R[X]`: it is minus the monic polynomial `X² - 1`. -/
private theorem isRegular_one_sub_X_sq : IsRegular (1 - X ^ 2 : R[X]) := by
  rw [show (1 - X ^ 2 : R[X]) = -1 * (X ^ 2 - C 1) by simp]
  exact isUnit_one.neg.isRegular.mul (monic_X_pow_sub_C 1 two_ne_zero).isRegular

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
  have hc := (isRegular_one_sub_X_sq (R := R)).pow #G.edgeFinset
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
  have hc := (isRegular_one_sub_X_sq (R := R)).pow (Fintype.card V)
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
  have hc := (isRegular_one_sub_X_sq (R := R)).pow #G.edgeFinset
  rw [← hc.left.eq_iff]
  rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' h,
    bass_determinant_formula_of_add_dartSymmMatrix_eq G hM]

end Bass

end SimpleGraph
