/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Dart.Matrix
public import TauCeti.Combinatorics.SimpleGraph.Hashimoto

/-!
# Singular values of the Hashimoto matrix

For a finite simple graph, write `B` for its Hashimoto matrix, `S` for the start incidence
matrix and `D` for the diagonal degree matrix. Then `Bᵀ B = 1 + Sᵀ (D - 2) S`. The
characteristic polynomial of `Bᵀ B`, multiplied by `(X - 1) ^ |V|`, factors into
`(X - 1) ^ |Dart|` and one factor `X - (deg v - 1)²` per vertex. An isolated vertex contributes
a factor of `X - 1` on each side.

The rectangular characteristic polynomial identity moves the product from the dart index type
to the vertex index type. There it uses `S Sᵀ = D` and `1 + D (D - 2) = (D - 1)²`.

Over the reals this gives Horton's singular-value formula. Each nonisolated vertex contributes
a singular value `deg v - 1`, and the remaining `|Dart| - n₊` singular values are `1`,
where `n₊` is the number of nonisolated vertices.

## References

* A. Terras, *Zeta Functions of Graphs: A Stroll through the Garden*, Cambridge University
  Press, 2010, Theorem 11.10(2), which credits M. D. Horton.
-/

public section

open Finset Matrix Polynomial

namespace SimpleGraph

variable {V R : Type*} (G : SimpleGraph V) [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
  [CommRing R]

/-- The Gram matrix of the columns of the Hashimoto matrix is `1 + Sᵀ (D - 2) S`, where
`S` is the start incidence matrix and `D` is the diagonal degree matrix. -/
theorem transpose_mul_hashimotoMatrix :
    (G.hashimotoMatrix R)ᵀ * G.hashimotoMatrix R =
      1 + (G.dartFstMatrix R)ᵀ * (G.degMatrix R - 2) * G.dartFstMatrix R := by
  have hB : G.hashimotoMatrix R + G.dartSymmMatrix R =
      (G.dartSndMatrix R)ᵀ * G.dartFstMatrix R := by
    ext a b
    rw [Matrix.add_apply, hashimotoMatrix_apply, dartSymmMatrix_apply,
      transpose_dartSndMatrix_mul_dartFstMatrix_apply]
    by_cases h : b = a.symm
    · subst b
      simp
    · simp [h]
  rw [eq_sub_of_add_eq hB, transpose_sub, transpose_mul, transpose_transpose,
    transpose_dartSymmMatrix]
  calc
    _ = (G.dartFstMatrix R)ᵀ * (G.dartSndMatrix R * (G.dartSndMatrix R)ᵀ) *
          G.dartFstMatrix R -
        (G.dartFstMatrix R)ᵀ * (G.dartSndMatrix R * G.dartSymmMatrix R) -
        (G.dartSymmMatrix R * (G.dartSndMatrix R)ᵀ) * G.dartFstMatrix R +
        G.dartSymmMatrix R * G.dartSymmMatrix R := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
          abel
    _ = _ := by
      rw [dartSndMatrix_mul_transpose_dartSndMatrix, dartSndMatrix_mul_dartSymmMatrix,
        dartSymmMatrix_mul_transpose_dartSndMatrix, dartSymmMatrix_mul_self, ← one_add_one_eq_two]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one]
      abel

/-- Horton's formula for the characteristic polynomial of `Bᵀ B`, where `B` is the Hashimoto
matrix. The factor `(X - 1) ^ |V|` keeps the identity valid for graphs with isolated vertices. -/
theorem charpoly_transpose_mul_hashimotoMatrix :
    (X - 1 : R[X]) ^ Fintype.card V *
        ((G.hashimotoMatrix R)ᵀ * G.hashimotoMatrix R).charpoly =
      (X - 1) ^ Fintype.card G.Dart * ∏ v, (X - C (((G.degree v : R) - 1) ^ 2)) := by
  let S := G.dartFstMatrix R
  let D := G.degMatrix R
  have h := congrArg (fun p : R[X] ↦ p.comp (X + C (-1)))
    (Matrix.charpoly_mul_comm' (Sᵀ * (D - 2)) S)
  simp only [mul_comp, pow_comp, X_comp] at h
  rw [← Matrix.charpoly_sub_scalar, ← Matrix.charpoly_sub_scalar] at h
  have hD : S * (Sᵀ * (D - 2)) - scalar V (-1) =
      diagonal (fun v ↦ ((G.degree v : R) - 1) ^ 2) := by
    rw [← Matrix.mul_assoc, dartFstMatrix_mul_transpose_dartFstMatrix, map_neg, map_one,
      sub_neg_eq_add]
    have hsq : D * (D - 2) + 1 = (D - 1) ^ 2 := by noncomm_ring
    rw [hsq]
    simp only [D, degMatrix, ← diagonal_one (n := V) (α := R), diagonal_sub,
      pow_two, diagonal_mul_diagonal]
  rw [hD, charpoly_diagonal] at h
  rw [transpose_mul_hashimotoMatrix, add_comm]
  simpa only [C_neg, C_1, ← sub_eq_add_neg, map_neg, map_one, sub_neg_eq_add, S, D] using h

/-- The squares of the singular values of the Hashimoto matrix over the reals are
`(deg v - 1)²` for the nonisolated vertices, together with `|Dart| - n₊` copies of `1`,
where `n₊` is the number of nonisolated vertices. The characteristic polynomial identity
holds over any commutative ring. -/
theorem charpoly_transpose_mul_hashimotoMatrix_eq_prod :
    ((G.hashimotoMatrix R)ᵀ * G.hashimotoMatrix R).charpoly =
      (X - 1 : R[X]) ^ (Fintype.card G.Dart - #{v | 0 < G.degree v}) *
        ∏ v ∈ univ with 0 < G.degree v, (X - C (((G.degree v : R) - 1) ^ 2)) := by
  let pos : Finset V := univ.filter fun v ↦ 0 < G.degree v
  let iso : Finset V := univ.filter fun v ↦ ¬0 < G.degree v
  have hcard : #pos + #iso = Fintype.card V := by
    simpa only [pos, iso, card_univ] using
      (card_filter_add_card_filter_not (s := (univ : Finset V)) (p := fun v ↦ 0 < G.degree v))
  have hle : #pos ≤ Fintype.card G.Dart := by
    rw [G.dart_card_eq_sum_degrees]
    calc
      #pos = ∑ _v ∈ pos, 1 := by simp
      _ ≤ ∑ v ∈ pos, G.degree v := sum_le_sum fun v hv ↦ (mem_filter.mp hv).2
      _ ≤ _ := sum_le_sum_of_subset (filter_subset _ _)
  have hiso : (∏ v ∈ iso, (X - C (((G.degree v : R) - 1) ^ 2))) = (X - 1) ^ #iso := by
    rw [← prod_const]
    refine prod_congr rfl fun v hv ↦ ?_
    simp [Nat.eq_zero_of_not_pos (mem_filter.mp hv).2]
  have h := G.charpoly_transpose_mul_hashimotoMatrix (R := R)
  rw [← prod_filter_mul_prod_filter_not univ (fun v ↦ 0 < G.degree v), hiso] at h
  have hmonic : (X - 1 : R[X]).Monic := by simpa using monic_X_sub_C (1 : R)
  apply (hmonic.pow (Fintype.card V)).isRegular.left.eq_iff.mp
  refine h.trans ?_
  conv_lhs => rw [← Nat.add_sub_cancel' hle, pow_add]
  rw [← hcard, pow_add]
  ac_rfl

end SimpleGraph
