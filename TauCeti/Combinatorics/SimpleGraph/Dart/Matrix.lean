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
import TauCeti.Combinatorics.SimpleGraph.Dart.Basic
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

They factor the adjacency matrix `A` and the degree matrix `D` of `G`: `S Tᵀ = T Sᵀ = A`,
`S Sᵀ = T Tᵀ = D`, `S J = T`, `T J = S`, `J Tᵀ = Sᵀ` and `J² = 1`, while `(Tᵀ S) a b = 1` exactly
when `a` ends where `b` starts. Removing the backtracking steps `J` from `Tᵀ S` gives the Hashimoto
(non-backtracking edge) matrix `B = Tᵀ S - J` of the graph. The reversal matrix swaps the two
darts of each edge, so `det (1 - X J) = (1 - X²) ^ e` for `e` the number of edges. These are the
ingredients of Bass's proof of the three-term determinant formula for the Ihara zeta function.

## Main definitions

* `SimpleGraph.dartFstMatrix`, `SimpleGraph.dartSndMatrix`: the start and end matrices.
* `SimpleGraph.dartSymmMatrix`: the reversal matrix.

## Main results

* `SimpleGraph.dartFstMatrix_mul_transpose_dartSndMatrix`,
  `SimpleGraph.dartSndMatrix_mul_transpose_dartFstMatrix`: `S Tᵀ = A` and `T Sᵀ = A`.
* `SimpleGraph.dartFstMatrix_mul_transpose_dartFstMatrix`,
  `SimpleGraph.dartSndMatrix_mul_transpose_dartSndMatrix`: `S Sᵀ = D` and `T Tᵀ = D`.
* `SimpleGraph.dartFstMatrix_mul_dartSymmMatrix`, `SimpleGraph.dartSndMatrix_mul_dartSymmMatrix`:
  `S J = T` and `T J = S`.
* `SimpleGraph.dartSymmMatrix_mul_self`: `J² = 1`.
* `SimpleGraph.dartSymmMatrix_mul_transpose_dartSndMatrix`,
  `SimpleGraph.dartSymmMatrix_mul_transpose_dartFstMatrix`: `J Tᵀ = Sᵀ` and `J Sᵀ = Tᵀ`.
* `SimpleGraph.transpose_dartSndMatrix_mul_dartFstMatrix_apply`: `(Tᵀ S) a b = 1` iff
  `a.snd = b.fst`.
* `SimpleGraph.dartSymmMatrix_eq_permMatrix`: `J` is the permutation matrix of the reversal.
* `SimpleGraph.charpolyRev_dartSymmMatrix`, `SimpleGraph.det_one_sub_smul_dartSymmMatrix`:
  `det (1 - X J) = (1 - X²) ^ e`, and `det (1 - t J) = (1 - t²) ^ e` for every scalar `t`.

## References

* A. Terras, *A Stroll Through the Garden of Graph Zeta Functions*, draft of 29 December 2009:
  the incidence identities of Proposition 4 in §11.1. The book *Zeta Functions of Graphs: A Stroll
  through the Garden* (Cambridge University Press, 2011) grew from this draft.
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
  simp

/-- The entry of the reversal matrix at a dart and its reversal is `1`. -/
theorem dartSymmMatrix_apply_symm (a : G.Dart) : G.dartSymmMatrix R a a.symm = 1 := by
  simp

/-- The reversal matrix is symmetric. -/
@[simp]
theorem transpose_dartSymmMatrix : (G.dartSymmMatrix R)ᵀ = G.dartSymmMatrix R := by
  ext a b
  simp [Dart.eq_symm_comm]

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
@[simp]
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
@[simp]
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
@[simp]
theorem dartFstMatrix_mul_dartSymmMatrix :
    G.dartFstMatrix R * G.dartSymmMatrix R = G.dartSndMatrix R := by
  ext v b
  simp [Matrix.mul_apply, Dart.eq_symm_comm]

/-- The end matrix times the reversal matrix is the start matrix: `T J = S`. -/
@[simp]
theorem dartSndMatrix_mul_dartSymmMatrix :
    G.dartSndMatrix R * G.dartSymmMatrix R = G.dartFstMatrix R := by
  ext v b
  simp [Matrix.mul_apply, Dart.eq_symm_comm]

/-- Reversing a dart twice gives it back: `J² = 1`. -/
@[simp]
theorem dartSymmMatrix_mul_self : G.dartSymmMatrix R * G.dartSymmMatrix R = 1 := by
  ext a c
  simp [Matrix.mul_apply, Dart.eq_symm_comm, Matrix.one_apply,
    Dart.symm_involutive.injective.eq_iff, eq_comm]

/-- The reversal matrix times the transposed end matrix is the transposed start matrix:
`J Tᵀ = Sᵀ`. -/
@[simp]
theorem dartSymmMatrix_mul_transpose_dartSndMatrix :
    G.dartSymmMatrix R * (G.dartSndMatrix R)ᵀ = (G.dartFstMatrix R)ᵀ := by
  ext a v
  rw [Matrix.mul_apply, Fintype.sum_eq_single a.symm fun b hb => by simp [hb]]
  simp

/-- The reversal matrix times the transposed start matrix is the transposed end matrix:
`J Sᵀ = Tᵀ`. -/
@[simp]
theorem dartSymmMatrix_mul_transpose_dartFstMatrix :
    G.dartSymmMatrix R * (G.dartFstMatrix R)ᵀ = (G.dartSndMatrix R)ᵀ := by
  ext a v
  rw [Matrix.mul_apply, Fintype.sum_eq_single a.symm fun b hb => by simp [hb]]
  simp

/-- The end matrix times its transpose is the degree matrix: `T Tᵀ = D`. -/
@[simp]
theorem dartSndMatrix_mul_transpose_dartSndMatrix :
    G.dartSndMatrix R * (G.dartSndMatrix R)ᵀ = G.degMatrix R := by
  rw [← dartFstMatrix_mul_transpose_dartFstMatrix]
  ext u w
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ Dart.symm_involutive)
    (fun a => G.dartSndMatrix R u a * (G.dartSndMatrix R)ᵀ a w)
    (fun a => G.dartFstMatrix R u a * (G.dartFstMatrix R)ᵀ a w) fun a => by simp

/-- The end matrix times the transposed start matrix is the adjacency matrix: `T Sᵀ = A`. -/
@[simp]
theorem dartSndMatrix_mul_transpose_dartFstMatrix :
    G.dartSndMatrix R * (G.dartFstMatrix R)ᵀ = G.adjMatrix R := by
  rw [← dartFstMatrix_mul_transpose_dartSndMatrix]
  ext u w
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact Fintype.sum_equiv (Function.Involutive.toPerm _ Dart.symm_involutive)
    (fun a => G.dartSndMatrix R u a * (G.dartFstMatrix R)ᵀ a w)
    (fun a => G.dartFstMatrix R u a * (G.dartSndMatrix R)ᵀ a w) fun a => by simp

end NonAssocSemiring

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

end SimpleGraph
