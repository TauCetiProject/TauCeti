/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import TauCeti.LinearAlgebra.Matrix.Determinant.Column

/-!
# Quantum minors with descending spectral shifts

For a matrix of generators `E`, the quantum minor on the row tuple `a` and column tuple `b`
is a column determinant. Its column `j` is taken from `T(u - j)`, where
`T(v)ᵢⱼ = Eᵢⱼ + δᵢⱼ v`. Tuples may repeat indices. Row alternation and the first- and
last-column Laplace expansions use only the ordered Leibniz formula, not the commutation
relations of the generators. The first column deletion lowers the starting parameter by one;
the last column deletion leaves it unchanged.

For quantum minors, see A. Molev, M. Nazarov and G. Olshanski, *Yangians and classical Lie
algebras*, §2. The expansion conventions are those of L. Alpöge's formalization of the
Riemann hypothesis for Dirichlet L-functions (`Formalism.FourierDecayAlt.Q.ExpFirstCol`).
-/

public section

namespace Matrix

open Equiv Equiv.Perm

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

/-- The column-ordered quantum minor with rows `a`, columns `b` and spectral parameter `u`.
In a nonempty minor the first factor in each Leibniz term uses `u`, and the last uses
`u - (n - 1)`. -/
def quantumMinor (E : Matrix ι ι A) (u : K) (a b : Fin n → ι) : A :=
  (of fun i j => (if a i = b j then algebraMap K A (u - (j.val : K)) else 0) +
    E (a i) (b j)).columnDet

/-- A quantum minor is the column determinant of the matrix of shifted entries. -/
theorem quantumMinor_eq_columnDet (E : Matrix ι ι A) (u : K) (a b : Fin n → ι) :
    E.quantumMinor u a b =
      (of fun i j => (if a i = b j then algebraMap K A (u - (j.val : K)) else 0) +
        E (a i) (b j)).columnDet :=
  (rfl)

/-- Algebra homomorphisms preserve quantum minors with the same spectral parameter. -/
@[simp] theorem _root_.AlgHom.map_quantumMinor {B : Type*} [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) (E : Matrix ι ι A) (u : K) (a b : Fin n → ι) :
    f (E.quantumMinor u a b) = (E.map f).quantumMinor u a b := by
  simp only [quantumMinor_eq_columnDet, ← AlgHom.coe_toRingHom, RingHom.map_columnDet]
  congr 1
  ext i j
  simp only [AlgHom.coe_toRingHom, Matrix.map_apply, of_apply, map_add, apply_ite f,
    AlgHom.commutes, map_zero]

/-- A constant scalar diagonal shift adds that scalar to the spectral parameter of every
quantum minor, without any commutator hypothesis on the generators. -/
@[simp] theorem quantumMinor_add_diagonal_algebraMap (E : Matrix ι ι A) (u t : K)
    (a b : Fin n → ι) :
    (E + diagonal (fun _ ↦ algebraMap K A t)).quantumMinor u a b =
      E.quantumMinor (u + t) a b := by
  simp only [quantumMinor_eq_columnDet]
  congr 1
  ext i j
  by_cases h : a i = b j
  · simp only [of_apply, Matrix.add_apply, h, diagonal_apply_eq, ↓reduceIte]
    have hs : (u - (j.val : K)) + t = u + t - j.val := by abel
    rw [← add_assoc, add_right_comm, ← map_add, hs]
  · simp [h]

/-- An element commuting with the entries in the selected rows and columns also commutes with
the quantum minor. -/
theorem commute_quantumMinor (E : Matrix ι ι A) (u : K) (a b : Fin n → ι) {x : A}
    (h : ∀ i j, Commute (E (a i) (b j)) x) : Commute (E.quantumMinor u a b) x := by
  rw [quantumMinor_eq_columnDet]
  apply commute_columnDet
  intro i j
  simp only [of_apply]
  refine Commute.add_left ?_ (h i j)
  split_ifs
  · exact Algebra.commutes _ _
  · exact Commute.zero_left _

/-- The empty quantum minor is one. -/
@[simp] theorem quantumMinor_fin_zero (E : Matrix ι ι A) (u : K) (a b : Fin 0 → ι) :
    E.quantumMinor u a b = 1 := by
  rw [quantumMinor_eq_columnDet, columnDet_fin_zero]

/-- A quantum minor of size one is the corresponding entry with unshifted parameter. -/
@[simp] theorem quantumMinor_fin_one (E : Matrix ι ι A) (u : K) (a b : Fin 1 → ι) :
    E.quantumMinor u a b = (if a 0 = b 0 then algebraMap K A u else 0) + E (a 0) (b 0) := by
  simp [quantumMinor_eq_columnDet]

/-- Reordering the row tuple multiplies the quantum minor by the sign of the permutation. -/
@[simp] theorem quantumMinor_comp_perm_left (E : Matrix ι ι A) (u : K) (a b : Fin n → ι)
    (e : Perm (Fin n)) : E.quantumMinor u (a ∘ e) b = sign e • E.quantumMinor u a b := by
  simp only [quantumMinor_eq_columnDet, ← columnDet_submatrix_left]
  congr 1

/-- Inserting a row at position `i` multiplies the minor with that row first by
`(-1)^i`. -/
theorem quantumMinor_insertNth_left (E : Matrix ι ι A) (u : K) (a : Fin n → ι)
    (b : Fin (n + 1) → ι) (i : Fin (n + 1)) (r : ι) :
    E.quantumMinor u (i.insertNth r a) b =
      (-1 : ℤ) ^ i.val • E.quantumMinor u (Fin.cons r a) b := by
  simp only [← Fin.cons_comp_cycleRange, quantumMinor_comp_perm_left, Fin.sign_cycleRange,
    Units.smul_def, Units.val_pow_eq_pow_val, Units.coe_neg_one]

/-- A quantum minor with a repeated row index vanishes. -/
theorem quantumMinor_eq_zero_of_not_injective_left (E : Matrix ι ι A) (u : K) (a b : Fin n → ι)
    (h : ¬ Function.Injective a) : E.quantumMinor u a b = 0 := by
  obtain ⟨i, j, ha, hij⟩ := Function.not_injective_iff.mp h
  rw [quantumMinor_eq_columnDet]
  apply columnDet_eq_zero_of_row_eq _ hij
  funext l
  simp [ha]

/-- Expand a quantum minor in its first column. The selected entry multiplies on the left, and
all cofactors start at spectral parameter `u - 1`. -/
theorem quantumMinor_succ_column_zero (E : Matrix ι ι A) (u : K) (a b : Fin (n + 1) → ι) :
    E.quantumMinor u a b = ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (((if a i = b 0 then algebraMap K A u else 0) + E (a i) (b 0)) *
        E.quantumMinor (u - 1) (i.removeNth a) (Fin.tail b)) := by
  simp only [quantumMinor_eq_columnDet, columnDet_succ_column_zero, of_apply, Fin.val_zero,
    Nat.cast_zero, sub_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 3
  ext x y
  have hshift : u - ((y.succ).val : K) = u - 1 - (y.val : K) := by
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one]
    ring
  by_cases h : a (i.succAbove x) = b y.succ <;>
    simp only [submatrix_apply, of_apply, Fin.removeNth, Fin.tail, hshift,
      h, ite_true, ite_false]

/-- Expand a quantum minor in its last column. The selected entry multiplies on the right, and
all cofactors retain the starting spectral parameter. -/
theorem quantumMinor_succ_column_last (E : Matrix ι ι A) (u : K) (a b : Fin (n + 1) → ι) :
    E.quantumMinor u a b = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
      (E.quantumMinor u (i.removeNth a) (Fin.init b) *
        ((if a i = b (Fin.last n) then algebraMap K A (u - (n : K)) else 0) +
          E (a i) (b (Fin.last n)))) := by
  simp only [quantumMinor_eq_columnDet, columnDet_succ_column_last, of_apply, Fin.val_last]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 3

/-- A quantum minor lies in any subalgebra containing the entries selected by its row and
column tuples. -/
theorem quantumMinor_mem_subalgebra (E : Matrix ι ι A) (u : K) (a b : Fin n → ι)
    {S : Subalgebra K A} (hS : ∀ i j, E (a i) (b j) ∈ S) : E.quantumMinor u a b ∈ S := by
  rw [quantumMinor_eq_columnDet, columnDet_apply]
  refine S.sum_mem fun σ _ ↦ ?_
  rw [Units.smul_def]
  refine S.zsmul_mem (list_prod_mem fun x hx ↦ ?_) _
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
  simp only [of_apply]
  refine S.add_mem ?_ (hS _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

end Matrix
