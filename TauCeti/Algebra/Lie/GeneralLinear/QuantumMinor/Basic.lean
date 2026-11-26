/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

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

end Matrix
