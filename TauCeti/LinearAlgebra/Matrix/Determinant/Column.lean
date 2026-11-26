/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.List.ProdOfFn
import TauCeti.GroupTheory.Perm.Basic

/-!
# The column determinant over a noncommutative ring

`Matrix.columnDet` is the signed Leibniz sum with factors multiplied in increasing column order.
Without commutativity the order matters: in the first-column expansion the selected entry is
on the left, and in the last-column expansion it is on the right. Both formulas apply without
relations among the entries. The construction is alternating in rows, but not in columns in
general. It recovers `Matrix.det` over a commutative ring.

See A. Chervov, G. Falqui and V. Rubtsov, *Algebraic properties of Manin matrices I*, §3.1.
-/

public section

open Equiv Equiv.Perm

namespace Matrix

variable {R : Type*} [Ring R] {n : ℕ}

/-- The signed Leibniz sum in which each product is taken in increasing column order: the
alternatization, in the rows, of the ordered product of the diagonal entries. -/
def columnDet (A : Matrix (Fin n) (Fin n) R) : R :=
  ((MultilinearMap.mkPiAlgebraFin ℤ n R).compLinearMap
    fun j => LinearMap.proj (R := ℤ) (φ := fun _ : Fin n => R) j).alternatization (of.symm A)

/-- The Leibniz formula for the column determinant, with the product taken in list order. -/
theorem columnDet_apply (A : Matrix (Fin n) (Fin n) R) :
    A.columnDet = ∑ σ : Perm (Fin n), sign σ • (List.ofFn fun j => A (σ j) j).prod := by
  rw [columnDet, MultilinearMap.alternatization_apply]
  simp [MultilinearMap.mkPiAlgebraFin_apply]

/-- The empty column determinant is one. -/
@[simp] theorem columnDet_fin_zero (A : Matrix (Fin 0) (Fin 0) R) : A.columnDet = 1 := by
  simp [columnDet_apply]

/-- Permuting rows multiplies the column determinant by the sign of the permutation. -/
@[simp] theorem columnDet_submatrix_left (A : Matrix (Fin n) (Fin n) R) (e : Perm (Fin n)) :
    (A.submatrix e id).columnDet = sign e • A.columnDet :=
  AlternatingMap.map_perm _ A e

/-- The column determinant vanishes when two distinct rows agree. -/
theorem columnDet_eq_zero_of_row_eq (A : Matrix (Fin n) (Fin n) R) {i j : Fin n}
    (hij : i ≠ j) (h : A i = A j) : A.columnDet = 0 :=
  AlternatingMap.map_eq_zero_of_eq _ A h hij

/-- For matrices agreeing off two adjacent columns, comparing the ordered two-row minors in
those columns suffices to compare the column determinants, with the same integer multiplier. -/
theorem columnDet_eq_zsmul_of_adjacent (A B : Matrix (Fin n) (Fin n) R) (c : ℤ)
    {i j : Fin n} (hij : i.val + 1 = j.val)
    (hcols : ∀ r k, k ≠ i → k ≠ j → A r k = B r k)
    (hpair : ∀ r s, r ≠ s → A r i * A s j - A s i * A r j =
      c • (B r i * B s j - B s i * B r j)) : A.columnDet = c • B.columnDet := by
  rw [columnDet_apply, columnDet_apply, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  simp_rw [smul_comm c, ← smul_sub]
  refine TauCeti.sum_sign_smul_eq_zero_of_mul_swap _ i j (by simp [Fin.ext_iff]; omega) ?_
  intro σ
  let a (τ : Perm (Fin n)) (k : Fin n) := A (τ k) k
  let b (τ : Perm (Fin n)) (k : Fin n) := B (τ k) k
  let τ := σ * swap i j
  have hfix k (hi : k ≠ i) (hj : k ≠ j) : τ k = σ k := by
    simp [τ, Equiv.swap_apply_of_ne_of_ne hi hj]
  have hB k hi hj : b σ k = a σ k := (hcols _ _ hi hj).symm
  -- Split every product at the adjacent columns, with the same outer factors from `a σ`.
  have hsplit (f : Fin n → R) (hf : ∀ k, k ≠ i → k ≠ j → f k = a σ k) :=
    List.prod_ofFn_eq_take_mul_mul_drop_of_eq f (a σ) hij hf
  rw [hsplit (a τ) (fun k hi hj ↦ by simp [a, hfix k hi hj]),
    hsplit (b τ) (fun k hi hj ↦ by simpa [b, hfix k hi hj] using hB k hi hj),
    hsplit (a σ) (fun _ _ _ ↦ rfl), hsplit (b σ) hB]
  have hmiddle : A (σ j) i * A (σ i) j - c • (B (σ j) i * B (σ i) j) =
      A (σ i) i * A (σ j) j - c • (B (σ i) i * B (σ j) j) := by
    have h := hpair (σ i) (σ j) (σ.injective.ne (by simp [Fin.ext_iff]; omega))
    rw [smul_sub] at h
    linear_combination (norm := abel) h.symm
  simpa only [a, b, τ, Equiv.Perm.mul_apply, swap_apply_left, swap_apply_right,
    mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc] using
    congrArg (fun x ↦ ((List.ofFn (a σ)).take i).prod * x *
      ((List.ofFn (a σ)).drop (j + 1)).prod) hmiddle

/-- Expanding along the first column puts the selected entry on the left of its minor. -/
theorem columnDet_succ_column_zero (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.columnDet = ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (A i 0 * (A.submatrix i.succAbove Fin.succ).columnDet) := by
  have h := TauCeti.sum_sign_smul_comp_eq_sum_cons_removeNth
    (fun u : Fin (n + 1) → Fin (n + 1) => (List.ofFn fun j => A (u j) j).prod) id
  simp only [Function.id_comp] at h
  rw [columnDet_apply, h]
  simp only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons,
    columnDet_apply, Fin.removeNth, submatrix_apply, Function.comp_apply, id_eq,
    Finset.mul_sum, Units.smul_def, mul_smul_comm]

/-- Expanding along the last column puts the selected entry on the right of its minor. -/
theorem columnDet_succ_column_last (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    A.columnDet = ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
      ((A.submatrix i.succAbove Fin.castSucc).columnDet * A i (Fin.last n)) := by
  have h := TauCeti.sum_sign_smul_comp_eq_sum_insertNth_removeNth
    (fun u : Fin (n + 1) → Fin (n + 1) => (List.ofFn fun j => A (u j) j).prod) id (Fin.last n)
  simp only [Fin.val_last, Function.id_comp] at h
  rw [columnDet_apply, h]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul]
  have hsign : (-1 : ℤ) ^ n * (-1 : ℤ) ^ i.val = (-1 : ℤ) ^ (n - i.val) := by
    have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hcast : ((n - i.val : ℕ) : ℤ) = (n : ℤ) - i.val := Nat.cast_sub hi
    simp only [← Int.coe_negOnePow_natCast, ← Units.val_mul, ← Int.negOnePow_sub, hcast]
  rw [hsign]
  simp only [List.ofFn_succ', List.prod_concat, Fin.insertNth_last', Fin.snoc_castSucc,
    Fin.snoc_last, columnDet_apply, Fin.removeNth, id_eq,
    submatrix_apply, Function.comp_apply, Finset.sum_mul, Units.smul_def, smul_mul_assoc]

/-- If the strictly upper entries kill a vector and each diagonal entry acts on it by a
scalar, the column determinant acts on it by the product of the diagonal scalars. -/
theorem columnDet_smul_of_upper_smul_eq_zero {S M : Type*} [CommMonoid S]
    [AddCommGroup M] [Module R M] [MulAction S M] [SMulCommClass R S M]
    (A : Matrix (Fin n) (Fin n) R) (v : M) (c : Fin n → S)
    (hupper : ∀ i j, i < j → A i j • v = 0) (hdiag : ∀ i, A i i • v = c i • v) :
    A.columnDet • v = (∏ i, c i) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- On `v`, only the bottom entry of the last column contributes.
    rw [columnDet_succ_column_last, Finset.sum_smul, Finset.sum_eq_single (Fin.last n)]
    · simp only [Fin.val_last, Nat.sub_self, pow_zero, one_smul, Fin.succAbove_last,
        mul_smul, hdiag]
      have hprefix := ih (A.submatrix Fin.castSucc Fin.castSucc) (c ∘ Fin.castSucc)
        (fun i j hij => hupper i.castSucc j.castSucc (Fin.castSucc_lt_castSucc_iff.mpr hij))
        (fun i => hdiag i.castSucc)
      rw [smul_comm, hprefix, ← mul_smul, Fin.prod_univ_castSucc]
      simp only [Function.comp_apply, mul_comm]
    · intro i _ hi
      rw [smul_assoc, mul_smul, hupper i _ (Fin.lt_last_iff_ne_last.mpr hi), smul_zero,
        smul_zero]
    · simp

/-- In size one the column determinant is the unique entry. -/
@[simp] theorem columnDet_fin_one (A : Matrix (Fin 1) (Fin 1) R) : A.columnDet = A 0 0 := by
  simp [columnDet_succ_column_zero]

/-- Over a commutative ring the ordered Leibniz formula computes the ordinary determinant. -/
@[simp] theorem columnDet_eq_det {S : Type*} [CommRing S] (A : Matrix (Fin n) (Fin n) S) :
    A.columnDet = A.det := by
  simp only [columnDet_apply, det_apply, List.prod_ofFn]

end Matrix
