/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Basic
import TauCeti.Data.Fin.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Moving a covector border across a quantum minor

An unshifted covector column can pass each adjacent shifted column in an ordered quantum
minor, at the cost of the transposition sign. The first- and last-column expansions then
identify the two signed cofactor contractions, with a shift of one in the spectral parameter.
This is the covector movement identity of L. Alpöge (`PI.MoveCov`); it needs only the mixed
commutators with the border, not any commutation relations among the original entries or
among the covector components.
-/

public section

namespace Matrix

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

/-- Insert the unshifted covector at `k`. The ordinary columns use the shifts of their positions
in the enlarged matrix. -/
private def covectorBorder (E : Matrix ι ι A) (u : K) (a : Fin (n + 1) → ι) (b : Fin n → ι)
    (η : ι → A) (k : Fin (n + 1)) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  of fun i ↦ k.insertNth (η (a i)) fun j ↦
    (if a i = b j then algebraMap K A (u - ((k.succAbove j).val : K)) else 0) + E (a i) (b j)

private theorem covectorBorder_self (E : Matrix ι ι A) (u : K) (a : Fin (n + 1) → ι)
    (b : Fin n → ι) (η : ι → A) (k i : Fin (n + 1)) :
    covectorBorder E u a b η k i k = η (a i) := by
  simp [covectorBorder]

private theorem covectorBorder_succAbove (E : Matrix ι ι A) (u : K) (a : Fin (n + 1) → ι)
    (b : Fin n → ι) (η : ι → A) (k i : Fin (n + 1)) (j : Fin n) :
    covectorBorder E u a b η k i (k.succAbove j) =
      (if a i = b j then algebraMap K A (u - ((k.succAbove j).val : K)) else 0) +
        E (a i) (b j) := by
  simp [covectorBorder]

/-- The ordered two-row Leibniz terms change sign when the covector crosses a column: the
commutator corrections are exactly the diagonal shifts of the ordinary entries. -/
private theorem covectorBorder_exchange (E : Matrix ι ι A) (u : K) (a : Fin (n + 1) → ι)
    (b : Fin n → ι) (η : ι → A) (j : Fin n) (r s : Fin (n + 1))
    (hr : E (a r) (b j) * η (a s) - η (a s) * E (a r) (b j) =
      if b j = a s then η (a r) else 0)
    (hs : E (a s) (b j) * η (a r) - η (a r) * E (a s) (b j) =
      if b j = a r then η (a s) else 0) :
    covectorBorder E u a b η j.succ r j.castSucc * covectorBorder E u a b η j.succ s j.succ -
      covectorBorder E u a b η j.succ s j.castSucc * covectorBorder E u a b η j.succ r j.succ =
    -(covectorBorder E u a b η j.castSucc r j.castSucc *
        covectorBorder E u a b η j.castSucc s j.succ -
      covectorBorder E u a b η j.castSucc s j.castSucc *
        covectorBorder E u a b η j.castSucc r j.succ) := by
  have first (i) := covectorBorder_succAbove E u a b η j.succ i j
  have last (i) := covectorBorder_succAbove E u a b η j.castSucc i j
  simp only [Fin.succAbove_succ_self, Fin.val_castSucc] at first
  simp only [Fin.succAbove_castSucc_self, Fin.val_succ, Nat.cast_add, Nat.cast_one,
    ← sub_sub] at last
  simp only [covectorBorder_self, first, last]
  have step (i : Fin (n + 1)) :
      (if a i = b j then algebraMap K A (u - (j.val : K) - 1) else 0) =
        (if a i = b j then algebraMap K A (u - (j.val : K)) else 0) -
          (if a i = b j then 1 else 0) := by
    split_ifs <;> simp
  rw [step r, step s]
  simp only [add_mul, mul_add, mul_sub]
  have central (i : Fin (n + 1)) (x : A) :
      (if a i = b j then algebraMap K A (u - (j.val : K)) else 0) * x =
        x * (if a i = b j then algebraMap K A (u - (j.val : K)) else 0) := by
    split_ifs
    · exact Algebra.commutes _ _
    · simp
  rw [central r, central s]
  by_cases h₁ : a r = b j <;> by_cases h₂ : a s = b j <;>
    simp only [eq_comm (a := b j), h₁, h₂, ite_true, ite_false, mul_one, mul_zero] at hr hs ⊢ <;>
    linear_combination (norm := abel) hr - hs

private theorem columnDet_covectorBorder_succ (E : Matrix ι ι A) (u : K)
    (a : Fin (n + 1) → ι) (b : Fin n → ι) (η : ι → A) (j : Fin n)
    (hη : ∀ r s, r ≠ s → E (a r) (b j) * η (a s) - η (a s) * E (a r) (b j) =
      if b j = a s then η (a r) else 0) :
    (covectorBorder E u a b η j.succ).columnDet =
      -(covectorBorder E u a b η j.castSucc).columnDet := by
  rw [← neg_one_smul ℤ]
  apply columnDet_eq_zsmul_of_adjacent _ _ _ (i := j.castSucc) (j := j.succ) (by simp)
  · intro r k hk₁ hk₂
    obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hk₁
    have hl : j.castSucc.succAbove l = j.succ.succAbove l := by
      rw [← Fin.swap_castSucc_succ_succAbove, Equiv.swap_apply_of_ne_of_ne hk₁ hk₂]
    calc
      _ = covectorBorder E u a b η j.succ r (j.succ.succAbove l) :=
        congrArg (covectorBorder E u a b η j.succ r) hl
      _ = _ := by rw [covectorBorder_succAbove, covectorBorder_succAbove, hl]
  · intro r s hrs
    rw [neg_one_smul]
    exact covectorBorder_exchange E u a b η j r s (hη r s hrs) (hη s r hrs.symm)

private theorem columnDet_covectorBorder_eq (E : Matrix ι ι A) (u : K) (a : Fin (n + 1) → ι)
    (b : Fin n → ι) (η : ι → A)
    (hη : ∀ r j s, r ≠ s → E (a r) (b j) * η (a s) - η (a s) * E (a r) (b j) =
      if b j = a s then η (a r) else 0) (k : Fin (n + 1)) :
    (covectorBorder E u a b η k).columnDet =
      (-1 : ℤ) ^ k.val • (covectorBorder E u a b η 0).columnDet := by
  induction k using Fin.induction with
  | zero => simp
  | succ j ih =>
    rw [columnDet_covectorBorder_succ E u a b η j (fun r s ↦ hη r j s), ih]
    simp only [Fin.val_succ, Fin.val_castSucc, pow_succ', mul_smul, neg_one_smul]

private theorem columnDet_covectorBorder_zero (E : Matrix ι ι A) (u : K)
    (a : Fin (n + 1) → ι) (b : Fin n → ι) (η : ι → A) :
    (covectorBorder E u a b η 0).columnDet =
      ∑ i, (-1 : ℤ) ^ i.val • (η (a i) * E.quantumMinor (u - 1) (i.removeNth a) b) := by
  rw [columnDet_succ_column_zero]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [covectorBorder_self, quantumMinor_eq_columnDet]
  congr 3
  ext r j
  rw [submatrix_apply, ← Fin.succAbove_zero, covectorBorder_succAbove]
  simp [Fin.removeNth, Nat.cast_add, sub_sub, add_comm (1 : K)]

private theorem columnDet_covectorBorder_last (E : Matrix ι ι A) (u : K)
    (a : Fin (n + 1) → ι) (b : Fin n → ι) (η : ι → A) :
    (covectorBorder E u a b η (Fin.last n)).columnDet =
      (-1 : ℤ) ^ n • ∑ i, (-1 : ℤ) ^ i.val • (E.quantumMinor u (i.removeNth a) b * η (a i)) := by
  rw [columnDet_succ_column_last, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [covectorBorder_self, smul_smul, quantumMinor_eq_columnDet]
  have hsign : (-1 : ℤ) ^ (n - i.val) = (-1 : ℤ) ^ n * (-1 : ℤ) ^ i.val := by
    have hi : n - i.val + i.val = n := by omega
    calc
      _ = (-1 : ℤ) ^ (n - i.val) * ((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ i.val) := by
        rw [← mul_pow]; norm_num
      _ = _ := by rw [← mul_assoc, ← pow_add, hi]
  rw [hsign]
  congr 3
  ext r j
  rw [submatrix_apply, ← Fin.succAbove_last_apply j, covectorBorder_succAbove]
  simp [Fin.removeNth]

/-- Move a covector from the left to the right of the signed cofactor contraction by increasing
all cofactor parameters by one. Only the mixed commutators between entries and covectors
in distinct row positions are required; the tuples need not be injective. -/
theorem sum_covector_mul_quantumMinor_eq (E : Matrix ι ι A) (u : K) (a : Fin (n + 1) → ι)
    (b : Fin n → ι) (η : ι → A)
    (hη : ∀ r j s, r ≠ s → E (a r) (b j) * η (a s) - η (a s) * E (a r) (b j) =
      if b j = a s then η (a r) else 0) :
    ∑ i, (-1 : ℤ) ^ i.val • (η (a i) * E.quantumMinor (u - 1) (i.removeNth a) b) =
      ∑ i, (-1 : ℤ) ^ i.val • (E.quantumMinor u (i.removeNth a) b * η (a i)) := by
  have h := columnDet_covectorBorder_eq E u a b η hη (Fin.last n)
  rw [columnDet_covectorBorder_zero, columnDet_covectorBorder_last, Fin.val_last] at h
  have hc : (-1 : ℤ) ^ n * (-1 : ℤ) ^ n = 1 := by rw [← mul_pow]; norm_num
  simpa only [smul_smul, hc, one_smul] using (congrArg ((-1 : ℤ) ^ n • ·) h).symm

end Matrix
