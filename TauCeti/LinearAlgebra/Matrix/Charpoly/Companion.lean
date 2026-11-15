/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Companion matrices, their characteristic polynomials, and cycle orders

For coefficients `c : Fin n → R`, the column companion matrix `Matrix.companion c` shifts each of
the first `n - 1` standard basis vectors to the next (`e_j ↦ e_{j + 1}`) and sends the last basis
vector `e_{n - 1}` to `-∑ i, c i • e_i`. Over a commutative ring its characteristic polynomial is
the monic polynomial `X ^ n + ∑ k : Fin n, C (c k) * X ^ (k : ℕ)`.

Two specializations govern the Coxeter elements of the classical Cartan matrices:
* `c = fun _ => 1` gives `charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k`, and has multiplicative
  order `n + 1` whenever `0 < n` and `(2 : R) ≠ 0` (type `A_n`);
* `c = Pi.single ⟨0, hn⟩ 1` gives `charpoly = X ^ n + 1`, satisfies `M ^ n = -1`, and has
  multiplicative order `2 * n` whenever `0 < n` and `(2 : R) ≠ 0` (the signed `n`-cycle appearing
  in types `B_n`, `C_n`, and `D_n`).

## Main definitions

* `Matrix.companion`: the `n × n` column companion matrix attached to `c : Fin n → R`.

## Main results

* `Matrix.charpoly_companion`: `(companion c).charpoly = X ^ n + ∑ k : Fin n, C (c k) * X ^ k.val`.
* `Matrix.charpoly_companion_const_one` and `Matrix.orderOf_companion_const_one`: characteristic
  polynomial and order `n + 1` of `companion (fun _ : Fin n => (1 : R))`.
* `Matrix.charpoly_companion_single_zero`, `Matrix.companion_single_zero_one_pow_eq_neg_one`, and
  `Matrix.orderOf_companion_single_zero_one`: characteristic polynomial `X ^ n + C a`, half-period
  `M ^ n = -1`, and order `2 * n` of `companion (Pi.single ⟨0, hn⟩ 1)`.
-/

public section

open Polynomial

namespace Matrix

section Defs

variable {R : Type*} [Zero R] [One R] [Neg R]

/-- The `n × n` column companion matrix of `c : Fin n → R`, with ones on the subdiagonal and `-c`
in the last column. -/
def companion {n : ℕ} (c : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  of fun i j =>
    if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -c i

/-- Entries of `Matrix.companion c`. -/
@[simp]
theorem companion_apply {n : ℕ} (c : Fin n → R) (i j : Fin n) :
    companion c i j =
      if (j : ℕ) + 1 < n then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else -c i :=
  (rfl)

end Defs

/-- Entrywise application of a ring homomorphism commutes with forming a companion matrix. -/
theorem map_companion {R S : Type*} [NonAssocRing R] [NonAssocRing S] (f : R →+* S) {n : ℕ}
    (c : Fin n → R) : (companion c).map f = companion (f ∘ c) := by
  ext i j
  simp only [map_apply, companion_apply, Function.comp_apply]
  split_ifs <;> simp

section Charpoly

variable {R : Type*} [CommRing R]

/-- **The characteristic polynomial of a companion matrix** `companion c` is
`X ^ n + ∑ k : Fin n, C (c k) * X ^ (k : ℕ)`. -/
theorem charpoly_companion {n : ℕ} (c : Fin n → R) :
    (companion c).charpoly = X ^ n + ∑ k : Fin n, C (c k) * X ^ (k : ℕ) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rcases m with _ | m
    · rw [charpoly, det_fin_one, charmatrix_apply, diagonal_apply_eq, companion_apply]
      simp
    · rw [charpoly, det_succ_row_zero]
      have h0ne_last : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) :=
        fun h => by simpa using congrArg Fin.val h
      have hmid : ∀ j : Fin (m + 2), j ≠ 0 → j ≠ Fin.last (m + 1) →
          charmatrix (companion c) 0 j = 0 := by
        intro j hj0 hjl
        have hjlt : (j : ℕ) + 1 < m + 2 := by
          have := j.isLt
          have : (j : ℕ) ≠ m + 1 := fun h => hjl (Fin.ext h)
          omega
        have h0ne : (0 : Fin (m + 2)) ≠ j := hj0.symm
        simp [charmatrix_apply, diagonal_apply_ne _ h0ne, companion_apply, hjlt]
      rw [Fintype.sum_eq_add (0 : Fin (m + 2)) (Fin.last (m + 1)) h0ne_last fun j ⟨hj0, hjl⟩ => by
        rw [hmid j hj0 hjl, mul_zero, zero_mul]]
      have h00 : charmatrix (companion c) 0 0 = X := by
        simp
      have hsub0 : (charmatrix (companion c)).submatrix Fin.succ (0 : Fin (m + 2)).succAbove =
          charmatrix (companion (c ∘ Fin.succ)) := by
        ext i k
        simp only [submatrix_apply, Fin.succAbove_zero, charmatrix_apply, diagonal_apply,
          Fin.succ_inj, companion_apply, Fin.val_succ, Function.comp_apply]
        have : (k : ℕ) + 1 + 1 < m + 2 ↔ (k : ℕ) + 1 < m + 1 := by omega
        have : (i : ℕ) + 1 = (k : ℕ) + 1 + 1 ↔ (i : ℕ) = (k : ℕ) + 1 := by omega
        split_ifs <;> simp_all
      have h0last : charmatrix (companion c) 0 (Fin.last (m + 1)) = C (c 0) := by
        simp
      let B := (charmatrix (companion c)).submatrix Fin.succ (Fin.last (m + 1)).succAbove
      have hBtri : B.IsUpperTriangular := by
        intro i k hki
        have hlt : (k : ℕ) < (i : ℕ) := hki
        have hne : i.succ ≠ k.castSucc := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
          omega
        have hkle : (k : ℕ) ≤ m := by have := k.isLt; omega
        have hik : (i : ℕ) ≠ (k : ℕ) := by omega
        simp [B, submatrix_apply, Fin.succAbove_last, charmatrix_apply,
          diagonal_apply_ne _ hne, companion_apply, hkle, hik]
      have hBdiag : ∀ i : Fin (m + 1), B i i = -1 := by
        intro i
        have hne : i.succ ≠ i.castSucc := by
          simp only [ne_eq, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
          omega
        have hile : (i : ℕ) ≤ m := by have := i.isLt; omega
        simp [B, submatrix_apply, Fin.succAbove_last, charmatrix_apply,
          diagonal_apply_ne _ hne, companion_apply, hile]
      have hBdet : B.det = (-1 : R[X]) ^ (m + 1) := by
        rw [det_of_isUpperTriangular hBtri]
        simp [hBdiag]
      have hdet0 : ((charmatrix (companion c)).submatrix Fin.succ (0 : Fin (m + 2)).succAbove).det =
          (companion (c ∘ Fin.succ)).charpoly := by
        rw [hsub0, charpoly]
      rw [h00, hdet0, ih (c ∘ Fin.succ), h0last, show
        ((charmatrix (companion c)).submatrix Fin.succ (Fin.last (m + 1)).succAbove).det =
          (-1 : R[X]) ^ (m + 1) from hBdet]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_last, Function.comp_apply]
      rw [mul_add, ← pow_succ', Finset.mul_sum]
      conv_rhs => rw [Fin.sum_univ_succ]
      have hsign : (-1 : R[X]) ^ (m + 1) * C (c 0) * (-1) ^ (m + 1) = C (c 0) := by
        calc (-1 : R[X]) ^ (m + 1) * C (c 0) * (-1) ^ (m + 1)
            = ((-1 : R[X]) ^ (m + 1)) ^ 2 * C (c 0) := by ring
          _ = C (c 0) := by rw [← pow_mul, mul_comm _ 2, pow_mul, neg_one_sq, one_pow, one_mul]
      rw [hsign]
      simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ]
      have hsum : ∑ x : Fin (m + 1), X * (C (c x.succ) * X ^ (x : ℕ)) =
          ∑ x : Fin (m + 1), C (c x.succ) * X ^ ((x : ℕ) + 1) :=
        Finset.sum_congr rfl fun x _ => by rw [pow_succ]; ring
      rw [hsum]
      ring

/-- The characteristic polynomial of the all-ones companion matrix is `1 + X + ⋯ + X ^ n`. -/
theorem charpoly_companion_const_one (n : ℕ) :
    (companion (fun _ : Fin n => (1 : R))).charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k := by
  rw [charpoly_companion, Finset.sum_range_succ, add_comm]
  simp [Fin.sum_univ_eq_sum_range (fun k => (X : R[X]) ^ k) n]

/-- The characteristic polynomial of the companion matrix supported on the first basis vector is
`X ^ n + C a`. -/
theorem charpoly_companion_single_zero {n : ℕ} (hn : 0 < n) (a : R) :
    (companion (Pi.single ⟨0, hn⟩ a)).charpoly = X ^ n + C a := by
  rw [charpoly_companion, Fintype.sum_eq_single ⟨0, hn⟩]
  · simp
  · intro k hk
    simp [Pi.single_eq_of_ne hk]

end Charpoly

section Order

variable {R : Type*} [Ring R]

/-- A companion matrix shifts each of the first `n - 1` standard basis vectors to the next. -/
theorem companion_mulVec_single_of_lt {n : ℕ} (c : Fin n → R) {j : Fin n} (hj : (j : ℕ) + 1 < n) :
    companion c *ᵥ Pi.single j 1 = Pi.single ⟨(j : ℕ) + 1, hj⟩ 1 := by
  ext i
  rw [mulVec_single_one, col_apply, companion_apply, ite_eq_left hj]
  simp [Pi.single_apply, Fin.ext_iff]

/-- A companion matrix sends the last standard basis vector to `-c`. -/
theorem companion_mulVec_single_of_eq {n : ℕ} (c : Fin n → R) {j : Fin n}
    (hj : (j : ℕ) + 1 = n) : companion c *ᵥ Pi.single j 1 = -c := by
  ext i
  have hnot : ¬ (j : ℕ) + 1 < n := by omega
  rw [mulVec_single_one, col_apply, companion_apply, ite_eq_right hnot, Pi.neg_apply]

/-- Powers of a companion matrix shift standard basis vectors as long as the index stays below
`n`. -/
theorem companion_pow_mulVec_single_of_lt {n : ℕ} (c : Fin n → R) {j : Fin n} {m : ℕ}
    (hjm : (j : ℕ) + m < n) :
    (companion c ^ m) *ᵥ Pi.single j 1 = Pi.single ⟨(j : ℕ) + m, hjm⟩ 1 := by
  induction m with
  | zero =>
    rw [pow_zero, one_mulVec]
    exact congrArg (Pi.single · 1) (Fin.ext (by simp))
  | succ m ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), companion_mulVec_single_of_lt c (by omega)]
    exact congrArg (Pi.single · 1) (Fin.ext (by simp [Nat.add_assoc]))

private theorem companion_const_one_mulVec_neg_one {n : ℕ} (hn : 0 < n) :
    companion (fun _ : Fin n => (1 : R)) *ᵥ (fun _ : Fin n => (-1 : R)) =
      Pi.single ⟨0, hn⟩ 1 := by
  ext i
  simp only [mulVec, dotProduct, companion_apply]
  rcases eq_or_ne (i : ℕ) 0 with hi0 | hi0
  · rw [Fintype.sum_eq_single (⟨n - 1, by omega⟩ : Fin n)]
    · have hnot : ¬ (n - 1 + 1 < n) := by omega
      have h0 : i = ⟨0, hn⟩ := Fin.ext hi0
      subst h0
      simp [hnot]
    · intro j hj
      have hjlt : (j : ℕ) + 1 < n := by
        have := j.isLt
        have : (j : ℕ) ≠ n - 1 := fun h => hj (Fin.ext h)
        omega
      simp [hjlt, hi0]
  · have hi1 : (i : ℕ) - 1 < n := by have := i.isLt; omega
    have hne : (⟨(i : ℕ) - 1, hi1⟩ : Fin n) ≠ ⟨n - 1, by omega⟩ := by
      have := i.isLt
      intro h
      have hval := congrArg Fin.val h
      dsimp only at hval
      omega
    rw [Fintype.sum_eq_add ⟨(i : ℕ) - 1, hi1⟩ ⟨n - 1, by omega⟩ hne]
    · have heq1 : (i : ℕ) - 1 + 1 = (i : ℕ) := by omega
      have hnot2 : ¬ (n - 1 + 1 < n) := by omega
      have hine0 : i ≠ ⟨0, hn⟩ := fun h => hi0 (congrArg Fin.val h)
      simp only [heq1, i.isLt, ↓reduceIte, hnot2, mul_neg, mul_one, neg_neg,
        Pi.single_eq_of_ne hine0]
      exact neg_add_cancel 1
    · intro j ⟨hj1, hj2⟩
      have hjlt : (j : ℕ) + 1 < n := by
        have := j.isLt
        have : (j : ℕ) ≠ n - 1 := fun h => hj2 (Fin.ext h)
        omega
      have hij : (i : ℕ) ≠ (j : ℕ) + 1 := by
        intro h
        apply hj1
        apply Fin.ext
        dsimp only
        omega
      simp [hjlt, hij]

/-- The all-ones companion matrix satisfies `M ^ (n + 1) = 1` over any ring. -/
theorem companion_const_one_pow_eq_one (n : ℕ) :
    companion (fun _ : Fin n => (1 : R)) ^ (n + 1) = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Subsingleton.elim _ _
  · ext i j
    have hsplit : n + 1 = (j : ℕ) + (1 + (1 + (n - 1 - (j : ℕ)))) := by
      have := j.isLt
      omega
    set M := companion (fun _ : Fin n => (1 : R))
    have hv : (M ^ (n + 1)) *ᵥ Pi.single j 1 =
        (1 : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single j 1 := by
      conv_lhs => enter [1, 2]; rw [hsplit]
      rw [pow_add, pow_add, pow_add, pow_one,
        ← mulVec_mulVec, ← mulVec_mulVec, ← mulVec_mulVec,
        companion_pow_mulVec_single_of_lt _ (by have := j.isLt; omega)]
      have hidx : (⟨(j : ℕ) + (n - 1 - (j : ℕ)), by have := j.isLt; omega⟩ : Fin n) =
          ⟨n - 1, by omega⟩ := by
        apply Fin.ext
        dsimp only
        have := j.isLt
        omega
      rw [hidx, companion_mulVec_single_of_eq _ (by simp; omega),
        show -(fun _ : Fin n => (1 : R)) = fun _ => -1 from rfl,
        companion_const_one_mulVec_neg_one hn,
        companion_pow_mulVec_single_of_lt _ (by simp [j.isLt]), one_mulVec]
      exact congrArg (Pi.single · 1) (Fin.ext (by simp))
    simpa only [mulVec_single_one, col_apply] using congrFun hv i

/-- **The all-ones companion matrix has multiplicative order `n + 1`** whenever `0 < n` and
`(2 : R) ≠ 0`. -/
theorem orderOf_companion_const_one {n : ℕ} (hn : 0 < n) (h2 : (2 : R) ≠ 0) :
    orderOf (companion (fun _ : Fin n => (1 : R))) = n + 1 := by
  have h10 : (1 : R) ≠ 0 := by
    intro h1
    apply h2
    rw [← one_add_one_eq_two, h1, add_zero]
  refine orderOf_eq_iff (by omega) |>.2
    ⟨companion_const_one_pow_eq_one n, fun m hmlt hm0 hpow => ?_⟩
  set M := companion (fun _ : Fin n => (1 : R))
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hmlt) with hmn | hmn
  · have hv := congrArg (fun A => (A *ᵥ Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨0, hn⟩) hpow
    rw [companion_pow_mulVec_single_of_lt _ (by simp [hmn]), one_mulVec] at hv
    have hne : (⟨0, hn⟩ : Fin n) ≠ ⟨0 + m, by simp [hmn]⟩ := by
      simp only [ne_eq, Fin.ext_iff, zero_add]
      omega
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_same] at hv
    exact h10 hv.symm
  · rw [hmn] at hpow
    have hv := congrArg (fun A => (A *ᵥ Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨0, hn⟩) hpow
    have hsplit : n = 1 + (n - 1) := by omega
    rw [one_mulVec, Pi.single_eq_same] at hv
    have hvm : (M ^ n) *ᵥ Pi.single ⟨0, hn⟩ 1 = -(fun _ : Fin n => (1 : R)) := by
      conv_lhs => enter [1, 2]; rw [hsplit]
      rw [pow_add, pow_one, ← mulVec_mulVec,
        companion_pow_mulVec_single_of_lt _ (by simp; omega)]
      have hidx : (⟨0 + (n - 1), by simp; omega⟩ : Fin n) = ⟨n - 1, by omega⟩ :=
        Fin.ext (by simp)
      rw [hidx, companion_mulVec_single_of_eq _ (by simp; omega)]
    rw [hvm, Pi.neg_apply] at hv
    apply h2
    rw [← one_add_one_eq_two]
    nth_rw 1 [← hv]
    exact neg_add_cancel 1

/-- The signed `n`-cycle companion matrix satisfies `M ^ n = -1` over any ring. -/
theorem companion_single_zero_one_pow_eq_neg_one {n : ℕ} (hn : 0 < n) :
    companion (Pi.single ⟨0, hn⟩ (1 : R)) ^ n = -1 := by
  ext i j
  set N := companion (Pi.single ⟨0, hn⟩ (1 : R))
  have hsplit : n = (j : ℕ) + (1 + (n - 1 - (j : ℕ))) := by
    have := j.isLt
    omega
  have hv : (N ^ n) *ᵥ Pi.single j 1 = (-1 : Matrix (Fin n) (Fin n) R) *ᵥ Pi.single j 1 := by
    conv_lhs => enter [1, 2]; rw [hsplit]
    rw [pow_add, pow_add, pow_one, ← mulVec_mulVec, ← mulVec_mulVec,
      companion_pow_mulVec_single_of_lt _ (by have := j.isLt; omega)]
    have hidx : (⟨(j : ℕ) + (n - 1 - (j : ℕ)), by have := j.isLt; omega⟩ : Fin n) =
        ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      dsimp only
      have := j.isLt
      omega
    rw [hidx, companion_mulVec_single_of_eq _ (by simp; omega), mulVec_neg,
      companion_pow_mulVec_single_of_lt _ (by simp [j.isLt]), neg_mulVec, one_mulVec]
    exact congrArg Neg.neg (congrArg (Pi.single · 1) (Fin.ext (by simp)))
  simpa only [mulVec_single_one, col_apply] using congrFun hv i

/-- **The signed `n`-cycle companion matrix has multiplicative order `2 * n`** whenever `0 < n`
and `(2 : R) ≠ 0`. -/
theorem orderOf_companion_single_zero_one {n : ℕ} (hn : 0 < n) (h2 : (2 : R) ≠ 0) :
    orderOf (companion (Pi.single ⟨0, hn⟩ (1 : R))) = 2 * n := by
  have h10 : (1 : R) ≠ 0 := by
    intro h1
    apply h2
    rw [← one_add_one_eq_two, h1, add_zero]
  set N := companion (Pi.single ⟨0, hn⟩ (1 : R))
  have hpow2n : N ^ (2 * n) = 1 := by
    rw [two_mul, pow_add, companion_single_zero_one_pow_eq_neg_one hn, neg_one_mul, neg_neg]
  refine orderOf_eq_iff (by omega) |>.2 ⟨hpow2n, fun m hmlt hm0 hpow => ?_⟩
  rcases lt_trichotomy m n with hmn | hmn | hnm
  · have hv := congrArg (fun A => (A *ᵥ Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨0, hn⟩) hpow
    rw [companion_pow_mulVec_single_of_lt _ (by simp [hmn]), one_mulVec] at hv
    have hne : (⟨0, hn⟩ : Fin n) ≠ ⟨0 + m, by simp [hmn]⟩ := by
      simp only [ne_eq, Fin.ext_iff, zero_add]
      omega
    rw [Pi.single_eq_of_ne hne, Pi.single_eq_same] at hv
    exact h10 hv.symm
  · rw [hmn, companion_single_zero_one_pow_eq_neg_one hn] at hpow
    have hv := congrArg (fun A => (A *ᵥ Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨0, hn⟩) hpow
    rw [neg_mulVec, one_mulVec, Pi.neg_apply, Pi.single_eq_same] at hv
    apply h2
    rw [← one_add_one_eq_two]
    nth_rw 1 [← hv]
    exact neg_add_cancel 1
  · set r := m - n
    have hrlt : r < n := by omega
    have hr0 : 0 < r := by omega
    have hm_eq : m = n + r := by omega
    rw [hm_eq, pow_add, companion_single_zero_one_pow_eq_neg_one hn, neg_one_mul] at hpow
    have hv := congrArg (fun A => (A *ᵥ Pi.single (⟨0, hn⟩ : Fin n) 1) ⟨0, hn⟩) hpow
    rw [neg_mulVec, companion_pow_mulVec_single_of_lt _ (by simp [hrlt]), one_mulVec] at hv
    have hne : (⟨0, hn⟩ : Fin n) ≠ ⟨0 + r, by simp [hrlt]⟩ := by
      simp only [ne_eq, Fin.ext_iff, zero_add]
      omega
    rw [Pi.neg_apply, Pi.single_eq_of_ne hne, neg_zero, Pi.single_eq_same] at hv
    exact h10 hv.symm

end Order

end Matrix

end
