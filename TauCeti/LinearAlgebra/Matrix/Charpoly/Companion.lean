/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Companion matrices, their characteristic polynomials, and cycle orders

For `c : Fin n → R`, the column companion matrix `Matrix.companion c` shifts each of the first
`n - 1` standard basis vectors (`e_j ↦ e_{j + 1}`) and sends `e_{n - 1}` to `-∑ i, c i • e_i`.
Over a commutative ring its characteristic polynomial is `X ^ n + ∑ k : Fin n, C (c k) * X ^ k.val`.

Two specializations govern the Coxeter elements of the classical Cartan matrices:
* `c = fun _ => 1` gives `charpoly = ∑ k ∈ Finset.range (n + 1), X ^ k` and multiplicative order
  `n + 1` when `0 < n` and `(2 : R) ≠ 0` (type `A_n`);
* `c = Pi.single ⟨0, hn⟩ 1` gives `charpoly = X ^ n + 1`, `M ^ n = -1`, and multiplicative order
  `2 * n` when `0 < n` and `(2 : R) ≠ 0` (the signed `n`-cycle in types `B_n`, `C_n`, and `D_n`).

## Main definitions and results

* `Matrix.companion`: the `n × n` column companion matrix attached to `c : Fin n → R`.
* `Matrix.charpoly_companion`: `(companion c).charpoly = X ^ n + ∑ k : Fin n, C (c k) * X ^ k.val`.
* `Matrix.charpoly_companion_const_one`, `Matrix.companion_const_one_pow_eq_one`, and
  `Matrix.orderOf_companion_const_one`.
* `Matrix.charpoly_companion_single_zero`, `Matrix.companion_single_zero_one_pow_eq_neg_one`, and
  `Matrix.orderOf_companion_single_zero_one`.
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
  ext i j; simp only [map_apply, companion_apply, Function.comp_apply]; split_ifs <;> simp

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
    · rw [charpoly, det_fin_one, charmatrix_apply, diagonal_apply_eq, companion_apply]; simp
    · rw [charpoly, det_succ_row_zero]
      have h0ne_last : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]
      rw [Fintype.sum_eq_add (0 : Fin (m + 2)) (Fin.last (m + 1)) h0ne_last fun j ⟨hj0, hjl⟩ => by
        have hjlt : (j : ℕ) + 1 < m + 2 := by
          have := j.isLt; have : (j : ℕ) ≠ m + 1 := fun h => hjl (Fin.ext h); omega
        simp [charmatrix_apply, diagonal_apply_ne _ hj0.symm, companion_apply, hjlt]]
      have hsub0 : (charmatrix (companion c)).submatrix Fin.succ (0 : Fin (m + 2)).succAbove =
          charmatrix (companion (c ∘ Fin.succ)) := by
        ext i k
        simp only [submatrix_apply, Fin.succAbove_zero, charmatrix_apply, diagonal_apply,
          Fin.succ_inj, companion_apply, Fin.val_succ, Function.comp_apply]
        have : (k : ℕ) + 1 + 1 < m + 2 ↔ (k : ℕ) + 1 < m + 1 := by omega
        have : (i : ℕ) + 1 = (k : ℕ) + 1 + 1 ↔ (i : ℕ) = (k : ℕ) + 1 := by omega
        split_ifs <;> simp_all
      let B := (charmatrix (companion c)).submatrix Fin.succ (Fin.last (m + 1)).succAbove
      have hBtri : B.IsUpperTriangular := fun i k hki => by
        have hlt : (k : ℕ) < (i : ℕ) := hki
        have hne : i.succ ≠ k.castSucc := by simp [Fin.ext_iff]; omega
        simp [B, submatrix_apply, Fin.succAbove_last, charmatrix_apply, diagonal_apply_ne _ hne,
          companion_apply, show (k : ℕ) ≤ m by have := k.isLt; omega, show (i : ℕ) ≠ k by omega]
      have hBdet : B.det = (-1 : R[X]) ^ (m + 1) := by
        have hdiag : ∀ i : Fin (m + 1), B i i = -1 := fun i => by
          have hne : i.succ ≠ i.castSucc := by simp [Fin.ext_iff]
          simp [B, submatrix_apply, Fin.succAbove_last, charmatrix_apply, diagonal_apply_ne _ hne,
            companion_apply, show (i : ℕ) ≤ m by have := i.isLt; omega]
        rw [det_of_isUpperTriangular hBtri]; simp [hdiag]
      rw [show charmatrix (companion c) 0 0 = X by simp,
        show ((charmatrix (companion c)).submatrix Fin.succ (0 : Fin (m + 2)).succAbove).det =
          (companion (c ∘ Fin.succ)).charpoly by rw [hsub0, charpoly],
        ih (c ∘ Fin.succ), show charmatrix (companion c) 0 (Fin.last (m + 1)) = C (c 0) by simp,
        show ((charmatrix (companion c)).submatrix Fin.succ (Fin.last (m + 1)).succAbove).det =
          (-1 : R[X]) ^ (m + 1) from hBdet]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_last, Function.comp_apply]
      rw [mul_add, ← pow_succ', Finset.mul_sum]
      conv_rhs => rw [Fin.sum_univ_succ]
      have hsign : (-1 : R[X]) ^ (m + 1) * C (c 0) * (-1) ^ (m + 1) = C (c 0) := by
        rw [mul_right_comm, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
      have hsum : ∑ x : Fin (m + 1), X * (C (c x.succ) * X ^ (x : ℕ)) =
          ∑ x : Fin (m + 1), C (c x.succ) * X ^ ((x : ℕ) + 1) :=
        Finset.sum_congr rfl fun x _ => by rw [pow_succ]; ring
      rw [hsign, hsum]; simp [add_comm, add_left_comm]

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
  · intro k hk; simp [Pi.single_eq_of_ne hk]

end Charpoly

section Order

variable {R : Type*} [Ring R]

/-- A companion matrix shifts each of the first `n - 1` standard basis vectors to the next. -/
theorem companion_mulVec_single_of_lt {n : ℕ} (c : Fin n → R) {j : Fin n} (hj : (j : ℕ) + 1 < n) :
    companion c *ᵥ Pi.single j 1 = Pi.single ⟨(j : ℕ) + 1, hj⟩ 1 := by
  ext i; rw [mulVec_single_one, col_apply, companion_apply, ite_eq_left hj]
  simp [Pi.single_apply, Fin.ext_iff]

/-- A companion matrix sends the last standard basis vector to `-c`. -/
theorem companion_mulVec_single_of_eq {n : ℕ} (c : Fin n → R) {j : Fin n}
    (hj : (j : ℕ) + 1 = n) : companion c *ᵥ Pi.single j 1 = -c := by
  ext i; rw [mulVec_single_one, col_apply, companion_apply, ite_eq_right (by omega), Pi.neg_apply]

/-- Powers of a companion matrix shift standard basis vectors as long as the index stays below
`n`. -/
theorem companion_pow_mulVec_single_of_lt {n : ℕ} (c : Fin n → R) {j : Fin n} {m : ℕ}
    (hjm : (j : ℕ) + m < n) :
    (companion c ^ m) *ᵥ Pi.single j 1 = Pi.single ⟨(j : ℕ) + m, hjm⟩ 1 := by
  induction m with
  | zero =>
    rw [pow_zero, one_mulVec]; exact congrArg (Pi.single · 1) (Fin.ext (by simp))
  | succ m ih =>
    rw [pow_succ', ← mulVec_mulVec, ih (by omega), companion_mulVec_single_of_lt c (by omega)]
    exact congrArg (Pi.single · 1) (Fin.ext (by simp [Nat.add_assoc]))

private theorem companion_pow_zero_zero {n : ℕ} (hn : 0 < n) (c : Fin n → R) {m : ℕ}
    (hm0 : 0 < m) (hmn : m < n) : (companion c ^ m) ⟨0, hn⟩ ⟨0, hn⟩ = 0 := by
  have hv :=
    congrFun (companion_pow_mulVec_single_of_lt c (j := ⟨0, hn⟩) (by simpa using hmn)) ⟨0, hn⟩
  rwa [mulVec_single_one, col_apply, Pi.single_eq_of_ne (by simp [Fin.ext_iff]; omega)] at hv

/-- The all-ones companion matrix satisfies `M ^ (n + 1) = 1` over any ring. -/
theorem companion_const_one_pow_eq_one (n : ℕ) :
    companion (fun _ : Fin n => (1 : R)) ^ (n + 1) = 1 := by
  let Mℤ : Matrix (Fin n) (Fin n) ℤ := companion (fun _ => 1)
  have hsum : ∑ k ∈ Finset.range (n + 1), Mℤ ^ k = 0 := by
    have h := aeval_self_charpoly Mℤ
    rw [show Mℤ.charpoly = _ from charpoly_companion_const_one n, map_sum] at h
    simpa using h
  have hℤ : Mℤ ^ (n + 1) = 1 := sub_eq_zero.mp <| by rw [← geom_sum_mul, hsum, zero_mul]
  have hmap : (Int.castRingHom R).mapMatrix Mℤ = companion (fun _ : Fin n => (1 : R)) := by
    rw [RingHom.mapMatrix_apply, map_companion]; congr 1; ext; simp
  rw [← hmap, ← map_pow, hℤ, map_one]

/-- **The all-ones companion matrix has multiplicative order `n + 1`** whenever `0 < n` and
`(2 : R) ≠ 0`. -/
theorem orderOf_companion_const_one {n : ℕ} (hn : 0 < n) (h2 : (2 : R) ≠ 0) :
    orderOf (companion (fun _ : Fin n => (1 : R))) = n + 1 := by
  have h10 : (1 : R) ≠ 0 := fun h1 => h2 (by rw [← one_add_one_eq_two, h1, add_zero])
  set M := companion (fun _ : Fin n => (1 : R))
  refine (orderOf_eq_iff (by omega)).2 ⟨companion_const_one_pow_eq_one n, fun m hmlt hm0 hpow => ?_⟩
  rcases lt_or_eq_of_le (Nat.le_of_lt_succ hmlt) with hmn | rfl
  · have hv := congrArg (fun A => A ⟨0, hn⟩ ⟨0, hn⟩) hpow
    rw [companion_pow_zero_zero hn _ hm0 hmn, one_apply_eq] at hv
    exact h10 hv.symm
  · have hM1 : M = 1 := by
      calc M = M ^ m * M := by rw [hpow, one_mul]
        _ = M ^ (m + 1) := (pow_succ M m).symm
        _ = 1 := companion_const_one_pow_eq_one m
    have hv := congrArg (fun A => A ⟨0, hn⟩ ⟨m - 1, by omega⟩) hM1
    dsimp only [M] at hv
    rw [companion_apply, ite_eq_right (by simp; omega)] at hv
    rcases eq_or_ne m 1 with rfl | hm1
    · simp only [one_apply_eq] at hv
      exact h2 (by rw [← one_add_one_eq_two]; nth_rw 1 [← hv]; exact neg_add_cancel 1)
    · rw [one_apply_ne (by simp [Fin.ext_iff]; omega)] at hv
      exact h10 (neg_eq_zero.mp hv)

/-- The signed `n`-cycle companion matrix satisfies `M ^ n = -1` over any ring. -/
theorem companion_single_zero_one_pow_eq_neg_one {n : ℕ} (hn : 0 < n) :
    companion (Pi.single ⟨0, hn⟩ (1 : R)) ^ n = -1 := by
  let Nℤ : Matrix (Fin n) (Fin n) ℤ := companion (Pi.single ⟨0, hn⟩ 1)
  have hsum : Nℤ ^ n + 1 = 0 := by
    have h := aeval_self_charpoly Nℤ
    dsimp only [Nℤ] at h
    rwa [charpoly_companion_single_zero hn, map_one, map_add, map_pow, aeval_X, map_one] at h
  have hℤ : Nℤ ^ n = -1 := eq_neg_of_add_eq_zero_left hsum
  have hmap : (Int.castRingHom R).mapMatrix Nℤ = companion (Pi.single ⟨0, hn⟩ (1 : R)) := by
    rw [RingHom.mapMatrix_apply, map_companion]
    congr 1; ext k; rcases eq_or_ne k ⟨0, hn⟩ with rfl | hk <;> simp [*]
  rw [← hmap, ← map_pow, hℤ, map_neg, map_one]

/-- **The signed `n`-cycle companion matrix has multiplicative order `2 * n`** whenever `0 < n`
and `(2 : R) ≠ 0`. -/
theorem orderOf_companion_single_zero_one {n : ℕ} (hn : 0 < n) (h2 : (2 : R) ≠ 0) :
    orderOf (companion (Pi.single ⟨0, hn⟩ (1 : R))) = 2 * n := by
  have h10 : (1 : R) ≠ 0 := fun h1 => h2 (by rw [← one_add_one_eq_two, h1, add_zero])
  set N := companion (Pi.single ⟨0, hn⟩ (1 : R))
  have hpow2n : N ^ (2 * n) = 1 := by
    rw [two_mul, pow_add, companion_single_zero_one_pow_eq_neg_one hn, neg_one_mul, neg_neg]
  refine (orderOf_eq_iff (by omega)).2 ⟨hpow2n, fun m hmlt hm0 hpow => ?_⟩
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · have hv := congrArg (fun A => A ⟨0, hn⟩ ⟨0, hn⟩) hpow
    rw [companion_pow_zero_zero hn _ hm0 hmn, one_apply_eq] at hv
    exact h10 hv.symm
  · rw [companion_single_zero_one_pow_eq_neg_one hn] at hpow
    have hv := congrArg (fun A => A ⟨0, hn⟩ ⟨0, hn⟩) hpow
    rw [Matrix.neg_apply, one_apply_eq] at hv
    exact h2 (by rw [← one_add_one_eq_two]; nth_rw 1 [← hv]; exact neg_add_cancel 1)
  · rw [show m = n + (m - n) by omega, pow_add,
      companion_single_zero_one_pow_eq_neg_one hn, neg_one_mul] at hpow
    have hv := congrArg (fun A => A ⟨0, hn⟩ ⟨0, hn⟩) hpow
    rw [Matrix.neg_apply, companion_pow_zero_zero hn _ (by omega) (by omega), neg_zero,
      one_apply_eq] at hv
    exact h10 hv.symm

end Order

end Matrix

end
