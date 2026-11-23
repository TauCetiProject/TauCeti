/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Permutation
public import TauCeti.LinearAlgebra.Matrix.Permutation.Coxeter
public import TauCeti.Data.List.OneDegenerateOrder
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.Data.Fin.Basic
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# The Coxeter element of type `Aₙ` has order `n + 1`

In the `ε`-model the simple root `αᵢ` is `εᵢ - εᵢ₊₁ ∈ ℤⁿ⁺¹` (`TauCeti.Coxeter.epsA`), the simple
reflection `sᵢ` becomes the permutation matrix of the adjacent transposition
`TauCeti.BraidGroup.transposition i = (i i+1)` (`TauCeti.Coxeter.epsA_mul_reflMatrix`), and the
Coxeter element becomes the permutation matrix of their product, the rotation `finRotate (n + 1)`
(`TauCeti.permCoxeterSystem_wordProd_finRange`), an `(n+1)`-cycle. The `ε`-embedding is injective
(it has the left inverse `TauCeti.Coxeter.epsALeftInv`), so the order of the Coxeter element divides
that of the rotation; conversely, a permutation fixing every simple root `εᵢ - εᵢ₊₁` is the identity
(`TauCeti.Coxeter.eq_one_of_permMatrixHom_mul_epsA`), so the two orders agree: both are `n + 1`.

In the basis of simple roots the Coxeter element is, up to relabelling, the companion matrix of
`1 + X + ⋯ + Xⁿ` (`TauCeti.Coxeter.coxeterElement_A_apply`).
-/

public section

open Matrix Equiv.Perm

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The `ε`-coordinates of the simple roots of type `Aₙ`: column `i` is `εᵢ - εᵢ₊₁`. -/
def epsA (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  Matrix.of fun a i => (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0)

theorem epsA_apply (a : Fin (n + 1)) (i : Fin n) :
    epsA n a i = (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0) :=
  (rfl)

/-- **The simple reflection `sᵢ` is the transposition `(i i+1)`** in the `ε`-model. -/
theorem epsA_mul_reflMatrix (i : Fin n) :
    epsA n * reflMatrix (CartanMatrix.A n) i =
      permMatrixHom (R := ℤ) (BraidGroup.transposition (n := n + 1) i) * epsA n := by
  rw [BraidGroup.transposition_eq_swap_castSucc_succ]
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  simp only [epsA_apply, CartanMatrix.A, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

/-- **The Coxeter element of type `Aₙ` is the rotation `finRotate (n + 1)`** in the `ε`-model. -/
theorem epsA_mul_coxeterElement :
    epsA n * coxeterElement (CartanMatrix.A n) =
      permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsA n :=
  mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul epsA_mul_reflMatrix

/-- Partial sums: a left inverse of `epsA`. -/
def epsALeftInv (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.of fun i a => if a.val ≤ i.val then 1 else 0

theorem epsALeftInv_apply (i : Fin n) (a : Fin (n + 1)) :
    epsALeftInv n i a = if a.val ≤ i.val then 1 else 0 :=
  (rfl)

@[simp]
theorem epsALeftInv_mul_epsA : epsALeftInv n * epsA n = 1 := by
  ext i k
  simp only [epsALeftInv_apply, epsA_apply, Matrix.mul_apply, Matrix.one_apply, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [sum_ite_val_eq _ (Nat.lt_succ_of_lt k.isLt), sum_ite_val_eq _ (Nat.succ_lt_succ k.isLt)]
  simp only [Fin.ext_iff]
  split_ifs <;> omega

/-- Row sums of `epsA`: they telescope. -/
theorem sum_epsA_row (a : Fin (n + 1)) :
    ∑ j : Fin n, epsA n a j = (if a.val = 0 then 1 else 0) - (if a.val = n then 1 else 0) := by
  simp only [epsA_apply]
  rw [Fin.sum_univ_eq_sum_range
    (fun i => (if a.val = i then (1 : ℤ) else 0) - (if a.val = i + 1 then 1 else 0)) n]
  exact Finset.sum_range_sub' (fun i => if a.val = i then (1 : ℤ) else 0) n

/-- **The Coxeter element of type `Aₙ` is the companion matrix of `1 + X + ⋯ + Xⁿ`** (up to
relabelling): it sends `eₖ` to `e_{k+1}` for `k + 1 < n`, and `e_{n-1}` to `-(e₀ + ⋯ + e_{n-1})`. -/
theorem coxeterElement_A_apply (a k : Fin n) :
    coxeterElement (CartanMatrix.A n) a k =
      if k.val + 1 < n then (if a.val = k.val + 1 then 1 else 0) else -1 := by
  have hCe : epsA n * Matrix.of (fun a k : Fin n =>
      if k.val + 1 < n then (if a.val = k.val + 1 then (1 : ℤ) else 0) else -1) =
      permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsA n := by
    ext a k
    rw [permMatrixHom_mul_apply, Matrix.mul_apply]
    have hs : ((finRotate (n + 1)).symm a).val = if a.val = 0 then n else a.val - 1 := by
      by_cases ha : a = 0
      · rw [ha, (Equiv.symm_apply_eq _).2 finRotate_last.symm, Fin.val_last, Fin.val_zero,
          ite_eq_left rfl]
      · rw [coe_finRotate_symm_of_ne_zero ha,
          ite_eq_right fun h => ha (Fin.ext (by rw [h, Fin.val_zero]))]
    by_cases hk : k.val + 1 < n
    · rw [Finset.sum_eq_single ⟨k.val + 1, hk⟩]
      · simp only [epsA_apply, Matrix.of_apply, hk, ite_true, mul_one]
        split_ifs at hs ⊢ <;> omega
      · intro j _ hj
        simp only [Matrix.of_apply, hk, ite_true]
        rw [ite_eq_right (fun h => absurd (Fin.ext h) hj), mul_zero]
      · simp
    · simp only [Matrix.of_apply, hk, ite_false, mul_neg, mul_one, Finset.sum_neg_distrib,
        sum_epsA_row]
      simp only [epsA_apply]
      split_ifs at hs ⊢ <;> omega
  rw [mul_right_injective_of_inv _ _ epsALeftInv_mul_epsA
    (epsA_mul_coxeterElement.trans hCe.symm), Matrix.of_apply]

/-- A permutation matrix fixing every column of `epsA` is the identity. -/
theorem eq_one_of_permMatrixHom_mul_epsA {τ : Equiv.Perm (Fin (n + 1))}
    (h : permMatrixHom (R := ℤ) τ * epsA n = epsA n) : τ = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Equiv.ext fun x => Subsingleton.elim (α := Fin 1) _ _
  have hcol : ∀ a (i : Fin n), epsA n (τ.symm a) i = epsA n a i := fun a i => by
    have := congrFun (congrFun h a) i
    rwa [permMatrixHom_mul_apply] at this
  have hfix : ∀ b : Fin (n + 1), τ.symm b = b := by
    intro b
    by_cases hb : b.val < n
    · have := hcol b ⟨b.val, hb⟩
      simp only [epsA_apply] at this
      ext
      split_ifs at this <;> omega
    · have := hcol b ⟨n - 1, by omega⟩
      simp only [epsA_apply] at this
      ext
      split_ifs at this <;> omega
  ext b
  simpa using congrArg Fin.val (congrArg τ (hfix b)).symm

/-- **The Coxeter element of type `Aₙ` has order `n + 1`.** -/
theorem orderOf_coxeterElement_A (n : ℕ) :
    orderOf (coxeterElement (CartanMatrix.A n)) = n + 1 := by
  have hfix : ∀ k, permMatrixHom (R := ℤ) (finRotate (n + 1)) ^ k * epsA n = epsA n →
      finRotate (n + 1) ^ k = 1 := fun k h =>
    eq_one_of_permMatrixHom_mul_epsA (by rwa [map_pow])
  rw [orderOf_eq_orderOf_of_mul_eq_mul epsA_mul_coxeterElement
      (fun k h => mul_right_injective_of_inv _ _ epsALeftInv_mul_epsA
        (h.trans (Matrix.mul_one _).symm))
      (fun k h => by rw [← map_pow, hfix k h, map_one]),
    Equiv.Perm.orderOf_permMatrixHom, orderOf_finRotate (Nat.succ_ne_zero n)]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.A, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂
    exacts [absurd h₁ hij, h₂, absurd rfl h]

end TauCeti.Coxeter

end
