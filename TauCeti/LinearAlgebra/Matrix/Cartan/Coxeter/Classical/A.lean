/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Intertwining
public import TauCeti.LinearAlgebra.Matrix.Permutation
public import TauCeti.GroupTheory.Perm.Coxeter
public import TauCeti.Data.List.OneDegenerateOrder
import TauCeti.GroupTheory.Perm.OrbitCount.FinRotate

/-!
# The Coxeter element of type `Aₙ` has order `n + 1`

In the `ε`-model the simple root `αᵢ` is `εᵢ - εᵢ₊₁ ∈ ℤⁿ⁺¹` (`TauCeti.Coxeter.epsA`), the simple
reflection `sᵢ` becomes the permutation matrix of the adjacent transposition
`TauCeti.BraidGroup.transposition i = (i i+1)` (`TauCeti.Coxeter.epsA_mul_reflMatrix`), and the
Coxeter element becomes the permutation matrix of their product, the rotation `finRotate (n + 1)`
(`TauCeti.permCoxeterSystem_wordProd_finRange`), an `(n+1)`-cycle. The `ε`-embedding is injective,
so the order of the Coxeter element is `n + 1`.
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
  simp only [epsA, CartanMatrix.A, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

/-- If `E` intertwines each `f i` with the permutation matrix of the adjacent transposition
`(i i+1)`, then it intertwines the product `f 0 * f 1 * ⋯ * f (n - 1)` with the permutation matrix
of their product, the rotation `finRotate (n + 1)` (`TauCeti.permCoxeterSystem_wordProd_finRange`).
-/
theorem mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul {k : Type*} [Fintype k]
    [DecidableEq k] {E : Matrix (Fin (n + 1)) k ℤ} {f : Fin n → Matrix k k ℤ}
    (h : ∀ i, E * f i = permMatrixHom (R := ℤ) (BraidGroup.transposition (n := n + 1) i) * E) :
    E * ((List.finRange n).map f).prod = permMatrixHom (R := ℤ) (finRotate (n + 1)) * E := by
  rw [mul_list_map_prod_eq_list_map_prod_mul h]
  refine congrArg (· * E) ?_
  rw [← permCoxeterSystem_wordProd_finRange, permCoxeterSystem_wordProd, map_list_prod,
    List.map_map]
  rfl

/-- **The Coxeter element of type `Aₙ` is the rotation `finRotate (n + 1)`** in the `ε`-model. -/
theorem epsA_mul_coxeterElement :
    epsA n * coxeterElement (CartanMatrix.A n) =
      permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsA n :=
  mul_prod_map_finRange_eq_permMatrixHom_finRotate_mul epsA_mul_reflMatrix

/-- Partial sums: a left inverse of `epsA`. -/
def epsALeftInv (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.of fun i a => if a.val ≤ i.val then 1 else 0

theorem epsALeftInv_mul_epsA : epsALeftInv n * epsA n = 1 := by
  ext i k
  simp only [epsALeftInv, epsA, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k.castSucc (fun a _ ha =>
      ite_eq_right_iff.2 fun h => absurd (Fin.ext (by simpa using h)) ha) (by simp),
    Finset.sum_eq_single k.succ (fun a _ ha =>
      ite_eq_right_iff.2 fun h => absurd (Fin.ext (by simpa using h)) ha) (by simp)]
  simp only [Fin.val_castSucc, Fin.val_succ, ite_true, Fin.ext_iff]
  split_ifs <;> omega

/-- `epsA` can be cancelled on the left. -/
theorem epsA_mul_left_cancel {X Y : Matrix (Fin n) (Fin n) ℤ} (h : epsA n * X = epsA n * Y) :
    X = Y := by
  rw [← Matrix.one_mul X, ← Matrix.one_mul Y, ← epsALeftInv_mul_epsA, Matrix.mul_assoc,
    Matrix.mul_assoc, h]

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
      simp only [epsA, Matrix.of_apply] at this
      ext
      split_ifs at this <;> omega
    · have := hcol b ⟨n - 1, by omega⟩
      simp only [epsA, Matrix.of_apply] at this
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
  have hrot : orderOf (permMatrixHom (R := ℤ) (finRotate (n + 1))) =
      orderOf (finRotate (n + 1)) := orderOf_eq_orderOf_iff.2 fun k =>
    ⟨fun h => hfix k (by rw [h, Matrix.one_mul]), fun h => by rw [← map_pow, h, map_one]⟩
  rw [orderOf_eq_orderOf_of_mul_eq_mul epsA_mul_coxeterElement
      (fun k h => epsA_mul_left_cancel (h.trans (Matrix.mul_one _).symm))
      (fun k h => by rw [← map_pow, hfix k h, map_one]),
    hrot, orderOf_finRotate (Nat.succ_ne_zero n)]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.A, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂
    exacts [absurd h₁ hij, h₂, absurd rfl h]

end TauCeti.Coxeter

end
