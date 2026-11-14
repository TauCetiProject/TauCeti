/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import TauCeti.LinearAlgebra.Matrix.Intertwining
public import TauCeti.LinearAlgebra.Matrix.Permutation
public import TauCeti.GroupTheory.Perm.Fin
public import TauCeti.Data.List.OneDegenerateOrder

/-!
# The Coxeter element of type `Aₙ` has order `n + 1`

In the `ε`-model the simple root `αᵢ` is `εᵢ - εᵢ₊₁ ∈ ℤⁿ⁺¹` (`TauCeti.Coxeter.epsMatrix`), the
simple reflection `sᵢ` becomes the permutation matrix of the transposition `(i i+1)`
(`TauCeti.Coxeter.epsMatrix_mul_reflMatrix`), and the Coxeter element becomes the permutation matrix
of the rotation `finRotate (n + 1)`, an `(n+1)`-cycle. The `ε`-embedding is injective, so the order
of the Coxeter element is `n + 1`.
-/

public section

open Matrix Equiv.Perm

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- The `ε`-coordinates of the simple roots of type `Aₙ`: column `i` is `εᵢ - εᵢ₊₁`. -/
@[expose] def epsMatrix (n : ℕ) : Matrix (Fin (n + 1)) (Fin n) ℤ :=
  Matrix.of fun a i => (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0)

/-- **The simple reflection `sᵢ` is the transposition `(i i+1)`** in the `ε`-model. -/
theorem epsMatrix_mul_reflMatrix (i : Fin n) :
    epsMatrix n * reflMatrix (CartanMatrix.A n) i =
      permMatrixHom (R := ℤ) (Equiv.swap i.castSucc i.succ) * epsMatrix n := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  simp only [epsMatrix, CartanMatrix.A, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff,
    Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> simp_all <;> omega

/-- The transposition `(i i+1)` attached to the `i`-th simple root of type `Aₙ`. -/
@[expose] def adjSwap (i : Fin n) : Equiv.Perm (Fin (n + 1)) := Equiv.swap i.castSucc i.succ

/-- A word in the simple reflections becomes the product of the corresponding transpositions. -/
theorem epsMatrix_mul_prod (l : List (Fin n)) :
    epsMatrix n * (l.map (reflMatrix (CartanMatrix.A n))).prod =
      permMatrixHom (R := ℤ) (l.map adjSwap).prod * epsMatrix n := by
  induction l with
  | nil => simp
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, ← Matrix.mul_assoc, epsMatrix_mul_reflMatrix,
      Matrix.mul_assoc, ih, ← Matrix.mul_assoc, List.map_cons, List.prod_cons, map_mul]
    rfl

/-- The product of the transpositions `(0 1) (1 2) ⋯ (n-1 n)` is the rotation `finRotate (n + 1)`,
that is `List.formPerm [0, 1, …, n]`. -/
theorem prod_adjSwap_eq_finRotate :
    ((List.finRange n).map adjSwap).prod = finRotate (n + 1) := by
  rw [← List.formPerm_finRange, List.formPerm]
  congr 1
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_zipWith, List.getElem_tail,
    adjSwap]
  congr 1

/-- Partial sums: a left inverse of `epsMatrix`. -/
@[expose] def epsLeftInv (n : ℕ) : Matrix (Fin n) (Fin (n + 1)) ℤ :=
  Matrix.of fun i a => if a.val ≤ i.val then 1 else 0

theorem epsLeftInv_mul_epsMatrix : epsLeftInv n * epsMatrix n = 1 := by
  ext i k
  simp only [epsLeftInv, epsMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, mul_sub,
    mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single k.castSucc (fun a _ ha =>
      ite_eq_right_iff.2 fun h => absurd (Fin.ext (by simpa using h)) ha) (by simp),
    Finset.sum_eq_single k.succ (fun a _ ha =>
      ite_eq_right_iff.2 fun h => absurd (Fin.ext (by simpa using h)) ha) (by simp)]
  simp only [Fin.val_castSucc, Fin.val_succ, ite_true, Fin.ext_iff]
  split_ifs <;> omega

/-- A permutation matrix fixing every column of `epsMatrix` is the identity. -/
theorem eq_one_of_permMatrixHom_mul_epsMatrix (hn : 1 ≤ n) {τ : Equiv.Perm (Fin (n + 1))}
    (h : permMatrixHom (R := ℤ) τ * epsMatrix n = epsMatrix n) : τ = 1 := by
  have hcol : ∀ a (i : Fin n), epsMatrix n (τ.symm a) i = epsMatrix n a i := fun a i => by
    have := congrFun (congrFun h a) i
    rwa [permMatrixHom_mul_apply] at this
  have hfix : ∀ b : Fin (n + 1), τ.symm b = b := by
    intro b
    by_cases hb : b.val < n
    · have := hcol b ⟨b.val, hb⟩
      simp only [epsMatrix, Matrix.of_apply] at this
      ext
      split_ifs at this <;> omega
    · have := hcol b ⟨n - 1, by omega⟩
      simp only [epsMatrix, Matrix.of_apply] at this
      ext
      split_ifs at this <;> omega
  ext b
  simpa using congrArg Fin.val (congrArg τ (hfix b)).symm

/-- **The Coxeter element of type `Aₙ` has order `n + 1`.** -/
theorem orderOf_coxeterElement_A (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.A n)) = n + 1 := by
  have hc : epsMatrix n * coxeterElement (CartanMatrix.A n) =
      permMatrixHom (R := ℤ) (finRotate (n + 1)) * epsMatrix n := by
    rw [coxeterElement, epsMatrix_mul_prod, prod_adjSwap_eq_finRotate]
  have hfix : ∀ k, permMatrixHom (R := ℤ) (finRotate (n + 1)) ^ k * epsMatrix n = epsMatrix n →
      finRotate (n + 1) ^ k = 1 := fun k h =>
    eq_one_of_permMatrixHom_mul_epsMatrix hn (by rwa [map_pow])
  have hrot : orderOf (permMatrixHom (R := ℤ) (finRotate (n + 1))) =
      orderOf (finRotate (n + 1)) := orderOf_eq_orderOf_iff.2 fun k =>
    ⟨fun h => hfix k (by rw [h, Matrix.one_mul]), fun h => by rw [← map_pow, h, map_one]⟩
  have hcox : ∀ k, epsMatrix n * coxeterElement (CartanMatrix.A n) ^ k = epsMatrix n →
      coxeterElement (CartanMatrix.A n) ^ k = 1 := fun k h => by
    rw [← Matrix.one_mul (coxeterElement (CartanMatrix.A n) ^ k), ← epsLeftInv_mul_epsMatrix,
      Matrix.mul_assoc, h]
  rw [orderOf_eq_orderOf_of_mul_eq_mul hc hcox (fun k h => by rw [← map_pow, hfix k h, map_one]),
    hrot, (isCycle_finRotate_of_le (by omega)).orderOf, support_finRotate_of_le (by omega),
    Finset.card_univ, Fintype.card_fin]

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.A, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂
    exacts [absurd h₁ hij, h₂, absurd rfl h]

end TauCeti.Coxeter

end
