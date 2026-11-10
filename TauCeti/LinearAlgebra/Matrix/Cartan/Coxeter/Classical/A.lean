/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Basic
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import TauCeti.Data.List.OneDegenerateOrder

/-!
# The Coxeter element of type `Aₙ` has order `n + 1`

In the `ε`-model the simple root `αᵢ` is `εᵢ - εᵢ₊₁ ∈ ℤⁿ⁺¹` (`TauCeti.Coxeter.epsMatrix`), the
simple reflection `sᵢ` becomes the permutation matrix of the transposition `(i i+1)`
(`TauCeti.Coxeter.epsMatrix_mul_reflMatrix`), and the Coxeter element becomes the permutation matrix
of `List.formPerm [0, 1, …, n]`, an `(n+1)`-cycle. The `ε`-embedding is injective, so the order of
the Coxeter element is `n + 1`.
-/

public section

open Matrix

namespace TauCeti.Coxeter

variable {n : ℕ}

/-- Left multiplication by the permutation matrix of `σ` moves row `σ⁻¹ a` to row `a`. -/
theorem permMatrixHom_mul_apply {m : ℕ} {k : Type*} (σ : Equiv.Perm (Fin m))
    (M : Matrix (Fin m) k ℤ) (a : Fin m) (j : k) :
    (permMatrixHom (R := ℤ) σ * M) a j = M (σ.symm a) j := by
  rw [permMatrixHom_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  rfl

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

/-- The product of the transpositions `(0 1) (1 2) ⋯ (n-1 n)` is `List.formPerm [0, 1, …, n]`. -/
theorem prod_adjSwap_eq_formPerm :
    ((List.finRange n).map adjSwap).prod = (List.finRange (n + 1)).formPerm := by
  rw [List.formPerm]
  congr 1
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_zipWith, List.getElem_tail,
    adjSwap]
  congr 1

/-- The `(n+1)`-cycle has order `n + 1`. -/
theorem orderOf_formPerm_finRange (hn : 1 ≤ n) :
    orderOf (List.finRange (n + 1)).formPerm = n + 1 := by
  have hlen : 2 ≤ (List.finRange (n + 1)).length := by simp; omega
  rw [(List.isCycle_formPerm (List.nodup_finRange _) hlen).orderOf,
    List.support_formPerm_of_nodup _ (List.nodup_finRange _), List.toFinset_card_of_nodup
      (List.nodup_finRange _), List.length_finRange]
  intro x hx
  have := congrArg List.length hx
  simp at this
  omega

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
    · have hb' : b.val = n := by omega
      have := hcol b ⟨n - 1, by omega⟩
      simp only [epsMatrix, Matrix.of_apply] at this
      ext
      split_ifs at this <;> omega
  ext b
  simpa using congrArg Fin.val (congrArg τ (hfix b)).symm

/-- **The Coxeter element of type `Aₙ` has order `n + 1`.** -/
theorem orderOf_coxeterElement_A (hn : 1 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.A n)) = n + 1 := by
  set σ := (List.finRange (n + 1)).formPerm
  have hc : epsMatrix n * coxeterElement (CartanMatrix.A n) =
      permMatrixHom (R := ℤ) σ * epsMatrix n := by
    rw [coxeterElement, epsMatrix_mul_prod, prod_adjSwap_eq_formPerm]
  have hpow : ∀ k, epsMatrix n * coxeterElement (CartanMatrix.A n) ^ k =
      permMatrixHom (R := ℤ) (σ ^ k) * epsMatrix n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, hc,
        ← Matrix.mul_assoc, ← map_mul (permMatrixHom (R := ℤ)), ← pow_succ]
  rw [← orderOf_formPerm_finRange hn]
  refine orderOf_eq_orderOf_iff.2 fun k => ⟨fun h => ?_, fun h => ?_⟩
  · apply eq_one_of_permMatrixHom_mul_epsMatrix hn
    rw [← hpow, h, Matrix.mul_one]
  · have := congrArg (fun M => epsLeftInv n * M) (hpow k)
    rw [h, map_one, Matrix.one_mul, ← Matrix.mul_assoc, epsLeftInv_mul_epsMatrix,
      Matrix.one_mul] at this
    exact this

/-- The path `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Aₙ`. -/
theorem isOneDegenerateOrder_A (n : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin n => CartanMatrix.A n i j ≠ 0) (List.finRange n) :=
  List.isOneDegenerateOrder_finRange fun i j hij h => by
    simp only [CartanMatrix.A, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂
    exacts [absurd h₁ hij, h₂, absurd rfl h]

end TauCeti.Coxeter

end
