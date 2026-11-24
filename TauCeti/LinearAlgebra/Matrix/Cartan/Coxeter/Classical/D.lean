/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.B
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
import TauCeti.Data.Fin.Basic
import TauCeti.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# The Coxeter element of type `Dₙ` has order `2n - 2`

Mathlib's `Dₙ` (`n = m + 3`) has the chain `0 - 1 - ⋯ - (n-3)` and the fork `n-3 - n-2`,
`n-3 - n-1`. In the `ε`-model `αᵢ = εᵢ - εᵢ₊₁` for `i ≤ n - 2` and `α_{n-1} = ε_{n-2} + ε_{n-1}`
(`TauCeti.Coxeter.epsD`, injective but of determinant `2`). The reflections become the
transpositions `(i i+1)` and the signed swap `ε_{n-2} ↦ -ε_{n-1}`, `ε_{n-1} ↦ -ε_{n-2}`; the Coxeter
element is the negacyclic shift of the first `n - 1` coordinates times `-1` on the last
(`TauCeti.Coxeter.negaD`, block diagonal by definition), so its order is that of the negacyclic
shift, `2n - 2`.
-/

public section

open Matrix Equiv.Perm

namespace TauCeti.Coxeter

variable {m : ℕ}

/-- The `ε`-coordinates of the simple roots of type `D_{m+3}`. -/
def epsD (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun a i =>
    if i.val < m + 2 then (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0)
    else (if a.val = m + 1 then 1 else 0) + (if a.val = m + 2 then 1 else 0)

theorem epsD_apply (a i : Fin (m + 3)) :
    epsD m a i =
      if i.val < m + 2 then (if a.val = i.val then 1 else 0) - (if a.val = i.val + 1 then 1 else 0)
      else (if a.val = m + 1 then 1 else 0) + (if a.val = m + 2 then 1 else 0) :=
  (rfl)

/-- The signed swap `ε_{m+1} ↦ -ε_{m+2}`, `ε_{m+2} ↦ -ε_{m+1}`. -/
private def flipPair (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun a b =>
    if a.val = m + 1 ∧ b.val = m + 2 then -1 else if a.val = m + 2 ∧ b.val = m + 1 then -1
    else if a = b ∧ a.val < m + 1 then 1 else 0

private theorem flipPair_mul_apply {k : Type*} (M : Matrix (Fin (m + 3)) k ℤ) (a : Fin (m + 3))
    (j : k) :
    (flipPair m * M) a j =
      if a.val = m + 1 then -M ⟨m + 2, by omega⟩ j
      else if a.val = m + 2 then -M ⟨m + 1, by omega⟩ j else M a j := by
  simp only [Matrix.mul_apply, flipPair, Matrix.of_apply, ite_mul, neg_one_mul, one_mul, zero_mul]
  by_cases h1 : a.val = m + 1
  · simp [h1, sum_ite_val_eq]
  · by_cases h2 : a.val = m + 2
    · simp [h2, sum_ite_val_eq]
    · have := a.isLt
      simp [h1, h2, show a.val < m + 1 by omega]


/-- The fork reflection `s_{n-1}` of type `Dₙ` is the signed swap of the last two coordinates. -/
private theorem epsD_mul_reflMatrix_last (i : Fin (m + 3)) (hi : i.val = m + 2) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i = flipPair m * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, flipPair_mul_apply]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  simp only [epsD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, hi, h2,
    ite_false, lt_irrefl, or_true, and_true]
  split_ifs <;> omega

/-- **The fork reflection `s_{n-1}` of type `Dₙ` is the signed swap `ε_{n-2} ↦ -ε_{n-1}`,
`ε_{n-1} ↦ -ε_{n-2}`** in the `ε`-model. -/
theorem epsD_mul_reflMatrix_last_apply (i : Fin (m + 3)) (hi : i.val = m + 2) (a j : Fin (m + 3)) :
    (epsD m * reflMatrix (CartanMatrix.D (m + 3)) i) a j =
      if a.val = m + 1 then -epsD m ⟨m + 2, by omega⟩ j
      else if a.val = m + 2 then -epsD m ⟨m + 1, by omega⟩ j else epsD m a j := by
  rw [epsD_mul_reflMatrix_last i hi, flipPair_mul_apply]

/-! The simple reflections `sᵢ`, `i < n - 1`, are the transpositions `(i i+1)` in the `ε`-model.
We treat separately the chain nodes `i < n - 3`, the branch node `i = n - 3` and the node
`i = n - 2` before the fork. -/

-- Splitting by node lets `simp` settle the branches of `CartanMatrix.D` before `split_ifs`; the
-- three cases are separate declarations because together they exceed the default heartbeat budget.

private theorem epsD_mul_reflMatrix_chain (i : Fin (m + 3)) (hi : i.val < m) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  have h3 : i.val + 2 < m + 3 := by omega
  have h4 : ¬ (i.val + 3 = m + 3) := by omega
  have h5 : ¬ (i.val + 2 = m + 3 ∨ i.val + 1 = m + 3) := by omega
  have h6 : i.val < m + 2 := by omega
  simp only [epsD_apply, CartanMatrix.D, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff, h2, h3,
    h4, h5, h6, ite_false, and_true, and_false, false_and]
  split_ifs <;> (try simp only at *) <;> omega

private theorem epsD_mul_reflMatrix_branch (i : Fin (m + 3)) (hi : i.val = m) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  have h3 : m + 2 < m + 3 := by omega
  have h5 : ¬ (m + 2 = m + 3 ∨ m + 1 = m + 3) := by omega
  have h6 : m < m + 2 := by omega
  simp only [epsD_apply, CartanMatrix.D, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff, hi,
    h2, h3, h5, h6, ite_false, ite_true, and_true, and_false, true_and]
  split_ifs <;> (try simp only [not_true_eq_false] at *) <;>
    omega

private theorem epsD_mul_reflMatrix_pre (i : Fin (m + 3)) (hi : i.val = m + 1) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, by omega⟩) * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, permMatrixHom_mul_apply, Equiv.symm_swap]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  have h3 : ¬ (m + 1 + 2 < m + 3) := by omega
  have h4 : ¬ (m + 1 + 3 = m + 3) := by omega
  have h6 : m + 1 < m + 2 := by omega
  simp only [epsD_apply, CartanMatrix.D, Matrix.of_apply, Equiv.swap_apply_def, Fin.ext_iff, hi,
    h2, h3, h4, h6, ite_false, ite_true, and_false, false_and]
  split_ifs <;> (try simp only [not_true_eq_false, and_true, true_or] at *) <;>
    omega

/-- The simple reflections `s₀, …, s_{n-2}` of type `Dₙ` are transpositions in the `ε`-model. -/
theorem epsD_mul_reflMatrix_of_lt (i : Fin (m + 3)) (hi : i.val + 1 < m + 3) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i =
      permMatrixHom (R := ℤ) (Equiv.swap i ⟨i.val + 1, hi⟩) * epsD m := by
  rcases Nat.lt_or_ge i.val m with h | h
  · exact epsD_mul_reflMatrix_chain i h
  · rcases Nat.eq_or_lt_of_le h with h' | h'
    · exact epsD_mul_reflMatrix_branch i h'.symm
    · exact epsD_mul_reflMatrix_pre i (by omega)

/-- The Coxeter element of type `D_{m+3}` in the `ε`-model: block diagonal, with the negacyclic
shift on the first `m + 2` coordinates and `-1` on the last. -/
def negaD (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  reindex (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3))
    (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3))
    (fromBlocks (negaShift ℤ (m + 2)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ))

/-- `negaD m` is block diagonal: the negacyclic shift on the first `m + 2` coordinates, `-1` on
the last. -/
theorem reindex_negaD (m : ℕ) :
    reindex (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm
        (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm (negaD m) =
      fromBlocks (negaShift ℤ (m + 2)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ) := by
  rw [negaD, ← reindex_symm, Equiv.symm_apply_apply]

theorem negaD_apply (a b : Fin (m + 3)) :
    negaD m a b =
      if b.val < m + 1 ∧ a.val = b.val + 1 then 1 else if b.val = m + 1 ∧ a.val = 0 then -1
      else if b.val = m + 2 ∧ a.val = m + 2 then -1 else 0 := by
  rw [negaD, reindex_apply, submatrix_apply]
  refine Fin.addCases (m := m + 2) (n := 1) (fun a => ?_) (fun a => ?_) a <;>
    refine Fin.addCases (m := m + 2) (n := 1) (fun b => ?_) (fun b => ?_) b <;>
    have := a.isLt <;> have := b.isLt
  · simp only [finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, negaShift_apply,
      Fin.val_castAdd]
    split_ifs <;> omega
  · simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      fromBlocks_apply₁₂, Matrix.zero_apply, Fin.val_castAdd, Fin.val_natAdd]
    split_ifs <;> omega
  · simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
      fromBlocks_apply₂₁, Matrix.zero_apply, Fin.val_castAdd, Fin.val_natAdd]
    split_ifs <;> omega
  · simp only [finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, Matrix.neg_apply,
      Matrix.one_apply, Subsingleton.elim a b, Fin.val_natAdd]
    split_ifs <;> omega

/-- **The Coxeter element of type `Dₙ` is `negaD`** in the `ε`-model. -/
theorem epsD_mul_coxeterElement :
    epsD m * coxeterElement (CartanMatrix.D (m + 3)) = negaD m * epsD m := by
  rw [coxeterElement, mul_prod_map_finRange_succ_eq_permMatrixHom_finRotate_mul_mul
    epsD_mul_reflMatrix_of_lt (epsD_mul_reflMatrix_last _ (by simp))]
  congr 1
  ext a b
  rw [permMatrixHom_mul_apply]
  obtain ⟨x, rfl⟩ := (finRotate (m + 3)).surjective a
  have hval : (finRotate (m + 3) x).val = (x.val + 1) % (m + 3) := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one]
  rw [Equiv.symm_apply_apply]
  simp only [flipPair, negaD_apply, Matrix.of_apply, Fin.ext_iff]
  rw [hval]
  by_cases hx : x.val + 1 < m + 3
  · have hm := Nat.mod_eq_of_lt hx
    split_ifs <;> omega
  · have hx' : x.val + 1 = m + 3 := by omega
    have hm : (x.val + 1) % (m + 3) = 0 := by rw [hx', Nat.mod_self]
    split_ifs <;> omega

/-- **The `Dₙ` Coxeter matrix `negaD` has order `2n - 2`**, the order of its block
`negaShift ℤ (n - 1)`. -/
theorem orderOf_negaD : orderOf (negaD m) = 2 * (m + 2) := by
  have hS := orderOf_negaShift (R := ℤ) (n := m + 2) (by omega) (by decide)
  have h : orderOf (negaD m) =
      orderOf (fromBlocks (negaShift ℤ (m + 2)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ)) := by
    rw [negaD, ← coe_reindexRingEquiv, ← RingEquiv.coe_toMulEquiv, MulEquiv.orderOf_eq]
  rw [h, orderOf_fromBlocks_zero_zero_neg_one (hS ▸ dvd_mul_right 2 _), hS]

/-- Right multiplication by `epsD m`: column `k` is the difference of columns `k` and `k + 1`
for `k < m + 2`, and the sum of the last two columns for `k = m + 2`. -/
private theorem mul_epsD_apply {l : Type*} (Z : Matrix l (Fin (m + 3)) ℤ) (i : l)
    (k : Fin (m + 3)) :
    (Z * epsD m) i k = if h : k.val < m + 2 then Z i k - Z i ⟨k.val + 1, by omega⟩
      else Z i ⟨m + 1, by omega⟩ + Z i ⟨m + 2, by omega⟩ := by
  simp only [Matrix.mul_apply, epsD_apply]
  split_ifs with hk
  · simp only [mul_sub, mul_ite, mul_one, mul_zero, Finset.sum_sub_distrib]
    rw [sum_ite_val_eq _ k.isLt, sum_ite_val_eq _ (by omega : k.val + 1 < m + 3)]
  · simp only [mul_add, mul_ite, mul_one, mul_zero, Finset.sum_add_distrib]
    rw [sum_ite_val_eq _ (by omega : m + 1 < m + 3), sum_ite_val_eq _ (by omega : m + 2 < m + 3)]

/-- Twice the rational inverse of `epsD m` (its adjugate, since `epsD m` has determinant `2`). Row
`i` holds the coordinates of `2 εⱼ` on the simple roots: `εⱼ = αⱼ + ⋯ + α_{n-3} +
(α_{n-2} + α_{n-1}) / 2` for `j ≤ n - 2`, and `ε_{n-1} = (α_{n-1} - α_{n-2}) / 2`. -/
private def epsDAdj (m : ℕ) : Matrix (Fin (m + 3)) (Fin (m + 3)) ℤ :=
  Matrix.of fun i j =>
    if j.val < m + 2 then
      (if j.val ≤ i.val ∧ i.val < m + 1 then 2 else if m + 1 ≤ i.val then 1 else 0)
    else if i.val = m + 1 then -1 else if i.val = m + 2 then 1 else 0

private theorem epsDAdj_mul_epsD : epsDAdj m * epsD m = (2 : ℤ) • 1 := by
  ext i k
  rw [mul_epsD_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  simp only [epsDAdj, Matrix.of_apply, Fin.ext_iff]
  split_ifs <;> omega

/-- `epsD` can be cancelled on the left: `epsDAdj m * epsD m = 2 • 1`, and `2` can be cancelled in
`ℤ`. -/
theorem isLeftRegular_epsD : IsLeftRegular (epsD m) := fun X Y h => by
  replace h : epsDAdj m * epsD m * X = epsDAdj m * epsD m * Y := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc]
    exact congrArg (epsDAdj m * ·) h
  rw [epsDAdj_mul_epsD, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.one_mul] at h
  ext a j
  have := congrFun (congrFun h a) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  omega

/-- **The Coxeter element of type `Dₙ` has order `2n - 2`** for `n ≥ 3`. -/
theorem orderOf_coxeterElement_D {n : ℕ} (hn : 3 ≤ n) :
    orderOf (coxeterElement (CartanMatrix.D n)) = 2 * (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  exact (orderOf_eq_orderOf_of_isLeftRegular epsD_mul_coxeterElement isLeftRegular_epsD).trans
    orderOf_negaD

/-- The order `0, 1, …, n - 1` is a one-degenerate order of the Dynkin diagram of type `Dₙ`
(`n = m + 3`): the fork node `n - 1` has the single earlier neighbour `n - 3`. -/
theorem isOneDegenerateOrder_D (m : ℕ) :
    List.IsOneDegenerateOrder (fun i j : Fin (m + 3) => CartanMatrix.D (m + 3) i j ≠ 0)
      (List.finRange (m + 3)) :=
  List.isOneDegenerateOrder_finRange_of_earlier_eq
    (fun z => if z.val = m + 2 then m else z.val - 1) fun z w hwz h => by
      have key : (z.val ≤ m + 1 ∧ w.val + 1 = z.val) ∨ (z.val = m + 2 ∧ w.val = m) := by
        simp only [CartanMatrix.D, Matrix.of_apply] at h
        split_ifs at h with h₁ h₂ h₃ h₄ h₅ h₆ <;>
          first | exact absurd rfl h | (subst h₁; omega) | omega
      split_ifs <;> omega

end TauCeti.Coxeter

end
