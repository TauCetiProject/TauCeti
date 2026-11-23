/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.Cartan.Coxeter.Classical.B
public import Mathlib.Data.Matrix.Block
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Nonsingular
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
      if a.val = m + 1 then -M (Fin.last (m + 2)) j
      else if a.val = m + 2 then -M ⟨m + 1, by omega⟩ j else M a j := by
  rw [Matrix.mul_apply]
  by_cases h1 : a.val = m + 1
  · rw [Finset.sum_eq_single (Fin.last (m + 2))]
    · simp [flipPair, h1]
    · intro c _ hc
      have : c.val ≠ m + 2 := fun h => hc (Fin.ext h)
      simp only [flipPair, Matrix.of_apply]
      split_ifs <;> simp_all
      omega
    · simp
  · by_cases h2 : a.val = m + 2
    · rw [Finset.sum_eq_single ⟨m + 1, by omega⟩]
      · simp [flipPair, h2]
      · intro c _ hc
        have : c.val ≠ m + 1 := fun h => hc (Fin.ext h)
        simp only [flipPair, Matrix.of_apply]
        split_ifs <;> simp_all
        omega
      · simp
    · rw [Finset.sum_eq_single a]
      · simp only [flipPair, Matrix.of_apply, h1, h2, false_and, ite_false, true_and]
        rw [ite_eq_left (by omega), one_mul]
      · intro c _ hc
        simp only [flipPair, Matrix.of_apply]
        split_ifs <;> simp_all
      · simp


/-- The fork reflection `s_{n-1}` of type `Dₙ` is the signed swap of the last two coordinates. -/
private theorem epsD_mul_reflMatrix_last (i : Fin (m + 3)) (hi : i.val = m + 2) :
    epsD m * reflMatrix (CartanMatrix.D (m + 3)) i = flipPair m * epsD m := by
  ext a j
  rw [mul_reflMatrix_apply, flipPair_mul_apply]
  have h2 : ¬ (m + 3 ≤ 2) := by omega
  simp only [epsD_apply, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff, Fin.val_last, hi, h2,
    ite_false, lt_irrefl, or_true, and_true]
  split_ifs <;> omega

/-- **The fork reflection `s_{n-1}` of type `Dₙ` is the signed swap `ε_{n-2} ↦ -ε_{n-1}`,
`ε_{n-1} ↦ -ε_{n-2}`** in the `ε`-model. -/
theorem epsD_mul_reflMatrix_last_apply (i : Fin (m + 3)) (hi : i.val = m + 2) (a j : Fin (m + 3)) :
    (epsD m * reflMatrix (CartanMatrix.D (m + 3)) i) a j =
      if a.val = m + 1 then -epsD m (Fin.last (m + 2)) j
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
    (fromBlocks (negaShift (m + 2)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ))

/-- `negaD m` is block diagonal: the negacyclic shift on the first `m + 2` coordinates, `-1` on
the last. -/
theorem reindex_negaD (m : ℕ) :
    reindex (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm
        (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm (negaD m) =
      fromBlocks (negaShift (m + 2)) 0 0 (-1 : Matrix (Fin 1) (Fin 1) ℤ) := by
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
`negaShift (n - 1)`. -/
theorem orderOf_negaD : orderOf (negaD m) = 2 * (m + 2) := by
  have h := MulEquiv.orderOf_eq (reindexAlgEquiv ℤ ℤ
    (finSumFinEquiv : Fin (m + 2) ⊕ Fin 1 ≃ Fin (m + 3)).symm).toRingEquiv.toMulEquiv (negaD m)
  rw [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, AlgEquiv.coe_toRingEquiv,
    coe_reindexAlgEquiv, reindex_negaD] at h
  rw [← h]
  refine (orderOf_eq_orderOf_iff.2 fun k => ?_).trans (orderOf_negaShift (by omega))
  rw [fromBlocks_diagonal_pow, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨fun h => h.1, fun h => ⟨h, rfl, rfl, ?_⟩⟩
  have hdvd := orderOf_dvd_of_pow_eq_one h
  rw [orderOf_negaShift (by omega)] at hdvd
  exact (even_iff_two_dvd.2 ((dvd_mul_right 2 _).trans hdvd)).neg_one_pow

private theorem epsD_mul_apply {k : Type*} (Z : Matrix (Fin (m + 3)) k ℤ) (a : Fin (m + 3))
    (j : k) :
    (epsD m * Z) a j =
      (if a.val < m + 2 then Z a j else 0) -
        (if h : 1 ≤ a.val then Z ⟨a.val - 1, by omega⟩ j else 0) +
        (if a.val = m + 1 ∨ a.val = m + 2 then Z (Fin.last (m + 2)) j else 0) := by
  have hsplit : ∀ c, epsD m a c * Z c j =
      (if c = a then (if a.val < m + 2 then Z c j else 0) else 0) -
        (if a.val = c.val + 1 ∧ c.val < m + 2 then Z c j else 0) +
        (if c = Fin.last (m + 2) then (if a.val = m + 1 ∨ a.val = m + 2 then Z c j else 0)
          else 0) := by
    intro c
    simp only [epsD_apply, Fin.ext_iff, Fin.val_last]
    split_ifs <;> omega
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun c _ => hsplit c, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  congr 2
  by_cases ha : 1 ≤ a.val
  · rw [dite_eq_left ha, Finset.sum_eq_single ⟨a.val - 1, by omega⟩]
    · rw [ite_eq_left (by simp; omega)]
    · intro c _ hc
      exact ite_eq_right_iff.2 fun h => absurd (Fin.ext (by simp; omega)) hc
    · simp
  · rw [dite_eq_right ha]
    exact Finset.sum_eq_zero fun c _ => ite_eq_right_iff.2 fun h => absurd h.1 (by omega)

/-- `epsD` can be cancelled on the left (it has determinant `2` and `ℤ` is torsion-free). -/
theorem isLeftRegular_epsD : IsLeftRegular (epsD m) := fun X Y h => by
  replace h : epsD m * X = epsD m * Y := h
  have hZ : epsD m * (X - Y) = 0 := by rw [Matrix.mul_sub, h, sub_self]
  rw [← sub_eq_zero]
  ext c j
  let v : ℕ → ℤ := fun t => if ht : t < m + 3 then (X - Y) ⟨t, ht⟩ j else 0
  have hv : ∀ c : Fin (m + 3), (X - Y) c j = v c.val := fun c => by simp [v, c.isLt]
  have row : ∀ t, t < m + 3 →
      (if t < m + 2 then v t else 0) - (if 1 ≤ t then v (t - 1) else 0) +
        (if t = m + 1 ∨ t = m + 2 then v (m + 2) else 0) = 0 := by
    intro t ht
    have := congrFun (congrFun hZ ⟨t, ht⟩) j
    rw [epsD_mul_apply] at this
    simpa [hv] using this
  have chain : ∀ t ≤ m, v t = 0 := by
    intro t
    induction t with
    | zero =>
      intro _
      have := row 0 (by omega)
      rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega)] at this
      omega
    | succ t ih =>
      intro ht
      have := row (t + 1) (by omega)
      have := ih (by omega)
      simp only [Nat.add_sub_cancel] at *
      split_ifs at * <;> omega
  have h1 := row (m + 1) (by omega)
  have h2 := row (m + 2) (by omega)
  have hm := chain m le_rfl
  rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (Or.inl rfl)] at h1
  rw [ite_eq_right (by omega), ite_eq_left (by omega), ite_eq_left (Or.inr rfl)] at h2
  have hm1 : m + 2 - 1 = m + 1 := rfl
  simp only [Nat.add_sub_cancel, hm1] at h1 h2
  rw [Matrix.zero_apply, hv]
  have hc := c.isLt
  by_cases hcm : c.val ≤ m
  · exact chain _ hcm
  · obtain hh | hh : c.val = m + 1 ∨ c.val = m + 2 := by omega
    all_goals rw [hh]; omega

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
      (List.finRange (m + 3)) := by
  refine List.isOneDegenerateOrder_iff.2 fun S₁ z S₂ hS x hx y hy hzx hzy => ?_
  have hlt := (List.pairwise_append.1 (hS ▸ List.pairwise_lt_finRange (m + 3))).2.2
  have key : ∀ w : Fin (m + 3), w ∈ S₁ → CartanMatrix.D (m + 3) z w ≠ 0 →
      (z.val ≤ m + 1 ∧ w.val + 1 = z.val) ∨ (z.val = m + 2 ∧ w.val = m) := by
    intro w hw h
    have hwz : w.val < z.val := hlt w hw z List.mem_cons_self
    simp only [CartanMatrix.D, Matrix.of_apply] at h
    split_ifs at h with h₁ h₂ h₃ h₄ h₅ h₆ <;> first | exact absurd rfl h | (subst h₁; omega) | omega
  rcases key x hx hzx with h | h <;> rcases key y hy hzy with h' | h' <;> ext <;> omega

end TauCeti.Coxeter

end
