/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Alternating
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Abel
import TauCeti.Data.List.ProdOfFn

/-!
# Row form of quantum minors

In the presence of the matrix-unit relations, the column-ordered minor with descending
spectral shifts is also the row-ordered minor with ascending shifts. This gives ordered
Laplace expansions along the first and last rows, with the selected factors on opposite
sides of their cofactors. The double alternation argument cancels a factorial, so the
results are stated for additively torsion-free coefficient rings.

The row form is stated in L. Alpöge's `Formalism.FourierDecayAlt.Q.RowForm`.
-/

public section

namespace Matrix

open Equiv Equiv.Perm

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A] {n : ℕ}

-- Only the scalar parts change with the shift. Interchanging both index slots reverses
-- the difference caused by interchanging the parameters.
private theorem shiftPair_sub_swap (E : Matrix ι ι A) (s t : K) (i j k l : ι) :
    let T (v : K) (a b : ι) := (if a = b then algebraMap K A v else 0) + E a b
    T s i j * T t k l - T t i j * T s k l = -(T s k l * T t i j - T t k l * T s i j) := by
  dsimp only
  have hcomm (x y : ι) (c : K) := (Algebra.commutes c (E x y)).symm
  by_cases h₁ : i = j <;> by_cases h₂ : k = l <;>
    simp only [h₁, h₂, ite_true, ite_false, zero_add, add_mul, mul_add, hcomm, ← map_mul,
      mul_comm] <;> abel

private def shiftedSlots (E : Matrix ι ι A) (a b : Fin n → ι) (s : Fin n → K)
    (p : Perm (Fin n) × Perm (Fin n)) : Fin n → A := fun k =>
  (if a (p.1 k) = b (p.2 k) then algebraMap K A (s k) else 0) + E (a (p.1 k)) (b (p.2 k))

private def shiftDoubleSum (E : Matrix ι ι A) (a b : Fin n → ι) (s : Fin n → K) : A :=
  ∑ p : Perm (Fin n) × Perm (Fin n), (sign p.1 * sign p.2) •
    (List.ofFn (shiftedSlots E a b s p)).prod

private theorem shiftDoubleSum_comp_swap (E : Matrix ι ι A) (a b : Fin n → ι)
    (s : Fin n → K) {i j : Fin n} (hij : i.val + 1 = j.val) :
    shiftDoubleSum E a b (s ∘ swap i j) = shiftDoubleSum E a b s := by
  classical
  -- Swap both index slots in the change in the sum, leaving its sign unchanged.
  rw [← sub_eq_zero]
  simp only [shiftDoubleSum, ← Finset.sum_sub_distrib, ← smul_sub]
  let e := swap i j
  have hne : i ≠ j := by omega
  refine Finset.sum_involution (fun p _ => (p.1 * e, p.2 * e)) ?_ ?_ (by simp) ?_
  · intro p _
    have he : sign (p.1 * e) * sign (p.2 * e) = sign p.1 * sign p.2 := by
      simp [e, sign_swap hne]
    rw [he, ← smul_add]
    apply smul_eq_zero_of_right
    rw [add_eq_zero_iff_eq_neg]
    let f (q : Perm (Fin n) × Perm (Fin n)) (v : Fin n → K) := shiftedSlots E a b v q
    let q := (p.1 * e, p.2 * e)
    have hsplit (r : Perm (Fin n) × Perm (Fin n)) (v : Fin n → K)
        (hrv : ∀ k, k ≠ i → k ≠ j → f r v k = f p s k) :=
      List.prod_ofFn_eq_take_mul_mul_drop_of_eq (f r v) (f p s) hij hrv
    rw [hsplit q (s ∘ e) (by intros; simp [e, q, f, shiftedSlots, swap_apply_of_ne_of_ne, *]),
      hsplit q s (by intros; simp [e, q, f, shiftedSlots, swap_apply_of_ne_of_ne, *]),
      hsplit p (s ∘ e) (by intros; simp [e, f, shiftedSlots, swap_apply_of_ne_of_ne, *]),
      hsplit p s (by intros; rfl)]
    simpa only [q, f, shiftedSlots, e, Perm.mul_apply, Function.comp_apply, swap_apply_left,
      swap_apply_right, mul_sub, sub_mul, mul_neg, neg_mul, neg_sub] using
      congrArg (fun x => ((List.ofFn (f p s)).take i).prod * x *
        ((List.ofFn (f p s)).drop (j.val + 1)).prod)
        (shiftPair_sub_swap E (s i) (s j) (a (p.1 j)) (b (p.2 j)) (a (p.1 i)) (b (p.2 i))).symm
  · intro p _ _ hp
    have he : e = 1 := mul_left_cancel ((congrArg Prod.fst hp).trans (mul_one _).symm)
    exact hne (by simpa [e] using (congrArg (fun f : Perm (Fin n) => f i) he).symm)
  · intro p _
    simp [e, mul_assoc]

private theorem shiftDoubleSum_comp_perm (E : Matrix ι ι A) (a b : Fin n → ι)
    (s : Fin n → K) (e : Perm (Fin n)) : shiftDoubleSum E a b (s ∘ e) = shiftDoubleSum E a b s := by
  cases n with
  | zero => rw [Subsingleton.elim e 1]; rfl
  | succ n =>
    induction (mclosure_swap_castSucc_succ n).ge (Submonoid.mem_top e) using
      Submonoid.closure_induction_left generalizing s with
    | one => rfl
    | mul_left x hx y _ ih =>
      obtain ⟨i, rfl⟩ := hx
      rw [Perm.coe_mul, ← Function.comp_assoc, ih, shiftDoubleSum_comp_swap E a b s (by simp)]

private theorem shiftDoubleSum_descending (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (u : K) (a b : Fin n → ι) :
    shiftDoubleSum E a b (fun k => u - (k.val : K)) = n.factorial • E.quantumMinor u a b := by
  classical
  rw [shiftDoubleSum, ← Equiv.sum_comp (Equiv.prodComm (Perm (Fin n)) (Perm (Fin n))),
    Fintype.sum_prod_type]
  simp only [Equiv.prodComm_apply]
  calc
    _ = ∑ τ : Perm (Fin n), sign τ • E.quantumMinor u a (b ∘ τ) := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [quantumMinor_eq_columnDet, columnDet_apply, Finset.smul_sum]
      simp only [Prod.fst_swap, Prod.snd_swap, of_apply, ← mul_smul,
        mul_comm, Function.comp_apply]
      rfl
    _ = _ := by
      simp [E.quantumMinor_comp_perm_right hE, ← mul_smul, Fintype.card_perm]

private def rowShiftMatrix (E : Matrix ι ι A) (u : K) (a b : Fin n → ι) :
    Matrix (Fin n) (Fin n) A :=
  of fun j i => (if a i = b j then algebraMap K A (u - ((n - 1 : ℕ) : K) + i.val)
    else 0) + E (a i) (b j)

-- The row-ordered expression is the column determinant for negative transpose, with a
-- negation from each of the factors and the spectral parameter reflected as well.
private theorem columnDet_rowShiftMatrix (E : Matrix ι ι A) (u : K) (a b : Fin n → ι) :
    (rowShiftMatrix E u a b).columnDet =
      (-1 : A) ^ n * (-Eᵀ).quantumMinor (((n - 1 : ℕ) : K) - u) b a := by
  rw [quantumMinor_eq_columnDet, columnDet_apply, columnDet_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_smul_comm]
  congr 1
  have h (i : Fin n) :
      (rowShiftMatrix E u a b) (σ i) i =
        -((if b (σ i) = a i then algebraMap K A (((n - 1 : ℕ) : K) - u - (i.val : K)) else 0) +
          (-Eᵀ) (b (σ i)) (a i)) := by
    have hshift : -(((n - 1 : ℕ) : K) - u - (i.val : K)) =
        u - ((n - 1 : ℕ) : K) + (i.val : K) := by abel
    by_cases heq : a i = b (σ i)
    · simp only [rowShiftMatrix, of_apply, heq, ite_true, Matrix.neg_apply, transpose_apply,
        neg_add_rev, neg_neg, ← map_neg, hshift, add_comm]
    · simp [rowShiftMatrix, heq, Ne.symm heq]
  simp only [h, of_apply]
  simpa only [List.map_ofFn, Function.comp_def, List.length_ofFn] using
    (List.prod_map_neg (List.ofFn fun i : Fin n =>
      (if b (σ i) = a i then algebraMap K A (((n - 1 : ℕ) : K) - u - (i.val : K)) else 0) +
        (-Eᵀ) (b (σ i)) (a i)))

private theorem shiftDoubleSum_ascending (E : Matrix ι ι A) (hE : E.HasMatrixUnitLieRelations)
    (u : K) (a b : Fin n → ι) :
    shiftDoubleSum E a b (fun k => u - ((n - 1 : ℕ) : K) + (k.val : K)) =
      n.factorial • (rowShiftMatrix E u a b).columnDet := by
  classical
  rw [shiftDoubleSum, Fintype.sum_prod_type]
  calc
    _ = ∑ σ : Perm (Fin n), sign σ • (rowShiftMatrix E u (a ∘ σ) b).columnDet := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [columnDet_apply, Finset.smul_sum]
      simp only [rowShiftMatrix, of_apply, Function.comp_apply, mul_smul]
      rfl
    _ = _ := by
      simp [columnDet_rowShiftMatrix, (-Eᵀ).quantumMinor_comp_perm_right hE.neg_transpose,
        mul_smul_comm, ← mul_smul, Fintype.card_perm]

/-- The row form of a quantum minor is the column determinant of the transposed array with
ascending shifts: row `i` in the original minor carries parameter `u - (n - 1) + i`. -/
theorem quantumMinor_eq_columnDet_row [HasUniqueDiv A] (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) (a b : Fin n → ι) :
    E.quantumMinor u a b =
      (of fun j i => (if a i = b j then algebraMap K A (u - ((n - 1 : ℕ) : K) + i.val)
        else 0) + E (a i) (b j)).columnDet := by
  have hshift (i : Fin n) : u - ((Fin.revPerm i).val : K) =
      u - ((n - 1 : ℕ) : K) + (i.val : K) := by
    have hrev : (Fin.revPerm i).val = n - 1 - i.val := by
      rw [Fin.revPerm_apply, Fin.val_rev]
      omega
    rw [hrev, Nat.cast_sub (by omega : i.val ≤ n - 1)]
    abel
  have hcomp : (fun i : Fin n => u - (i.val : K)) ∘ Fin.revPerm =
      fun i => u - ((n - 1 : ℕ) : K) + (i.val : K) := funext hshift
  have h := shiftDoubleSum_comp_perm E a b (fun i => u - (i.val : K)) Fin.revPerm
  rw [hcomp, shiftDoubleSum_ascending E hE, shiftDoubleSum_descending E hE] at h
  exact nsmul_right_injective (Nat.factorial_ne_zero n) h.symm

/-- Expand a quantum minor in its first row. The selected entry uses the smallest spectral
parameter and multiplies its cofactor on the left. -/
theorem quantumMinor_succ_row_zero [HasUniqueDiv A] (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) (a b : Fin (n + 1) → ι) :
    E.quantumMinor u a b = ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
      (((if a 0 = b j then algebraMap K A (u - (n : K)) else 0) + E (a 0) (b j)) *
        E.quantumMinor u (Fin.tail a) (j.removeNth b)) := by
  rw [E.quantumMinor_eq_columnDet_row hE, columnDet_succ_column_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [E.quantumMinor_eq_columnDet_row hE u (Fin.tail a) (j.removeNth b)]
  simp only [of_apply, Nat.add_sub_cancel, Fin.val_zero, Nat.cast_zero, add_zero]
  congr 3
  ext i k
  have hs : u - (n : K) + ((k.succ).val : K) = u - ((n - 1 : ℕ) : K) + (k.val : K) := by
    have hn : 1 ≤ n := Nat.zero_lt_of_lt k.isLt
    simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn]
    abel
  simp only [submatrix_apply, of_apply, Fin.tail, Fin.removeNth, hs]
  rfl

/-- Expand a quantum minor in its last row. The selected entry uses the largest spectral
parameter and multiplies its cofactor on the right. -/
theorem quantumMinor_succ_row_last [HasUniqueDiv A] (E : Matrix ι ι A)
    (hE : E.HasMatrixUnitLieRelations) (u : K) (a b : Fin (n + 1) → ι) :
    E.quantumMinor u a b = ∑ j : Fin (n + 1), (-1 : ℤ) ^ (n - j.val) •
      (E.quantumMinor (u - 1) (Fin.init a) (j.removeNth b) *
        ((if a (Fin.last n) = b j then algebraMap K A u else 0) + E (a (Fin.last n)) (b j))) := by
  rw [E.quantumMinor_eq_columnDet_row hE, columnDet_succ_column_last]
  apply Finset.sum_congr rfl
  intro j _
  rw [E.quantumMinor_eq_columnDet_row hE (u - 1) (Fin.init a) (j.removeNth b)]
  simp only [of_apply, Nat.add_sub_cancel, Fin.val_last, sub_add_cancel]
  congr 3
  ext i k
  have hs : u - (n : K) + ((k.castSucc).val : K) = (u - 1) - ((n - 1 : ℕ) : K) + (k.val : K) := by
    have hn : 1 ≤ n := Nat.zero_lt_of_lt k.isLt
    simp only [Fin.val_castSucc, Nat.cast_sub hn, Nat.cast_one]
    abel
  simp only [submatrix_apply, of_apply, Fin.init, Fin.removeNth, hs]
  rfl

end Matrix
