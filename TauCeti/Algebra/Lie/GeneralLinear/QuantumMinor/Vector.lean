/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.GeneralLinear.QuantumMinor.Commutator
import Mathlib.GroupTheory.Perm.Fin
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Vector commutators of quantum minors

For a vector operator `y` (so `⁅E i j, y k⁆ = if i = k then -y j else 0`), this file computes
`⁅y c, Δ_ab(u)⁆` for a quantum minor `Δ_ab(u)` as the sum, over the rows `i` with `a i = c`, of
the signed row cofactors at the same parameter `u`, each multiplied by the vector on the left
(`lie_vector_quantumMinor`). For the full quantum determinant `Δ(u)` this gives
`Δ(u) * y c = y c * Δ(u) - ∑ j, ± y j * Δ_{c,j}(u)` (`quantumMinor_id_mul_vector`). These
identities move vector components across quantum (Capelli) determinants in spectral-shift
computations.

The full determinant formula is L. Alpöge's `Formalism.FourierDecayAlt.Qr.DetVec`
in the formalization of the Riemann hypothesis for Dirichlet L-functions.
-/

public section

namespace Matrix

open Function

attribute [local instance 100] LieRing.ofAssociativeRing

variable {ι K A : Type*} [DecidableEq ι] [CommRing K] [Ring A] [Algebra K A]

-- Adjoin a fresh row label for the vector. The new column is never used.
private def withVectorRow (E : Matrix ι ι A) (y : ι → A) : Matrix (Option ι) (Option ι) A :=
  of fun i j ↦ j.elim 0 fun l ↦ i.elim (y l) (fun k ↦ E k l)

private theorem quantumMinor_withVectorRow_some (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a b : Fin n → ι) :
    (withVectorRow E y).quantumMinor u (some ∘ a) (some ∘ b) = E.quantumMinor u a b := by
  simp [quantumMinor_eq_columnDet, withVectorRow, Function.comp_def]

private theorem quantumMinor_update_vectorRow (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a b : Fin (n + 1) → ι) (i : Fin (n + 1)) :
    (withVectorRow E y).quantumMinor u (update (some ∘ a) i none) (some ∘ b) =
      (-1 : ℤ) ^ i.val • (withVectorRow E y).quantumMinor u
        (Fin.cons none (some ∘ i.removeNth a)) (some ∘ b) := by
  have h : Fin.cons none (some ∘ i.removeNth a) =
      update (some ∘ a) i none ∘ i.cycleRange.symm := by
    rw [← Fin.cons_removeNth_eq_comp_cycleRange_symm]
    simp only [update_self, Fin.removeNth_update, Function.comp_def, Fin.removeNth_comp]
  rw [h, quantumMinor_comp_perm_left, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  simp [Units.smul_def, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]

-- Before expanding in cofactors, infinitesimal covariance inserts the vector in each matching row.
private theorem lie_vector_quantumMinor_rows (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a b : Fin (n + 1) → ι) (c : ι)
    (hy : ∀ i j, ⁅y c, E (a i) (b j)⁆ = if c = a i then y (b j) else 0) :
    ⁅y c, E.quantumMinor u a b⁆ = ∑ i, if c = a i then
      (-1 : ℤ) ^ i.val • (withVectorRow E y).quantumMinor u
        (Fin.cons none (some ∘ i.removeNth a)) (some ∘ b) else 0 := by
  have h := (withVectorRow E y).lie_quantumMinor (p := none) (q := some c)
    u (some ∘ a) (some ∘ b) (fun i j ↦ by
      simpa [withVectorRow] using hy i j)
  simp only [quantumMinor_withVectorRow_some, quantumMinor_update_vectorRow] at h
  exact h.trans (by simp)

-- The two signs arise from deleting the last column before or after the first row.
private theorem cofactor_sign (n : ℕ) (i : Fin (n + 1)) :
    -((-1 : ℤ) ^ (n + 1) * (-1) ^ i.val) = (-1) ^ (n - i.val) := by
  -- write `n = i + k`; the two factors combine to `(-1) ^ (2 * i + k + 1)`
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le i.is_le
  simp only [hk, Nat.add_sub_cancel_left]
  rw [← pow_add, show i.val + k + 1 + i.val = 2 * i.val + (k + 1) by ring, pow_add, pow_mul]
  simp [pow_succ]

-- The last shift for the bordered minor has an extra subtraction by one.
private theorem vectorRow_shift (E : Matrix ι ι A) (u : K) (n : ℕ) (i j : ι) :
    ((if i = j then algebraMap K A (u - (↑(n + 1) : K)) else 0) + E i j) +
        (if i = j then 1 else 0) =
      (if i = j then algebraMap K A (u - (n : K)) else 0) + E i j := by
  split_ifs
  · simp
    abel
  · simp

-- Expand the cofactors that retain the last column, and interchange the two finite sums.
private theorem sum_vector_mul_cofactor_castSucc (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a : Fin (n + 1) → ι) (b : Fin (n + 2) → ι) :
    (∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
      (y (b j.castSucc) * E.quantumMinor u a (j.castSucc.removeNth b))) =
    ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
      ((∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
        (y (b j.castSucc) * E.quantumMinor u (i.removeNth a) (j.removeNth (Fin.init b)))) *
          ((if a i = b (Fin.last (n + 1)) then algebraMap K A (u - (n : K)) else 0) +
            E (a i) (b (Fin.last (n + 1))))) := by
  have init_removeNth_castSucc (j : Fin (n + 1)) :
      Fin.init (j.castSucc.removeNth b) = j.removeNth (Fin.init b) := by
    ext k
    simp only [Fin.init, Fin.removeNth_apply, Fin.castSucc_succAbove_castSucc]
  simp_rw [quantumMinor_succ_column_last E u a (Fin.removeNth _ b),
    init_removeNth_castSucc, Fin.removeNth_apply (i := Fin.last n),
    Fin.succAbove_ne_last_last (Fin.castSucc_lt_last _).ne,
    Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _

private theorem quantumMinor_vectorRow_succ (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a : Fin (n + 1) → ι) (b : Fin (n + 2) → ι) :
    let z := b (Fin.last (n + 1))
    let b₀ := Fin.init b
    (withVectorRow E y).quantumMinor u (Fin.cons none (some ∘ a)) (some ∘ b) =
      (-1 : ℤ) ^ (n + 1) • (E.quantumMinor u a b₀ * y z) +
      ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
        ((withVectorRow E y).quantumMinor u (Fin.cons none (some ∘ i.removeNth a)) (some ∘ b₀) *
          ((if a i = z then algebraMap K A (u - (↑(n + 1) : K)) else 0) + E (a i) z)) := by
  intro z b₀
  have hremove (i : Fin (n + 1)) :
      i.succ.removeNth (α := fun _ ↦ Option ι) (Fin.cons none (some ∘ a)) =
        Fin.cons none (some ∘ i.removeNth a) := Fin.cons_comp_succ_succAbove none (some ∘ a) i
  have hinit : Fin.init (some ∘ b) = some ∘ b₀ := (Fin.comp_init some b).symm
  rw [quantumMinor_succ_column_last, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.sub_zero, Fin.removeNth_zero, Fin.tail_cons, hinit,
    quantumMinor_withVectorRow_some, Fin.cons_zero, Fin.cons_succ, Fin.val_succ,
    Nat.add_sub_add_right, hremove]
  simp [withVectorRow, z]

-- The correction to the last-column shift is exactly the commutator of its cofactor with y.
private theorem quantumMinor_vectorRow (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a : Fin n → ι) (b : Fin (n + 1) → ι)
    (hy : ∀ i j k, ⁅y (b k), E (a i) (b j)⁆ = if b k = a i then y (b j) else 0) :
    (withVectorRow E y).quantumMinor u (Fin.cons none (some ∘ a)) (some ∘ b) =
      ∑ j, (-1 : ℤ) ^ j.val • (y (b j) * E.quantumMinor u a (j.removeNth b)) := by
  induction n with
  | zero => simp [withVectorRow]
  | succ n ih =>
    let z := b (Fin.last (n + 1))
    let b₀ := Fin.init b
    let C := E.quantumMinor u a b₀
    let F (i : Fin (n + 1)) := ∑ j : Fin (n + 1), (-1 : ℤ) ^ j.val •
      (y (b₀ j) * E.quantumMinor u (i.removeNth a) (j.removeNth b₀))
    have hF (i : Fin (n + 1)) : (withVectorRow E y).quantumMinor u
        (Fin.cons none (some ∘ i.removeNth a)) (some ∘ b₀) = F i :=
      ih _ _ (fun r j k ↦ hy (i.succAbove r) j.castSucc k.castSucc)
    have hc : ⁅y z, C⁆ = ∑ i, if z = a i then (-1 : ℤ) ^ i.val • F i else 0 := by
      simpa only [hF] using lie_vector_quantumMinor_rows E y u a b₀ z
        (fun i j ↦ hy i j.castSucc (Fin.last (n + 1)))
    have hshift : (∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
        (F i * (if a i = z then 1 else 0))) = -(((-1 : ℤ) ^ (n + 1)) • ⁅y z, C⁆) := by
      rw [hc, Finset.smul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      by_cases h : a i = z
      · simp only [h, ite_true, mul_one, smul_smul, ← neg_smul, cofactor_sign]
      · simp [h, Ne.symm h]
    -- The two expansions differ only in the order of `C` and `y z` and in the final shift.
    have hleft := quantumMinor_vectorRow_succ E y u a b
    have hleft' : (withVectorRow E y).quantumMinor u (Fin.cons none (some ∘ a)) (some ∘ b) =
        (-1 : ℤ) ^ (n + 1) • (C * y z) +
        ∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
          (F i * ((if a i = z then algebraMap K A (u - (↑(n + 1) : K)) else 0) + E (a i) z)) := by
      rw [hleft]
      congr 1
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun x ↦ _ • (x * _)) (hF i)
    have hright : (∑ j, (-1 : ℤ) ^ j.val • (y (b j) * E.quantumMinor u a (j.removeNth b))) =
        (∑ i : Fin (n + 1), (-1 : ℤ) ^ (n - i.val) •
          (F i * ((if a i = z then algebraMap K A (u - (n : K)) else 0) + E (a i) z))) +
          (-1 : ℤ) ^ (n + 1) • (y z * C) := by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last, Fin.removeNth_last]
      exact congrArg (· + (-1 : ℤ) ^ (n + 1) • (y z * C))
        (sum_vector_mul_cofactor_castSucc E y u a b)
    rw [hleft', hright]
    simp_rw [← vectorRow_shift E u n]
    simp only [mul_add, smul_add, Finset.sum_add_distrib]
    rw [hshift, Ring.lie_def, smul_sub]
    abel

/-- The commutator of a vector component with a quantum minor is the sum of the signed
row cofactors for each occurrence of its index. The vector multiplies the cofactors on
the left. This needs only the vector commutation relations on the selected entries, not
the relations among the matrix entries themselves. -/
theorem lie_vector_quantumMinor (E : Matrix ι ι A) (y : ι → A) (u : K)
    {n : ℕ} (a b : Fin (n + 1) → ι) (c : ι)
    (hc : ∀ i j, ⁅E (a i) (b j), y c⁆ = if a i = c then -y (b j) else 0)
    (hy : ∀ i j k, ⁅E (a i) (b j), y (b k)⁆ = if a i = b k then -y (b j) else 0) :
    ⁅y c, E.quantumMinor u a b⁆ = ∑ i, if c = a i then
      ∑ j, (-1 : ℤ) ^ (i.val + j.val) •
        (y (b j) * E.quantumMinor u (i.removeNth a) (j.removeNth b)) else 0 := by
  have skew {k : ι} (h : ∀ i j, ⁅E (a i) (b j), y k⁆ = if a i = k then -y (b j) else 0)
      (i j : Fin (n + 1)) : ⁅y k, E (a i) (b j)⁆ = if k = a i then y (b j) else 0 := by
    rw [← lie_skew, h]
    by_cases h' : a i = k
    · simp [h']
    · simp [h', Ne.symm h']
  rw [lie_vector_quantumMinor_rows E y u a b c (skew hc)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [quantumMinor_vectorRow E y u (i.removeNth a) b
    (fun r j k ↦ skew (fun i j ↦ hy i j k) (i.succAbove r) j)]
  simp only [Finset.smul_sum, smul_smul, ← pow_add]

/-- Moving a vector component through the full quantum determinant subtracts the signed
cofactor row contracted with the vector. The determinant and the cofactors are taken at
the same starting spectral parameter. -/
theorem quantumMinor_id_mul_vector {n : ℕ} (E : Matrix (Fin (n + 1)) (Fin (n + 1)) A)
    (y : Fin (n + 1) → A) (u : K) (c : Fin (n + 1))
    (hy : ∀ i j k, ⁅E i j, y k⁆ = if i = k then -y j else 0) :
    E.quantumMinor u id id * y c = y c * E.quantumMinor u id id -
      ∑ j, (-1 : ℤ) ^ (c.val + j.val) •
        (y j * E.quantumMinor u (c.removeNth id) (j.removeNth id)) := by
  have h := E.lie_vector_quantumMinor y u id id c (fun i j ↦ hy i j c) hy
  rw [Finset.sum_eq_single c] at h
  · simp only [id_eq, ↓reduceIte, Ring.lie_def] at h
    rw [← h]
    abel
  · intro i _ hi
    simp [hi.symm]
  · simp

end Matrix
