/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.Analysis.Matrix.EntrywiseOpNorm
import Mathlib.Tactic.Positivity

/-!
# Hermitian matrices with constant upper entries

`TauCeti.hermitianOffDiagonal c n` has zero diagonal, upper entries `c`, and lower entries
`star c`. These matrices describe the deterministic change caused by centering the upper
entries of a Wigner matrix. For nonreal `c` their ranks need not be bounded.

Partitioning the indices into consecutive blocks gives an approximation of rank at most
twice the number of complete blocks. The error is supported within the blocks, so its squared
Frobenius norm is at most `n * blockSize * ‖c‖²`. The combination of these estimates, rather
than an operator-norm bound on the whole matrix, makes complex centering harmless for weak
spectral limits.

## References

* Z. D. Bai, *Methodologies in spectral analysis of large dimensional random matrices,
  a review*, Statistica Sinica 9 (1999), proof of Theorem 2.1, for complex mean removal.
  Here a block approximation replaces the explicit cotangent eigenvalue calculation.
-/

public section

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius

namespace TauCeti

variable {𝕜 : Type*}

/-- The matrix with upper entries `c`, lower entries `star c`, and zero diagonal.
It is Hermitian for an involutive additive star. -/
def hermitianOffDiagonal [Zero 𝕜] [Star 𝕜] (c : 𝕜) (n : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  .of fun i j ↦ if i < j then c else if j < i then star c else 0

/-- The entry formula for the constant-upper-entry Hermitian matrix. -/
theorem hermitianOffDiagonal_apply [Zero 𝕜] [Star 𝕜] (c : 𝕜) (n : ℕ) (i j : Fin n) :
    hermitianOffDiagonal c n i j = if i < j then c else if j < i then star c else 0 :=
  (rfl)

/-- The diagonal entries vanish. -/
@[simp] theorem hermitianOffDiagonal_apply_self [Zero 𝕜] [Star 𝕜] (c : 𝕜) (n : ℕ) (i : Fin n) :
    hermitianOffDiagonal c n i i = 0 := by
  simp [hermitianOffDiagonal_apply]

/-- Strictly upper entries equal the prescribed scalar. -/
@[simp] theorem hermitianOffDiagonal_apply_of_lt [Zero 𝕜] [Star 𝕜] (c : 𝕜) {n : ℕ} {i j : Fin n}
    (h : i < j) : hermitianOffDiagonal c n i j = c := by
  simp [hermitianOffDiagonal_apply, h]

/-- Strictly lower entries are the conjugate of the prescribed scalar. -/
@[simp] theorem hermitianOffDiagonal_apply_of_gt [Zero 𝕜] [Star 𝕜] (c : 𝕜) {n : ℕ} {i j : Fin n}
    (h : j < i) : hermitianOffDiagonal c n i j = star c := by
  simp [hermitianOffDiagonal_apply, h, h.not_gt]

/-- Constant conjugate upper and lower entries define a Hermitian matrix. -/
theorem isHermitian_hermitianOffDiagonal [AddMonoid 𝕜] [StarAddMonoid 𝕜] (c : 𝕜) (n : ℕ) :
    (hermitianOffDiagonal c n).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, hermitianOffDiagonal_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.not_gt]
  · simp
  · simp [h, h.not_gt]

/-- Zero upper entries give the zero matrix. -/
@[simp] theorem hermitianOffDiagonal_zero [AddMonoid 𝕜] [StarAddMonoid 𝕜] (n : ℕ) :
    hermitianOffDiagonal (0 : 𝕜) n = 0 := by
  ext i j
  simp [hermitianOffDiagonal_apply]

/-- The construction is additive in the upper entry. -/
@[simp] theorem hermitianOffDiagonal_add [AddMonoid 𝕜] [StarAddMonoid 𝕜] (c e : 𝕜) (n : ℕ) :
    hermitianOffDiagonal (c + e) n = hermitianOffDiagonal c n + hermitianOffDiagonal e n := by
  ext i j
  simp only [Matrix.add_apply, hermitianOffDiagonal_apply]
  split_ifs <;> simp

/-- Real scaling commutes with constant-upper-entry Hermitian completion. -/
@[simp] theorem hermitianOffDiagonal_real_smul [AddCommMonoid 𝕜] [StarAddMonoid 𝕜]
    [Module ℝ 𝕜] [StarModule ℝ 𝕜] (r : ℝ) (c : 𝕜) (n : ℕ) :
    hermitianOffDiagonal (r • c) n = r • hermitianOffDiagonal c n := by
  ext i j
  simp only [Matrix.smul_apply, hermitianOffDiagonal_apply]
  split_ifs <;> simp

/-- Subtraction commutes with constant-upper-entry Hermitian completion. -/
@[simp] theorem hermitianOffDiagonal_sub [AddGroup 𝕜] [StarAddMonoid 𝕜] (c e : 𝕜) (n : ℕ) :
    hermitianOffDiagonal (c - e) n = hermitianOffDiagonal c n - hermitianOffDiagonal e n := by
  ext i j
  simp only [Matrix.sub_apply, hermitianOffDiagonal_apply]
  split_ifs <;> simp

/-- Every entry has norm at most the norm of the upper entry. -/
theorem norm_hermitianOffDiagonal_apply_le [SeminormedAddCommGroup 𝕜] [StarAddMonoid 𝕜]
    [NormedStarGroup 𝕜] (c : 𝕜) (n : ℕ) (i j : Fin n) :
    ‖hermitianOffDiagonal c n i j‖ ≤ ‖c‖ := by
  simp only [hermitianOffDiagonal_apply]
  split_ifs <;> simp

open scoped Matrix.Norms.L2Operator in
/-- The Euclidean operator norm of a constant Hermitian off-diagonal completion is
at most the dimension times the absolute value of the coefficient. -/
theorem l2_opNorm_hermitianOffDiagonal_le [RCLike 𝕜] (c : 𝕜) (n : ℕ) :
    ‖hermitianOffDiagonal c n‖ ≤ n * ‖c‖ := by
  apply (isHermitian_hermitianOffDiagonal c n).l2_opNorm_le_of_row_sum_le (by positivity)
  intro i
  calc
    _ ≤ ∑ _j : Fin n, ‖c‖ :=
      Finset.sum_le_sum fun j _ ↦ norm_hermitianOffDiagonal_apply_le c n i j
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable [RCLike 𝕜]

private def blockIndex (n d : ℕ) (i : Fin n) : Fin (n / (d + 1) + 1) :=
  ⟨i.val / (d + 1), Nat.lt_succ_of_le (Nat.div_le_div_right i.isLt.le)⟩

private theorem blockIndex_mono (n d : ℕ) : Monotone (blockIndex n d) := by
  intro i j hij
  exact Nat.div_le_div_right hij

private def blockApproximation (c : 𝕜) (n d : ℕ) : Matrix (Fin n) (Fin n) 𝕜 :=
  (hermitianOffDiagonal c (n / (d + 1) + 1)).submatrix (blockIndex n d) (blockIndex n d)

private theorem isHermitian_blockApproximation (c : 𝕜) (n d : ℕ) :
    (blockApproximation c n d).IsHermitian :=
  (isHermitian_hermitianOffDiagonal c _).submatrix _

private theorem rank_blockApproximation_le (c : 𝕜) (n d : ℕ) :
    (blockApproximation c n d).rank ≤ 2 * (n / (d + 1)) := by
  by_cases h : n / (d + 1) = 0
  · have heq : blockApproximation c n d = 0 := by
      ext i j
      have hi : blockIndex n d i = 0 := Fin.ext (by
        exact Nat.le_zero.mp (h ▸ Nat.div_le_div_right (c := d + 1) i.isLt.le))
      have hj : blockIndex n d j = 0 := Fin.ext (by
        exact Nat.le_zero.mp (h ▸ Nat.div_le_div_right (c := d + 1) j.isLt.le))
      simp [blockApproximation, hi, hj]
    simp [heq, h]
  · exact ((rank_submatrix_le _ _ _).trans (rank_le_card_width _)).trans (by
      simp only [Fintype.card_fin]
      omega)

private theorem blockApproximation_eq_of_ne (c : 𝕜) {n d : ℕ} {i j : Fin n}
    (h : blockIndex n d i ≠ blockIndex n d j) :
    blockApproximation c n d i j = hermitianOffDiagonal c n i j := by
  rcases lt_or_gt_of_ne h with hij | hji
  · have hlt : i < j := lt_of_not_ge fun hji ↦ hij.not_ge (blockIndex_mono n d hji)
    simp [blockApproximation, hij, hlt]
  · have hlt : j < i := lt_of_not_ge fun hij ↦ hji.not_ge (blockIndex_mono n d hij)
    simp [blockApproximation, hji, hlt]

private theorem norm_block_error_apply_le (c : 𝕜) (n d : ℕ) (i j : Fin n) :
    ‖(hermitianOffDiagonal c n - blockApproximation c n d) i j‖ ^ 2 ≤
      if blockIndex n d i = blockIndex n d j then ‖c‖ ^ 2 else 0 := by
  by_cases h : blockIndex n d i = blockIndex n d j
  · simp only [h, ↓reduceIte, Matrix.sub_apply]
    have hz : blockApproximation c n d i j = 0 := by
      simp [blockApproximation, h]
    rw [hz, sub_zero]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_hermitianOffDiagonal_apply_le c n i j) 2
  · simp [h, Matrix.sub_apply, blockApproximation_eq_of_ne c h]

private theorem card_block_fiber_le (n d : ℕ) (i : Fin n) :
    (Finset.univ.filter fun j : Fin n ↦ blockIndex n d i = blockIndex n d j).card ≤ d + 1 := by
  have hcard := Finset.card_le_card_of_injOn (fun j : Fin n ↦ j.val % (d + 1))
    (s := Finset.univ.filter fun j : Fin n ↦ blockIndex n d i = blockIndex n d j)
    (t := Finset.range (d + 1))
    (fun j _ ↦ Finset.mem_range.mpr (Nat.mod_lt _ (Nat.succ_pos d)))
    (fun j hj k hk heq ↦ ?_)
  · simpa using hcard
  · have hj' := congrArg Fin.val (Finset.mem_filter.mp hj).2
    have hk' := congrArg Fin.val (Finset.mem_filter.mp hk).2
    dsimp [blockIndex] at hj' hk'
    dsimp at heq
    apply Fin.ext
    calc
      j.val = j.val % (d + 1) + (d + 1) * (j.val / (d + 1)) :=
        (Nat.mod_add_div _ _).symm
      _ = k.val % (d + 1) + (d + 1) * (k.val / (d + 1)) := by
        rw [heq, hj'.symm.trans hk']
      _ = k.val := Nat.mod_add_div _ _

private theorem frobenius_norm_block_error_sq_le (c : 𝕜) (n d : ℕ) :
    ‖hermitianOffDiagonal c n - blockApproximation c n d‖ ^ 2 ≤
      (n : ℝ) * (d + 1) * ‖c‖ ^ 2 := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity)]
  simp only [Real.rpow_two]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        if blockIndex n d i = blockIndex n d j then ‖c‖ ^ 2 else 0 :=
      Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ norm_block_error_apply_le c n d i j
    _ ≤ ∑ _i : Fin n, (d + 1 : ℝ) * ‖c‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_block_fiber_le n d i)
        (sq_nonneg _)
    _ = _ := by simp [mul_assoc]

/-- A constant-upper-entry Hermitian matrix admits a low-rank block approximation whose
squared Frobenius error is at most `n * (d + 1) * ‖c‖²`. The rank bound also covers `n ≤ d`,
when the approximation is zero. Empty matrices and zero upper entries are allowed. -/
theorem exists_isHermitian_rank_le_frobenius_norm_sub_sq_le_hermitianOffDiagonal
    (c : 𝕜) (n d : ℕ) :
    ∃ B : Matrix (Fin n) (Fin n) 𝕜, B.IsHermitian ∧ B.rank ≤ 2 * (n / (d + 1)) ∧
      ‖hermitianOffDiagonal c n - B‖ ^ 2 ≤ (n : ℝ) * (d + 1) * ‖c‖ ^ 2 :=
  ⟨blockApproximation c n d, isHermitian_blockApproximation c n d,
    rank_blockApproximation_le c n d, frobenius_norm_block_error_sq_le c n d⟩

end TauCeti
