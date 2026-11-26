/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.Spectrum
public import TauCeti.LinearAlgebra.Matrix.NonBacktracking
import Mathlib.Tactic.NoncommRing
import TauCeti.Analysis.Matrix.Eigenvalues.Basic
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.NonBacktracking
import TauCeti.Data.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Block

/-!
# Non-backtracking bounds for the spectrum of a sample covariance matrix

Let `Y` be a `p × n` matrix whose entries are small, whose rows have squared norms close to `1`
and whose columns have squared norms close to `c ≤ 1`. This is the situation of `Y = X / √n` for a
matrix `X` of standardized entries with `p / n ≈ c`, where `Y * Yᴴ` is the sample covariance
matrix `X * Xᴴ / n`. This file shows that the spectrum of `Y * Yᴴ` then lies close to
`[(1 - √c) ^ 2, (1 + √c) ^ 2]`, the support of the Marchenko–Pastur law of ratio `c`, as soon as
the non-backtracking walk matrices of `Y` grow at the rate `√c`. This is the deterministic part of
Bai and Yin's proof that the smallest eigenvalue of a sample covariance matrix tends to
`(1 - √c) ^ 2`.

The walks live on the Hermitian dilation `H = [[0, Y], [Yᴴ, 0]]`, the weighted bipartite graph
between rows and columns. Let `T l` be the row block of `Matrix.nonbacktrackingPow H (2 * l)`.
Since `H` vanishes on its diagonal blocks, only walks alternating between rows and columns carry
weight in the walk sums of `Matrix.nonbacktrackingPow_apply`, so informally `T l` sums the products
`Y a₀ v₁ * conj (Y a₁ v₁) * Y a₁ v₂ * ⋯ * conj (Y a_l v_l)` over the alternating paths that
never step straight back; these are the matrices `T(l)` of Bai and Yin. The results below use
`T l` only through its definition as a block. Applying the non-backtracking recursion
`Matrix.nonbacktrackingPow_add_two` twice, and using that `H` exchanges the row and column blocks,
gives for `M = Y * Yᴴ - (1 + c)` the Chebyshev recursion `M * T 0 ≈ T 1 - c • T 0` and
`M * T (l + 1) ≈ T (l + 2) + c • T l`. Its errors come from the deviation of the squared row and
column norms from `1` and `c`, and from the walks that traverse an edge three times in a row,
whose contributions `Matrix.tendsto_l2_opNorm_nonbacktrackingCorrection` shows to be negligible
when the entries are small. If `‖T l‖ ≤ C * (l + 1) ^ d * √c ^ l`, iterating the recursion bounds
`‖M ^ k‖` by `C * (k + 1) ^ d * (2 * √c) ^ k` up to small errors, and
`‖M‖ ^ (2 ^ m) = ‖M ^ (2 ^ m)‖` for the Hermitian matrix `M` turns this into `‖M‖ ≤ 2 * √c`
asymptotically.

## Main results

* `Matrix.eventually_l2_opNorm_mul_conjTranspose_sub_smul_one_le`: along a filter, if the entries
  of `Y` tend to zero and its squared row and column norms tend to `1` and `c ≤ 1` uniformly, and
  `‖T l‖ ≤ C * (l + 1) ^ d * √c ^ l` eventually for each `l`, then
  `‖Y * Yᴴ - (1 + c)‖ ≤ 2 * √c + ε` eventually, for every `ε > 0`.
* `Matrix.eventually_eigenvalues₀_mul_conjTranspose_mem_Icc`: under the same hypotheses, all
  eigenvalues of `Y * Yᴴ` eventually lie in `[(1 - √c) ^ 2 - ε, (1 + √c) ^ 2 + ε]`.

## References

* Z. D. Bai and Y. Q. Yin, *Limit of the smallest eigenvalue of a large dimensional sample
  covariance matrix*, Ann. Probab. 21 (1993), 1275–1294.
* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*, 2nd ed.,
  Springer, 2010, §5.2.
-/

public section

open Finset Filter
open scoped Matrix.Norms.L2Operator NNReal

namespace Matrix

variable {𝕜 p n : Type*} [RCLike 𝕜] [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n]

section Dilation

variable (Y : Matrix p n 𝕜) (c : ℝ)

/-- The two-step identity behind the even recursion: if `b₀, …, b₄` in a ring satisfy the one-step
recursion `bⱼ₊₂ = H * bⱼ₊₁ - D * bⱼ + eⱼ`, then `H * H * b₂` is
`b₄ + (D₀ + D₀') * b₂ + D₀' * D₀ * b₀` up to the commutator term `(H * D₀ - D₀' * H) * b₁` and
explicit errors. -/
private theorem mul_mul_eq_add {A : Type*} [Ring A] {H D D₀ D₀' b₀ b₁ b₂ b₃ b₄ e₀ e₁ e₂ : A}
    (h₀ : b₂ = H * b₁ - D * b₀ + e₀) (h₁ : b₃ = H * b₂ - D * b₁ + e₁)
    (h₂ : b₄ = H * b₃ - D * b₂ + e₂) :
    H * H * b₂ = b₄ + (D₀ + D₀') * b₂ + D₀' * D₀ * b₀ + (H * D₀ - D₀' * H) * b₁ +
      ((D - D₀) * b₂ + D₀' * ((D - D₀) * b₀) + H * ((D - D₀) * b₁) - e₂ - D₀' * e₀ - H * e₁) := by
  subst h₂ h₁ h₀
  noncomm_ring

/-- A bound on the error term of the two-step identity `mul_mul_eq_add`: the triangle inequality on
its six summands, then submultiplicativity, with `‖D₀'‖ ≤ 1`. -/
private theorem norm_sub_sub_sub_le {A : Type*} [NormedRing A] {D D₀ D₀' H b₀ b₁ b₂ e₀ e₁ e₂ : A}
    (hD₀' : ‖D₀'‖ ≤ 1) :
    ‖(D - D₀) * b₂ + D₀' * ((D - D₀) * b₀) + H * ((D - D₀) * b₁) - e₂ - D₀' * e₀ - H * e₁‖ ≤
      ‖D - D₀‖ * (‖b₂‖ + ‖b₀‖ + ‖H‖ * ‖b₁‖) + ‖e₂‖ + ‖e₀‖ + ‖H‖ * ‖e₁‖ := by
  calc _ ≤ ‖(D - D₀) * b₂‖ + ‖D₀' * ((D - D₀) * b₀)‖ + ‖H * ((D - D₀) * b₁)‖ + ‖e₂‖ +
        ‖D₀' * e₀‖ + ‖H * e₁‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact norm_add₃_le
    _ ≤ ‖D - D₀‖ * ‖b₂‖ + 1 * (‖D - D₀‖ * ‖b₀‖) + ‖H‖ * (‖D - D₀‖ * ‖b₁‖) + ‖e₂‖ +
        1 * ‖e₀‖ + ‖H‖ * ‖e₁‖ := by
        gcongr
        · exact norm_mul_le _ _
        · exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        · exact (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
        · exact (norm_mul_le _ _).trans (by gcongr)
        · exact norm_mul_le _ _
    _ = _ := by ring

/-- The diagonal matrix `diag(a, …, a, b, …, b)` with `a` on the rows and `b` on the columns. -/
private abbrev blockScalar (a b : 𝕜) : Matrix (p ⊕ n) (p ⊕ n) 𝕜 :=
  diagonal (Sum.elim (fun _ ↦ a) fun _ ↦ b)

/-- Multiplying the dilation by `diag(a, b)` on the right is multiplying it by `diag(b, a)` on the
left: the dilation exchanges rows and columns. -/
private theorem fromBlocks_zero_mul_blockScalar (a b : 𝕜) :
    fromBlocks 0 Y Yᴴ 0 * blockScalar (p := p) (n := n) a b =
      blockScalar b a * fromBlocks 0 Y Yᴴ 0 := by
  ext (x | x) (y | y) <;> simp [blockScalar, mul_comm]

omit [Fintype p] [Fintype n] in
/-- `diag(1, c) + diag(c, 1) = (1 + c) • 1`. -/
private theorem blockScalar_add_blockScalar :
    blockScalar (p := p) (n := n) (1 : 𝕜) c + blockScalar (c : 𝕜) 1 =
      (1 + c) • (1 : Matrix (p ⊕ n) (p ⊕ n) 𝕜) := by
  ext (x | x) (y | y) <;> simp only [blockScalar, Matrix.add_apply, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp [RCLike.real_smul_eq_coe_mul, add_comm]

/-- `diag(c, 1) * diag(1, c) = c • 1`. -/
private theorem blockScalar_mul_blockScalar :
    blockScalar (p := p) (n := n) (c : 𝕜) 1 * blockScalar (p := p) (n := n) (1 : 𝕜) c =
      c • (1 : Matrix (p ⊕ n) (p ⊕ n) 𝕜) := by
  ext (x | x) (y | y) <;> simp only [blockScalar, diagonal_mul_diagonal, Matrix.smul_apply,
    Matrix.diagonal_apply, Matrix.one_apply, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp [RCLike.real_smul_eq_coe_mul]

omit [Fintype p] [Fintype n] in
/-- The upper left block of `diag(a, b)` is `a` times the identity. -/
private theorem toBlocks₁₁_blockScalar (a b : 𝕜) :
    (blockScalar (p := p) (n := n) a b).toBlocks₁₁ = a • 1 := by
  simp [blockScalar, smul_one_eq_diagonal]

/-- `diag(c, 1)` has operator norm at most `1` for `0 ≤ c ≤ 1`. -/
private theorem norm_blockScalar_le {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    ‖blockScalar (p := p) (n := n) (c : 𝕜) 1‖ ≤ 1 := by
  refine l2_opNorm_diagonal_le zero_le_one fun x ↦ ?_
  rcases x with a | v <;> simp [abs_of_nonneg hc₀, hc₁]

omit [DecidableEq p] [DecidableEq n] in
/-- The squared norms of the rows of the dilation are those of the rows and columns of `Y`. -/
private theorem sum_norm_fromBlocks_zero_sq (x : p ⊕ n) :
    ∑ y, ‖fromBlocks 0 Y Yᴴ 0 x y‖ ^ 2 =
      Sum.elim (fun a ↦ ∑ v, ‖Y a v‖ ^ 2) (fun v ↦ ∑ a, ‖Y a v‖ ^ 2) x := by
  rcases x with a | v <;> simp [Fintype.sum_sum_type]

omit [DecidableEq p] [DecidableEq n] in
/-- The degrees `(H * H) x x = ∑ w, H x w * H w x` of the dilation are the squared row norms. -/
private theorem diag_fromBlocks_zero_mul_self_apply (x : p ⊕ n) :
    (fromBlocks 0 Y Yᴴ 0 * fromBlocks 0 Y Yᴴ 0).diag x =
      ((∑ y, ‖fromBlocks 0 Y Yᴴ 0 x y‖ ^ 2 : ℝ) : 𝕜) := by
  have hH : (fromBlocks 0 Y Yᴴ 0).IsHermitian :=
    IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero
  rw [diag_apply, Matrix.mul_apply]
  push_cast
  refine sum_congr rfl fun w _ ↦ ?_
  rw [← hH.apply w x, RCLike.star_def, RCLike.mul_conj]

/-- `Y * Yᴴ` is the upper left block of `H * H = B 2 + D` for the dilation `H`, with
`D = diagonal (H * H).diag`. -/
private theorem mul_conjTranspose_eq_toBlocks₁₁_add :
    Y * Yᴴ = (nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) 2).toBlocks₁₁ +
      (diagonal (fromBlocks 0 Y Yᴴ 0 * fromBlocks 0 Y Yᴴ 0).diag).toBlocks₁₁ := by
  rw [← toBlocks₁₁_add, nonbacktrackingPow_two, sub_add_cancel, fromBlocks_multiply,
    toBlocks_fromBlocks₁₁, Matrix.zero_mul, zero_add]

/-- **The first step of the row recursion.** For `M = Y * Yᴴ - (1 + c)`, the row block `T` of the
non-backtracking walk matrices of the dilation satisfies `M * T 0 = T 1 - c • T 0` up to the
deviation of the degrees from `diag(1, c)`. -/
private theorem norm_mul_toBlocks₁₁_nonbacktrackingPow_zero_sub_le :
    ‖(Y * Yᴴ - (1 + c) • 1) * (nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) 0).toBlocks₁₁ -
        ((nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) 2).toBlocks₁₁ -
          c • (nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) 0).toBlocks₁₁)‖ ≤
      ‖diagonal (fromBlocks 0 Y Yᴴ 0 * fromBlocks 0 Y Yᴴ 0).diag - blockScalar 1 (c : 𝕜)‖ := by
  set H := fromBlocks 0 Y Yᴴ 0
  have hYY := mul_conjTranspose_eq_toBlocks₁₁_add Y
  have h : (Y * Yᴴ - (1 + c) • 1) * (nonbacktrackingPow H 0).toBlocks₁₁ -
      ((nonbacktrackingPow H 2).toBlocks₁₁ - c • (nonbacktrackingPow H 0).toBlocks₁₁) =
      (diagonal (H * H).diag - blockScalar 1 (c : 𝕜)).toBlocks₁₁ := by
    rw [nonbacktrackingPow_zero, toBlocks₁₁_one, Matrix.mul_one, toBlocks₁₁_sub,
      toBlocks₁₁_blockScalar, one_smul, hYY, add_smul, one_smul]
    abel
  rw [h, toBlocks₁₁_eq_submatrix]
  exact l2_opNorm_submatrix_le _ Sum.inl_injective Sum.inl_injective

/-- **The later steps of the row recursion.** For `M = Y * Yᴴ - (1 + c)` and the row block `T` of
the non-backtracking walk matrices `B` of the dilation `H`,
`M * T (k + 2) = T (k + 4) + c • T k` up to the deviation of the degrees
`D = diagonal (H * H).diag` from `diag(1, c)` and the corrections `E` of the non-backtracking
recursion `Matrix.nonbacktrackingPow_add_two`, with `0 ≤ c ≤ 1`. -/
private theorem norm_mul_toBlocks₁₁_nonbacktrackingPow_add_two_sub_le {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) (k : ℕ) :
    ‖(Y * Yᴴ - (1 + c) • 1) * (nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) (k + 2)).toBlocks₁₁ -
        ((nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) (k + 4)).toBlocks₁₁ +
          c • (nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) k).toBlocks₁₁)‖ ≤
      ‖diagonal (fromBlocks 0 Y Yᴴ 0 * fromBlocks 0 Y Yᴴ 0).diag - blockScalar 1 (c : 𝕜)‖ *
          (‖nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) (k + 2)‖ +
            ‖nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) k‖ +
            ‖fromBlocks 0 Y Yᴴ 0‖ * ‖nonbacktrackingPow (fromBlocks 0 Y Yᴴ 0) (k + 1)‖) +
        ‖nonbacktrackingCorrection (fromBlocks 0 Y Yᴴ 0) (k + 2)‖ +
        ‖nonbacktrackingCorrection (fromBlocks 0 Y Yᴴ 0) k‖ +
        ‖fromBlocks 0 Y Yᴴ 0‖ * ‖nonbacktrackingCorrection (fromBlocks 0 Y Yᴴ 0) (k + 1)‖ := by
  set H := fromBlocks 0 Y Yᴴ 0
  set B := nonbacktrackingPow H
  set D := diagonal (H * H).diag
  set E := nonbacktrackingCorrection H
  set D₀ : Matrix (p ⊕ n) (p ⊕ n) 𝕜 := blockScalar 1 (c : 𝕜)
  set D₀' : Matrix (p ⊕ n) (p ⊕ n) 𝕜 := blockScalar (c : 𝕜) 1
  have key := mul_mul_eq_add (D₀ := D₀) (D₀' := D₀') (b₃ := B (k + 3)) (b₄ := B (k + 4))
    (nonbacktrackingPow_add_two H k) (nonbacktrackingPow_add_two H (k + 1))
    (nonbacktrackingPow_add_two H (k + 2))
  rw [blockScalar_add_blockScalar, blockScalar_mul_blockScalar, fromBlocks_zero_mul_blockScalar,
    sub_self, zero_mul, add_zero, smul_mul_assoc, smul_mul_assoc, Matrix.one_mul,
    Matrix.one_mul] at key
  set Δ := (D - D₀) * B (k + 2) + D₀' * ((D - D₀) * B k) + H * ((D - D₀) * B (k + 1)) -
    E (k + 2) - D₀' * E k - H * E (k + 1)
  have hfull : H * H * B (k + 2) = B (k + 4) + (1 + c) • B (k + 2) + c • B k + Δ := key
  -- Take the upper left block of the two-step identity.
  have hT : Y * Yᴴ * (B (k + 2)).toBlocks₁₁ = (B (k + 4)).toBlocks₁₁ +
      (1 + c) • (B (k + 2)).toBlocks₁₁ + c • (B k).toBlocks₁₁ + Δ.toBlocks₁₁ := by
    have hHH : (H * H * B (k + 2)).toBlocks₁₁ = Y * Yᴴ * (B (k + 2)).toBlocks₁₁ := by
      rw [fromBlocks_multiply, toBlocks₁₁_mul]
      simp
    rw [← hHH, hfull]
    simp only [toBlocks₁₁_add, toBlocks₁₁_smul]
  have hdef : (Y * Yᴴ - (1 + c) • 1) * (B (k + 2)).toBlocks₁₁ -
      ((B (k + 4)).toBlocks₁₁ + c • (B k).toBlocks₁₁) = Δ.toBlocks₁₁ := by
    rw [sub_mul, smul_mul_assoc, Matrix.one_mul, hT]
    abel
  rw [hdef, toBlocks₁₁_eq_submatrix]
  exact (l2_opNorm_submatrix_le _ Sum.inl_injective Sum.inl_injective).trans
    (norm_sub_sub_sub_le (norm_blockScalar_le hc₀ hc₁))

/-- The degrees of the dilation are within `ε` of `diag(1, c)` when the squared row norms of `Y`
are within `ε` of `1` and its squared column norms within `ε` of `c`. -/
private theorem norm_diagonal_diag_sub_blockScalar_le {ε : ℝ} (hε : 0 ≤ ε)
    (hr : ∀ a, |∑ v, ‖Y a v‖ ^ 2 - 1| ≤ ε) (hc : ∀ v, |∑ a, ‖Y a v‖ ^ 2 - c| ≤ ε) :
    ‖diagonal (fromBlocks 0 Y Yᴴ 0 * fromBlocks 0 Y Yᴴ 0).diag - blockScalar 1 (c : 𝕜)‖ ≤ ε := by
  rw [blockScalar, diagonal_sub]
  refine l2_opNorm_diagonal_le hε fun x ↦ ?_
  rw [diag_fromBlocks_zero_mul_self_apply, sum_norm_fromBlocks_zero_sq]
  rcases x with a | v
  · simp only [Sum.elim_inl]
    rw [← RCLike.ofReal_one, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact hr a
  · simp only [Sum.elim_inr]
    rw [← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact hc v

omit [DecidableEq p] [DecidableEq n] in
/-- The rows of the dilation have squared norms at most `2` when those of `Y` are at most `2` and
the columns at most `2`. -/
private theorem sum_norm_fromBlocks_zero_sq_le (hr : ∀ a, ∑ v, ‖Y a v‖ ^ 2 ≤ 2)
    (hc : ∀ v, ∑ a, ‖Y a v‖ ^ 2 ≤ 2) (x : p ⊕ n) : ∑ y, ‖fromBlocks 0 Y Yᴴ 0 x y‖ ^ 2 ≤ 2 := by
  rw [sum_norm_fromBlocks_zero_sq]
  rcases x with a | v
  exacts [hr a, hc v]

omit [Fintype p] [Fintype n] [DecidableEq p] [DecidableEq n] in
/-- The entries of the dilation are those of `Y`, their conjugates and zeros. -/
private theorem norm_fromBlocks_zero_apply_le {ε : ℝ} (hε : 0 ≤ ε) (hY : ∀ a v, ‖Y a v‖ ≤ ε)
    (x y : p ⊕ n) : ‖fromBlocks 0 Y Yᴴ 0 x y‖ ≤ ε := by
  rcases x with a | v <;> rcases y with b | w <;> simp [hε, hY]

/-- A bound `K` on `‖Y * Yᴴ‖` bounds the dilation by `2 * max 1 K`. -/
private theorem l2_opNorm_fromBlocks_zero_le_of_le {K : ℝ} (hK : ‖Y * Yᴴ‖ ≤ K) :
    ‖fromBlocks 0 Y Yᴴ 0‖ ≤ 2 * max 1 K := by
  rw [l2_opNorm_mul_conjTranspose_self] at hK
  have hY : ‖Y‖ ≤ max 1 K := by
    by_cases h1 : ‖Y‖ ≤ 1
    · exact h1.trans (le_max_left _ _)
    · exact (le_mul_of_one_le_left (norm_nonneg _) (le_of_not_ge h1)).trans (hK.trans
        (le_max_right _ _))
  calc _ ≤ ‖Y‖ + ‖Yᴴ‖ := l2_opNorm_fromBlocks_zero₁₁_zero₂₂_le Y Yᴴ
    _ ≤ 2 * max 1 K := by rw [l2_opNorm_conjTranspose]; linarith

omit [DecidableEq n] in
/-- A bound `K` on `‖Y * Yᴴ‖` bounds `Y * Yᴴ - (1 + c)` by `K + 2` for `0 ≤ c ≤ 1`. -/
private theorem l2_opNorm_mul_conjTranspose_sub_smul_one_le {K : ℝ}
    (hK : ‖Y * Yᴴ‖ ≤ K) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    ‖Y * Yᴴ - (1 + c) • 1‖ ≤ K + 2 := by
  have h1 : ‖(1 + c) • (1 : Matrix p p 𝕜)‖ ≤ 2 := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (by linarith)]
    nlinarith [l2_opNorm_one_le (n := p) (𝕜 := 𝕜), norm_nonneg (1 : Matrix p p 𝕜)]
  exact (norm_sub_le _ _).trans (add_le_add hK h1)

end Dilation

section Asymptotics

variable {ι : Type*} {F : Filter ι}

omit [Fintype p] [DecidableEq p] in
/-- One step of a three-term recursion: `M ^ (k + 1) * X` is `M ^ k * Y + s • (M ^ k * Z)` up to
`M ^ k` applied to the error of `M * X ≈ Y + s • Z`. -/
private theorem l2_opNorm_pow_succ_mul_le {m : Type*} [Fintype m] [DecidableEq m]
    (M X Y Z : Matrix m m 𝕜) (s : ℝ) (k : ℕ) :
    ‖M ^ (k + 1) * X‖ ≤ ‖M ^ k * Y‖ + |s| * ‖M ^ k * Z‖ + ‖M‖ ^ k * ‖M * X - (Y + s • Z)‖ := by
  have hsplit : M ^ (k + 1) * X = M ^ k * Y + s • (M ^ k * Z) + M ^ k * (M * X - (Y + s • Z)) := by
    rw [pow_succ, Matrix.mul_assoc, mul_sub, mul_add, Matrix.mul_smul]
    abel
  rw [hsplit]
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans_eq ?_)
    ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (l2_opNorm_pow_le _ k) (norm_nonneg _))))
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), norm_smul, RCLike.norm_ofReal]

/-- The bound `C * (j + k + 1) ^ d * ρ ^ j * σ ^ k`, with `σ = ρ + c / ρ`, absorbs one step of the
recursion `M * T (j + 1) ≈ T (j + 2) + c • T j`, since
`ρ ^ (j + 2) + c * ρ ^ j = ρ ^ (j + 1) * σ`. -/
private theorem bound_add_two_add_mul_bound_le {C ρ c : ℝ} {d : ℕ} (hC : 0 ≤ C) (hρ : 0 < ρ)
    (hc : 0 ≤ c) (j k : ℕ) :
    C * (((j + 2 : ℕ) : ℝ) + k + 1) ^ d * ρ ^ (j + 2) * (ρ + c / ρ) ^ k +
        c * (C * ((j : ℝ) + k + 1) ^ d * ρ ^ j * (ρ + c / ρ) ^ k) ≤
      C * (((j + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) + 1) ^ d * ρ ^ (j + 1) *
        (ρ + c / ρ) ^ (k + 1) := by
  have hρσ : ρ * (ρ + c / ρ) = ρ ^ 2 + c := by field_simp
  set σ := ρ + c / ρ
  set X : ℝ := (j : ℝ) + k + 3
  have hQ : ((j : ℝ) + k + 1) ^ d ≤ X ^ d := by gcongr; simp only [X]; linarith
  have hc' : c * (C * ((j : ℝ) + k + 1) ^ d * ρ ^ j * σ ^ k) ≤ c * (C * X ^ d * ρ ^ j * σ ^ k) := by
    gcongr
  have e1 : (((j + 2 : ℕ) : ℝ) + k + 1) = X := by push_cast; ring
  have e2 : (((j + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) + 1) = X := by push_cast; ring
  have e3 : C * X ^ d * ρ ^ (j + 1) * σ ^ (k + 1) = C * X ^ d * ρ ^ j * σ ^ k * (ρ * σ) := by ring
  have e4 : C * X ^ d * ρ ^ (j + 2) * σ ^ k = C * X ^ d * ρ ^ j * σ ^ k * ρ ^ 2 := by ring
  rw [e1, e2, e3, e4, hρσ]
  linarith

/-- At `j = 0` the recursion is `M * T 0 ≈ T 1 - c • T 0`, and the bound absorbs the step because
`ρ + c ≤ ρ + c / ρ` for `ρ ≤ 1`. -/
private theorem bound_one_add_mul_bound_le {C ρ c : ℝ} {d : ℕ} (hC : 0 ≤ C) (hρ₀ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (hc : 0 ≤ c) (k : ℕ) :
    C * (((1 : ℕ) : ℝ) + k + 1) ^ d * ρ ^ 1 * (ρ + c / ρ) ^ k +
        c * (C * (((0 : ℕ) : ℝ) + k + 1) ^ d * ρ ^ 0 * (ρ + c / ρ) ^ k) ≤
      C * (((0 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) + 1) ^ d * ρ ^ 0 * (ρ + c / ρ) ^ (k + 1) := by
  have hρc : ρ + c ≤ ρ + c / ρ := by linarith [le_div_self hc hρ₀ hρ₁]
  set σ := ρ + c / ρ
  have hQ : ((k : ℝ) + 1) ^ d ≤ ((k : ℝ) + 2) ^ d := by gcongr; linarith
  have hP : 0 ≤ C * ((k : ℝ) + 2) ^ d * σ ^ k := by positivity
  have hc' : c * (C * ((k : ℝ) + 1) ^ d * σ ^ k) ≤ c * (C * ((k : ℝ) + 2) ^ d * σ ^ k) := by
    gcongr
  have hσ' := mul_le_mul_of_nonneg_left hρc hP
  have e1 : (((1 : ℕ) : ℝ) + k + 1) = (k : ℝ) + 2 := by push_cast; ring
  have e2 : (((0 : ℕ) : ℝ) + k + 1) = (k : ℝ) + 1 := by push_cast; ring
  have e3 : (((0 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 := by push_cast; ring
  rw [e1, e2, e3, pow_zero, pow_one, mul_one, mul_one, pow_succ]
  nlinarith

omit [Fintype p] [DecidableEq p] in
/-- **Powers through an approximate three-term recursion.** Let `0 ≤ c`, `0 < ρ ≤ 1` and
`σ = ρ + c / ρ`. Suppose that, along a filter, `‖M‖` is eventually bounded, each `T j` eventually
has norm at most `C * (j + 1) ^ d * ρ ^ j`, and the recursion `M * T 0 = T 1 - c • T 0`,
`M * T (j + 1) = T (j + 2) + c • T j` holds up to errors tending to zero. Then for all `k` and `j`,
eventually `‖M ^ k * T j‖ ≤ C * (j + k + 1) ^ d * ρ ^ j * σ ^ k + δ`, for every `δ > 0`. -/
private theorem eventually_l2_opNorm_pow_mul_le {m : ι → Type*} [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] {M : (i : ι) → Matrix (m i) (m i) 𝕜}
    {T : (i : ι) → ℕ → Matrix (m i) (m i) 𝕜} {c ρ C R : ℝ} {d : ℕ} (hc : 0 ≤ c) (hρ₀ : 0 < ρ)
    (hρ₁ : ρ ≤ 1) (hC : 0 ≤ C) (hR : 0 ≤ R) (hM : ∀ᶠ i in F, ‖M i‖ ≤ R)
    (hT : ∀ j, ∀ᶠ i in F, ‖T i j‖ ≤ C * ((j : ℝ) + 1) ^ d * ρ ^ j)
    (h0 : ∀ δ > 0, ∀ᶠ i in F, ‖M i * T i 0 - (T i 1 - c • T i 0)‖ ≤ δ)
    (hs : ∀ j, ∀ δ > 0, ∀ᶠ i in F, ‖M i * T i (j + 1) - (T i (j + 2) + c • T i j)‖ ≤ δ)
    (k j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in F, ‖M i ^ k * T i j‖ ≤
      C * ((j : ℝ) + k + 1) ^ d * ρ ^ j * (ρ + c / ρ) ^ k + δ := by
  induction k generalizing j δ with
  | zero =>
    filter_upwards [hT j] with i hi
    simp only [pow_zero, Matrix.one_mul, mul_one, Nat.cast_zero, add_zero]
    linarith
  | succ k ih =>
    -- Split the error budget between the two earlier bounds and the recursion error.
    set δ₁ := δ / (2 * (1 + c))
    set δ₂ := δ / (2 * (R ^ k + 1))
    have hδ₁ : 0 < δ₁ := by positivity
    have hδ₂ : 0 < δ₂ := by positivity
    have herr : δ₁ + c * δ₁ + R ^ k * δ₂ ≤ δ := by
      have h1 : δ₁ + c * δ₁ = δ / 2 := by simp only [δ₁]; field_simp
      have h2 : R ^ k * δ₂ ≤ δ / 2 := by
        simp only [δ₂]
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) two_pos]
        nlinarith [pow_nonneg hR k]
      linarith
    rcases j with _ | j
    · filter_upwards [ih 1 hδ₁, ih 0 hδ₁, h0 δ₂ hδ₂, hM] with i h1 h0' hd hMi
      have hstep := l2_opNorm_pow_succ_mul_le (M i) (T i 0) (T i 1) (T i 0) (-c) k
      rw [neg_smul, ← sub_eq_add_neg, abs_neg, abs_of_nonneg hc] at hstep
      have hMk : ‖M i‖ ^ k * ‖M i * T i 0 - (T i 1 - c • T i 0)‖ ≤ R ^ k * δ₂ :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hMi k) hd (norm_nonneg _) (by positivity)
      have := bound_one_add_mul_bound_le hC hρ₀ hρ₁ hc (d := d) k
      nlinarith
    · filter_upwards [ih (j + 2) hδ₁, ih j hδ₁, hs j δ₂ hδ₂, hM] with i h2 h0' hd hMi
      have hstep := l2_opNorm_pow_succ_mul_le (M i) (T i (j + 1)) (T i (j + 2)) (T i j) c k
      rw [abs_of_nonneg hc] at hstep
      have hMk : ‖M i‖ ^ k * ‖M i * T i (j + 1) - (T i (j + 2) + c • T i j)‖ ≤ R ^ k * δ₂ :=
        mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hMi k) hd (norm_nonneg _) (by positivity)
      have := bound_add_two_add_mul_bound_le hC hρ₀ hc (d := d) j k
      nlinarith

end Asymptotics


/-- The growth rate `ρ + c / ρ` of the recursion is below `2 * √c + ε` for
`ρ = max √c (min 1 (ε / 4))`. -/
private theorem max_add_div_max_lt {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    max √c (min 1 (ε / 4)) + c / max √c (min 1 (ε / 4)) < 2 * √c + ε := by
  set ρ := max √c (min 1 (ε / 4))
  have hρ₀ : 0 < ρ := lt_max_of_lt_right (lt_min one_pos (by positivity))
  have hcρ : c / ρ ≤ ρ := by
    rw [div_le_iff₀ hρ₀]
    nlinarith [Real.sq_sqrt hc, le_max_left √c (min 1 (ε / 4)), Real.sqrt_nonneg c]
  have : ρ ≤ √c + ε / 4 :=
    max_le (by linarith) ((min_le_right _ _).trans (by linarith [Real.sqrt_nonneg c]))
  linarith

section BaiYin

variable {ι : Type*} {F : Filter ι} {p n : ι → Type*} [∀ i, Fintype (p i)] [∀ i, Fintype (n i)]
  [∀ i, DecidableEq (p i)] [∀ i, DecidableEq (n i)] {Y : (i : ι) → Matrix (p i) (n i) 𝕜}

/-- `‖Y * Yᴴ‖` is eventually bounded when the rows and columns have squared norms at most `2` and
the first row block `T 1` of the non-backtracking walk matrices is bounded. -/
private theorem eventually_l2_opNorm_mul_conjTranspose_le {K : ℝ}
    (hdeg : ∀ᶠ i in F, ∀ x, ∑ y, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0 x y‖ ^ 2 ≤ 2)
    (hT1 : ∀ᶠ i in F, ‖(nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) 2).toBlocks₁₁‖ ≤ K) :
    ∀ᶠ i in F, ‖Y i * (Y i)ᴴ‖ ≤ K + 2 := by
  filter_upwards [hT1, hdeg] with i hT1 hdi
  have hD : ‖(diagonal (fromBlocks 0 (Y i) (Y i)ᴴ 0 *
      fromBlocks 0 (Y i) (Y i)ᴴ 0).diag).toBlocks₁₁‖ ≤ 2 := by
    rw [toBlocks₁₁_eq_submatrix]
    refine (l2_opNorm_submatrix_le _ Sum.inl_injective Sum.inl_injective).trans
      (l2_opNorm_diagonal_le zero_le_two fun x ↦ ?_)
    rw [diag_fromBlocks_zero_mul_self_apply, RCLike.norm_ofReal,
      abs_of_nonneg (sum_nonneg fun _ _ ↦ by positivity)]
    exact hdi x
  rw [mul_conjTranspose_eq_toBlocks₁₁_add]
  exact (norm_add_le _ _).trans (add_le_add hT1 hD)

omit [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)] in
/-- The defects of the later steps of the row recursion are eventually small, given eventual
bounds on the dilations and on the squared norms of their rows, entries tending to zero, and
degrees close to `diag(1, c)`. -/
private theorem eventually_norm_mul_toBlocks₁₁_sub_le [∀ i, Fintype (n i)]
    [∀ i, DecidableEq (n i)] {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {R : ℝ} (hR : 0 ≤ R)
    (hDdev : ∀ η > 0, ∀ᶠ i in F, ‖diagonal (fromBlocks 0 (Y i) (Y i)ᴴ 0 *
      fromBlocks 0 (Y i) (Y i)ᴴ 0).diag - blockScalar 1 (c : 𝕜)‖ ≤ η)
    (hdeg : ∀ᶠ i in F, ∀ x, ∑ y, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0 x y‖ ^ 2 ≤ 2)
    (hent : ∀ η > 0, ∀ᶠ i in F, ∀ x y, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0 x y‖ ≤ η)
    (hH : ∀ᶠ i in F, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0‖ ≤ R) (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in F, ‖(Y i * (Y i)ᴴ - (1 + c) • 1) *
        (nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * (j + 1))).toBlocks₁₁ -
        ((nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * (j + 2))).toBlocks₁₁ +
          c • (nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * j)).toBlocks₁₁)‖ ≤ δ := by
  have hHerm (i : ι) : (fromBlocks 0 (Y i) (Y i)ᴴ 0).IsHermitian :=
    IsHermitian.fromBlocks isHermitian_zero rfl isHermitian_zero
  -- The walk matrices are eventually bounded, and the corrections tend to zero.
  have hB (k : ℕ) :
      ∀ᶠ i in F, ‖nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) k‖ ≤ (R + 6) ^ k := by
    filter_upwards [hH, hdeg, hent 1 one_pos] with i hHi hdi hei
    exact ((hHerm i).l2_opNorm_nonbacktrackingPow_le zero_le_two hei hdi k).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) k)
  -- The defect is at most `η` times a constant; choose `η` accordingly.
  obtain ⟨η, hη₀, hηL⟩ : ∃ η > 0, η * ((R + 6) ^ (2 * j + 2) + (R + 6) ^ (2 * j) +
      R * (R + 6) ^ (2 * j + 1) + R + 2) ≤ δ :=
    ⟨δ / ((R + 6) ^ (2 * j + 2) + (R + 6) ^ (2 * j) + R * (R + 6) ^ (2 * j + 1) + R + 2),
      by positivity, (div_mul_cancel₀ _ (by positivity)).le⟩
  have hE (k : ℕ) : ∀ᶠ i in F, ‖nonbacktrackingCorrection (fromBlocks 0 (Y i) (Y i)ᴴ 0) k‖ ≤ η :=
    (tendsto_l2_opNorm_nonbacktrackingCorrection hHerm hH hent k).eventually
      (ge_mem_nhds hη₀)
  filter_upwards [hDdev η hη₀, hE (2 * j + 2), hE (2 * j), hE (2 * j + 1), hB (2 * j + 2),
    hB (2 * j), hB (2 * j + 1), hH] with i hD hE2 hE0 hE1 hB2 hB0 hB1 hHi
  rw [(by ring : 2 * (j + 1) = 2 * j + 2), (by ring : 2 * (j + 2) = 2 * j + 4)]
  refine (norm_mul_toBlocks₁₁_nonbacktrackingPow_add_two_sub_le (Y i) hc₀ hc₁ (2 * j)).trans ?_
  have hBs := add_le_add (add_le_add hB2 hB0) (mul_le_mul hHi hB1 (norm_nonneg _) hR)
  have hDs := mul_le_mul hD hBs (by positivity) hη₀.le
  have hEs := mul_le_mul hHi hE1 (norm_nonneg _) hR
  linarith

/-- **Bai and Yin's non-backtracking bound.** Let `Y i` be rectangular matrices, along a filter,
whose entries tend to zero uniformly, whose rows have squared norms tending to `1` uniformly and
whose columns have squared norms tending to `c ∈ [0, 1]` uniformly. Suppose that the row blocks
`T l` of the non-backtracking walk matrices of length `2 * l` of the Hermitian dilations
`[[0, Y], [Yᴴ, 0]]` are eventually bounded by `C * (l + 1) ^ d * √c ^ l`, for constants `C` and `d`
independent of `l`. Then `‖Y * Yᴴ - (1 + c)‖ ≤ 2 * √c + ε` eventually, for every `ε > 0`. -/
theorem eventually_l2_opNorm_mul_conjTranspose_sub_smul_one_le {c : ℝ≥0} (hc : c ≤ 1)
    (hentry : ∀ ε > 0, ∀ᶠ i in F, ∀ a v, ‖Y i a v‖ ≤ ε)
    (hrow : ∀ ε > 0, ∀ᶠ i in F, ∀ a, |∑ v, ‖Y i a v‖ ^ 2 - 1| ≤ ε)
    (hcol : ∀ ε > 0, ∀ᶠ i in F, ∀ v, |∑ a, ‖Y i a v‖ ^ 2 - c| ≤ ε)
    (hT : ∃ (C : ℝ) (d : ℕ), ∀ l : ℕ, ∀ᶠ i in F,
      ‖(nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * l)).toBlocks₁₁‖ ≤
        C * ((l : ℝ) + 1) ^ d * √c ^ l) :
    ∀ ε > 0, ∀ᶠ i in F, ‖Y i * (Y i)ᴴ - (1 + (c : ℝ)) • 1‖ ≤ 2 * √c + ε := by
  have hc₀ : (0 : ℝ) ≤ c := c.coe_nonneg
  have hc₁ : (c : ℝ) ≤ 1 := by exact_mod_cast hc
  obtain ⟨C₀, d, hT₀⟩ := hT
  set C := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hT : ∀ l : ℕ, ∀ᶠ i in F,
      ‖(nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * l)).toBlocks₁₁‖ ≤
        C * ((l : ℝ) + 1) ^ d * √c ^ l := fun l ↦ (hT₀ l).mono fun i hi ↦ hi.trans <|
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      (by positivity)
  -- The dilations have small entries, bounded degrees and degrees close to `diag(1, c)`.
  have hdeg : ∀ᶠ i in F, ∀ x, ∑ y, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0 x y‖ ^ 2 ≤ 2 := by
    filter_upwards [hrow 1 one_pos, hcol 1 one_pos] with i hr hcl
    exact sum_norm_fromBlocks_zero_sq_le (Y i) (fun a ↦ by linarith [(abs_le.mp (hr a)).2])
      fun v ↦ by linarith [(abs_le.mp (hcl v)).2]
  have hDdev (η : ℝ) (hη : 0 < η) : ∀ᶠ i in F, ‖diagonal (fromBlocks 0 (Y i) (Y i)ᴴ 0 *
      fromBlocks 0 (Y i) (Y i)ᴴ 0).diag - blockScalar 1 ((c : ℝ) : 𝕜)‖ ≤ η := by
    filter_upwards [hrow η hη, hcol η hη] with i hr hcl
    exact norm_diagonal_diag_sub_blockScalar_le (Y i) c hη.le hr hcl
  -- `‖Y * Yᴴ‖` and the dilations are eventually bounded.
  set K := C * 2 ^ d * √c + 2
  have hYY := eventually_l2_opNorm_mul_conjTranspose_le (K := C * 2 ^ d * √c) hdeg
    ((hT 1).mono fun i hi ↦ by simpa [one_add_one_eq_two] using hi)
  set R := 2 * max 1 K
  have hR : 0 ≤ R := by positivity
  have hH : ∀ᶠ i in F, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0‖ ≤ R :=
    hYY.mono fun i hi ↦ l2_opNorm_fromBlocks_zero_le_of_le (Y i) hi
  have hent (η : ℝ) (hη : 0 < η) : ∀ᶠ i in F, ∀ x y, ‖fromBlocks 0 (Y i) (Y i)ᴴ 0 x y‖ ≤ η :=
    (hentry η hη).mono fun i hi ↦ norm_fromBlocks_zero_apply_le (Y i) hη.le hi
  -- Iterate the row recursion and extract the norm from the powers.
  intro ε hε
  set ρ := max √c (min 1 (ε / 4))
  have hρ₀ : 0 < ρ := lt_max_of_lt_right (lt_min one_pos (by positivity))
  have hρ₁ : ρ ≤ 1 := max_le (Real.sqrt_le_one.mpr hc₁) (min_le_left _ _)
  have hM : ∀ᶠ i in F, ‖Y i * (Y i)ᴴ - (1 + (c : ℝ)) • 1‖ ≤ K + 2 :=
    hYY.mono fun i hi ↦ l2_opNorm_mul_conjTranspose_sub_smul_one_le (Y i) hi hc₀ hc₁
  have hcheb := eventually_l2_opNorm_pow_mul_le (T := fun i l ↦
      (nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * l)).toBlocks₁₁) hc₀ hρ₀ hρ₁ hC
    (by positivity) hM (fun j ↦ (hT j).mono fun i hi ↦ hi.trans (by gcongr; exact le_max_left _ _))
    (fun δ hδ ↦ (hDdev δ hδ).mono fun i hi ↦
      (norm_mul_toBlocks₁₁_nonbacktrackingPow_zero_sub_le (Y i) c).trans hi)
    fun j δ hδ ↦ eventually_norm_mul_toBlocks₁₁_sub_le hc₀ hc₁ hR hDdev hdeg hent hH j hδ
  refine eventually_l2_opNorm_le_of_forall_pow (C := C) (d := d) (fun i ↦ ?_)
    (by positivity) (max_add_div_max_lt hc₀ hε) fun k δ hδ ↦ ?_
  · exact (isHermitian_mul_conjTranspose_self _).sub (isHermitian_one.smul (.all _))
  · filter_upwards [hcheb k 0 hδ] with i hi
    simpa using hi

/-- **Bai and Yin's non-backtracking bound for eigenvalues.** Under the hypotheses of
`Matrix.eventually_l2_opNorm_mul_conjTranspose_sub_smul_one_le`, for every `ε > 0` all eigenvalues
of `Y * Yᴴ` eventually lie in `[(1 - √c) ^ 2 - ε, (1 + √c) ^ 2 + ε]`, around the support of the
Marchenko–Pastur law of ratio `c`. -/
theorem eventually_eigenvalues₀_mul_conjTranspose_mem_Icc {c : ℝ≥0} (hc : c ≤ 1)
    (hentry : ∀ ε > 0, ∀ᶠ i in F, ∀ a v, ‖Y i a v‖ ≤ ε)
    (hrow : ∀ ε > 0, ∀ᶠ i in F, ∀ a, |∑ v, ‖Y i a v‖ ^ 2 - 1| ≤ ε)
    (hcol : ∀ ε > 0, ∀ᶠ i in F, ∀ v, |∑ a, ‖Y i a v‖ ^ 2 - c| ≤ ε)
    (hT : ∃ (C : ℝ) (d : ℕ), ∀ l : ℕ, ∀ᶠ i in F,
      ‖(nonbacktrackingPow (fromBlocks 0 (Y i) (Y i)ᴴ 0) (2 * l)).toBlocks₁₁‖ ≤
        C * ((l : ℝ) + 1) ^ d * √c ^ l) :
    ∀ ε > 0, ∀ᶠ i in F, ∀ k, (isHermitian_mul_conjTranspose_self (Y i)).eigenvalues₀ k ∈
      Set.Icc ((1 - √c) ^ 2 - ε) ((1 + √c) ^ 2 + ε) := by
  intro ε hε
  filter_upwards [eventually_l2_opNorm_mul_conjTranspose_sub_smul_one_le hc hentry hrow hcol
    hT ε hε] with i hi k
  have hA := isHermitian_mul_conjTranspose_self (Y i)
  have hshift : (Y i * (Y i)ᴴ + (-(1 + (c : ℝ))) • (1 : Matrix (p i) (p i) 𝕜)).IsHermitian :=
    hA.add (isHermitian_one.smul (.all _))
  have hev := congrFun (hA.eigenvalues₀_add_smul_one (-(1 + (c : ℝ))) hshift) k
  have hle := hshift.norm_eigenvalues₀_le_l2_opNorm k
  rw [hev, neg_smul, ← sub_eq_add_neg, Pi.add_apply, Real.norm_eq_abs] at hle
  have hsq : (√(c : ℝ)) ^ 2 = c := Real.sq_sqrt c.coe_nonneg
  constructor <;> nlinarith [abs_le.mp (hle.trans hi)]

end BaiYin

end Matrix
