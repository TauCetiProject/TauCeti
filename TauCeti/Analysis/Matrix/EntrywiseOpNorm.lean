/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Entrywise bounds for the Euclidean action of a matrix

For a finite rectangular matrix over `RCLike 𝕜`, the norm of its action on a
Euclidean vector is bounded by the largest entry norm times the geometric mean
of the row and column counts. For an `n × n` matrix, this specializes to the
constant `n * ε`. The bounds include matrices with empty row or column types.

## Main results

* `Matrix.norm_toEuclideanLin_le_of_entry_le`: rectangular entrywise-to-action bound.
* `Matrix.norm_toEuclideanLin_le_of_entry_le_square`: square finite-index specialization.
* `Matrix.l2_opNorm_le_of_norm_apply_le`: operator norm comparison under entrywise domination.
* `Matrix.l2_opNorm_le_sqrt_mul_of_row_col_sum_le`: the finite Schur test.

## Source

Adapted from `ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0).
-/

public section

namespace Matrix

open scoped BigOperators

/-- If every entry in row `i` of a finite matrix is bounded by `ε ≥ 0`, the `i`-th coordinate of
its Euclidean action has norm at most `ε * (√(card κ) * ‖x‖)`. -/
theorem norm_toEuclideanLin_apply_le_of_entry_le {𝕜 ι κ : Type*} [RCLike 𝕜]
    [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ 𝕜} {ε : ℝ} (heps : 0 ≤ ε) (i : ι) (hentry : ∀ j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 κ) :
    ‖(Matrix.toEuclideanLin A x) i‖ ≤ ε * (Real.sqrt (Fintype.card κ) * ‖x‖) := by
  calc
    ‖(Matrix.toEuclideanLin A x) i‖ = ‖∑ j : κ, A i j * x j‖ := by
      -- `toEuclideanLin` is `toLpLin 2 2`: unwrap `WithLp` explicitly, then expand `mulVec`;
      -- the closing `rfl` of `rw` identifies `ofLp x j` with `x j`.
      rw [show (Matrix.toEuclideanLin A x) i = (A *ᵥ WithLp.ofLp x) i from
        congrArg (fun y : EuclideanSpace 𝕜 ι => y i) (Matrix.toLpLin_apply (p := 2) (q := 2) A x),
        Matrix.mulVec_apply_eq_sum]
    _ ≤ ∑ j : κ, ‖A i j * x j‖ := norm_sum_le _ _
    _ = ∑ j : κ, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
    _ ≤ ∑ j : κ, ε * ‖x j‖ :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_right (hentry j) (norm_nonneg _)
    _ = ε * ∑ j : κ, ‖x j‖ := by rw [Finset.mul_sum]
    _ ≤ ε * (Real.sqrt (Fintype.card κ) * ‖x‖) :=
      mul_le_mul_of_nonneg_left (PiLp.sum_norm_le_sqrt_card_mul_norm x) heps

/-- Squared form of the entrywise bound on the Euclidean action of a finite matrix with entries
bounded by `ε ≥ 0`. -/
private theorem norm_toEuclideanLin_sq_le_of_entry_le {𝕜 ι κ : Type*} [RCLike 𝕜]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ 𝕜} {ε : ℝ} (heps : 0 ≤ ε) (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 κ) :
    ‖Matrix.toEuclideanLin A x‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc
    ∑ i : ι, ‖(Matrix.toEuclideanLin A x) i‖ ^ 2
        ≤ ∑ _i : ι, (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 :=
      Finset.sum_le_sum fun i _ =>
        pow_le_pow_left₀ (norm_nonneg _)
          (Matrix.norm_toEuclideanLin_apply_le_of_entry_le heps i (hentry i) x) 2
    _ = (Fintype.card ι : ℝ) * (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- If every entry of a finite rectangular matrix is bounded by `ε`, its Euclidean
action has norm at most `√(card ι) * ε * √(card κ)` times the input norm.

Both index types may be empty; in that case the action is zero, even if `ε` is negative. -/
theorem norm_toEuclideanLin_le_of_entry_le {𝕜 ι κ : Type*} [RCLike 𝕜]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    {A : Matrix ι κ 𝕜} {ε : ℝ} (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 κ) :
    ‖Matrix.toEuclideanLin A x‖ ≤
      Real.sqrt (Fintype.card ι) * ε * Real.sqrt (Fintype.card κ) * ‖x‖ := by
  classical
  by_cases hrows : Nonempty ι
  · by_cases hcols : Nonempty κ
    · obtain ⟨i₀⟩ := hrows
      obtain ⟨j₀⟩ := hcols
      have heps : 0 ≤ ε := (norm_nonneg (A i₀ j₀)).trans (hentry i₀ j₀)
      have hs : (Real.sqrt (Fintype.card ι)) ^ 2 = (Fintype.card ι : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2
          ≤ (Real.sqrt (Fintype.card ι) * ε *
              Real.sqrt (Fintype.card κ) * ‖x‖) ^ 2 := by
        calc ‖Matrix.toEuclideanLin A x‖ ^ 2
            ≤ (Fintype.card ι : ℝ) *
              (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 :=
              Matrix.norm_toEuclideanLin_sq_le_of_entry_le heps hentry x
          _ = _ := by
            simp only [mul_pow, hs]
            ring
      exact (abs_le_of_sq_le_sq' hle (by positivity)).2
    · have hx : x = 0 := by
        ext j
        exact (hcols ⟨j⟩).elim
      subst x
      simp
  · have hzero : Matrix.toEuclideanLin A x = 0 := by
      ext i
      exact (hrows ⟨i⟩).elim
    have hcard : Fintype.card ι = 0 :=
      Fintype.card_eq_zero_iff.mpr ⟨fun i => hrows ⟨i⟩⟩
    simp [hzero, hcard]

/-- The square finite-index form of the entrywise-to-Euclidean operator bound:
`‖A x‖ ≤ card ι * ε * ‖x‖` when `‖A i j‖ ≤ ε`. -/
theorem norm_toEuclideanLin_le_of_entry_le_square {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] [DecidableEq ι] {A : Matrix ι ι 𝕜} {ε : ℝ}
    (hentry : ∀ i j, ‖A i j‖ ≤ ε)
    (x : EuclideanSpace 𝕜 ι) :
    ‖Matrix.toEuclideanLin A x‖ ≤ (Fintype.card ι : ℝ) * ε * ‖x‖ := by
  have h := norm_toEuclideanLin_le_of_entry_le hentry x
  have hs : Real.sqrt (Fintype.card ι : ℝ) ^ 2 = (Fintype.card ι : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg _)
  calc
    ‖Matrix.toEuclideanLin A x‖ ≤
        Real.sqrt (Fintype.card ι) * ε * Real.sqrt (Fintype.card ι) * ‖x‖ := h
    _ = Real.sqrt (Fintype.card ι) ^ 2 * ε * ‖x‖ := by ring
    _ = (Fintype.card ι : ℝ) * ε * ‖x‖ := by rw [hs]

section L2Operator

open scoped Matrix.Norms.L2Operator

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

/-- Entrywise domination by a real matrix bounds the Euclidean operator norm. -/
theorem l2_opNorm_le_of_norm_apply_le (A : Matrix m n 𝕜) (B : Matrix m n ℝ)
    (hAB : ∀ i j, ‖A i j‖ ≤ B i j) : ‖A‖ ≤ ‖B‖ := by
  rw [l2_opNorm_def A]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_
  let y : EuclideanSpace ℝ n := WithLp.toLp 2 fun j ↦ ‖x j‖
  have hy : ‖y‖ = ‖x‖ := by
    apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mp
    simp [EuclideanSpace.norm_sq_eq, y]
  have hcoord (i : m) :
      ‖(toEuclideanLin A x) i‖ ≤ ‖(toEuclideanLin B y) i‖ := by
    simp only [toEuclideanLin, toLpLin_apply, PiLp.toLp_apply, mulVec_apply_eq_sum, y]
    calc
      _ ≤ ∑ j, ‖A i j * x j‖ := norm_sum_le _ _
      _ ≤ ∑ j, B i j * ‖x j‖ := by
        simp only [norm_mul]
        exact Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_right (hAB i j) (norm_nonneg _)
      _ ≤ ‖∑ j, B i j * ‖x j‖‖ := Real.le_norm_self _
  have hnorm : ‖toEuclideanLin A x‖ ≤ ‖toEuclideanLin B y‖ := by
    apply le_of_sq_le_sq _ (norm_nonneg _)
    simp only [EuclideanSpace.norm_sq_eq]
    exact Finset.sum_le_sum fun i _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hcoord i) 2
  exact hnorm.trans (by
    rw [← hy]
    exact B.l2_opNorm_mulVec y)

omit [Fintype m] in
/-- Weighted Cauchy–Schwarz bounds the squared magnitude of a matrix-vector coordinate by the
absolute row sum times a weighted sum of squared input coordinates. -/
theorem norm_toEuclideanLin_apply_sq_le (A : Matrix m n 𝕜) (x : EuclideanSpace 𝕜 n)
    (i : m) :
    ‖(toEuclideanLin A x) i‖ ^ 2 ≤
      (∑ j, ‖A i j‖) * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 := by
  calc
    _ ≤ (∑ j, ‖A i j‖ * ‖x j‖) ^ 2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      simpa only [toEuclideanLin, toLpLin_apply, PiLp.toLp_apply, mulVec_apply_eq_sum,
        norm_mul] using norm_sum_le Finset.univ (fun j ↦ A i j * x j)
    _ ≤ _ := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _
      (fun _ _ ↦ norm_nonneg _) (fun _ _ ↦ by positivity) (fun _ _ ↦ by ring_nf; rfl)

/-- The finite Schur test. The Euclidean operator norm is at most the geometric mean of any
upper bounds on the absolute row and column sums. Empty index types are allowed. -/
theorem l2_opNorm_le_sqrt_mul_of_row_col_sum_le (A : Matrix m n 𝕜) {r c : ℝ}
    (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ r) (hcol : ∀ j, ∑ i, ‖A i j‖ ≤ c) :
    ‖A‖ ≤ Real.sqrt (r * c) := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨i⟩⟩
  · rw [Subsingleton.elim A 0, norm_zero]
    exact Real.sqrt_nonneg _
  rcases isEmpty_or_nonempty n with hn | ⟨⟨j⟩⟩
  · rw [Subsingleton.elim A 0, norm_zero]
    exact Real.sqrt_nonneg _
  have hr : 0 ≤ r := (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hrow i)
  have hc : 0 ≤ c := (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _).trans (hcol j)
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x ↦ ?_
  apply le_of_sq_le_sq _ (by positivity)
  rw [mul_pow, Real.sq_sqrt (mul_nonneg hr hc), EuclideanSpace.norm_sq_eq x]
  calc
    ‖toEuclideanLin A x‖ ^ 2 = ∑ i, ‖(toEuclideanLin A x) i‖ ^ 2 :=
      EuclideanSpace.norm_sq_eq _
    _ ≤ ∑ i, r * ∑ j, ‖A i j‖ * ‖x j‖ ^ 2 :=
      Finset.sum_le_sum fun k _ ↦ (A.norm_toEuclideanLin_apply_sq_le x k).trans
        (mul_le_mul_of_nonneg_right (hrow k) (Finset.sum_nonneg fun j _ ↦
          mul_nonneg (norm_nonneg _) (sq_nonneg _)))
    _ = r * ∑ j, (∑ i, ‖A i j‖) * ‖x j‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      simp only [Finset.sum_mul]
    _ ≤ r * ∑ j, c * ‖x j‖ ^ 2 := by
      gcongr with j
      exact hcol j
    _ = r * c * ∑ j, ‖x j‖ ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

/-- For a Hermitian matrix, an upper bound on the absolute row sums bounds the Euclidean
operator norm. Nonnegativity of the bound also covers the empty matrix. -/
theorem IsHermitian.l2_opNorm_le_of_row_sum_le {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {r : ℝ} (hr : 0 ≤ r) (hrow : ∀ i, ∑ j, ‖A i j‖ ≤ r) : ‖A‖ ≤ r := by
  rw [← Real.sqrt_sq hr, sq]
  refine A.l2_opNorm_le_sqrt_mul_of_row_col_sum_le hrow fun j ↦ ?_
  simpa only [← hA.apply j, norm_star] using hrow j

end L2Operator

end Matrix
