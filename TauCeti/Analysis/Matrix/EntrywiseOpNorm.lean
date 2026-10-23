/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Lp.PiLp

/-!
# Entrywise bounds for the Euclidean action of a matrix

For a finite rectangular matrix over `RCLike 𝕜`, the norm of its action on a
Euclidean vector is bounded by the largest entry norm times the geometric mean
of the row and column counts. For an `n × n` matrix, this specializes to the
constant `n * ε`. The bounds include matrices with empty row or column types.

## Main results

* `Matrix.norm_toEuclideanLin_le_of_entry_le`: rectangular entrywise-to-action bound.
* `Matrix.norm_toEuclideanLin_le_of_entry_le_square`: square finite-index specialization.

## Source

Adapted from `ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(Kitware, Inc.; Apache-2.0).
-/

public section

namespace TauCeti

open Matrix

open scoped BigOperators

/-- If every entry of a finite rectangular matrix is bounded by `ε`, its Euclidean
action has norm at most `√(card ι) * ε * √(card κ)` times the input norm.

Both index types may be empty; in that case the action is zero, even if `ε` is negative. -/
theorem _root_.Matrix.norm_toEuclideanLin_le_of_entry_le {𝕜 ι κ : Type*} [RCLike 𝕜]
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
      have hrow : ∀ i : ι,
          ‖(Matrix.toEuclideanLin A x) i‖ ≤
            ε * (Real.sqrt (Fintype.card κ) * ‖x‖) := by
        intro i
        have happ : (Matrix.toEuclideanLin A x) i = ∑ j : κ, A i j * x j := by
          -- `toEuclideanLin` abbreviates `toLpLin 2 2`; use its public evaluation
          -- theorem instead of reducing the `EuclideanSpace`/`WithLp` implementation.
          calc
            _ = (WithLp.toLp 2 (A *ᵥ WithLp.ofLp x)) i :=
              congrArg (fun y : EuclideanSpace 𝕜 ι => y i)
                (Matrix.toLpLin_apply (p := 2) (q := 2) A x)
            _ = ∑ j : κ, A i j * x j := by
              simp [Matrix.mulVec, dotProduct]
        calc
          ‖(Matrix.toEuclideanLin A x) i‖ = ‖∑ j : κ, A i j * x j‖ := by rw [happ]
          _ ≤ ∑ j : κ, ‖A i j * x j‖ := norm_sum_le _ _
          _ = ∑ j : κ, ‖A i j‖ * ‖x j‖ := by simp only [norm_mul]
          _ ≤ ∑ j : κ, ε * ‖x j‖ :=
            Finset.sum_le_sum fun j _ =>
              mul_le_mul_of_nonneg_right (hentry i j) (norm_nonneg _)
          _ = ε * ∑ j : κ, ‖x j‖ := by rw [Finset.mul_sum]
          _ ≤ ε * (Real.sqrt (Fintype.card κ) * ‖x‖) := by
            exact mul_le_mul_of_nonneg_left
              (PiLp.sum_norm_le_sqrt_card_mul_norm x) heps
      have hnorm_sq : ‖Matrix.toEuclideanLin A x‖ ^ 2
          ≤ (Fintype.card ι : ℝ) *
            (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        calc
          ∑ i : ι, ‖(Matrix.toEuclideanLin A x) i‖ ^ 2
              ≤ ∑ _i : ι, (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
            exact Finset.sum_le_sum fun i _ =>
              pow_le_pow_left₀ (norm_nonneg _) (hrow i) 2
          _ = (Fintype.card ι : ℝ) *
                (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hs : (Real.sqrt (Fintype.card ι)) ^ 2 = (Fintype.card ι : ℝ) :=
        Real.sq_sqrt (by positivity)
      have hsq_eq :
          (Real.sqrt (Fintype.card ι) * ε * Real.sqrt (Fintype.card κ) * ‖x‖) ^ 2 =
            (Fintype.card ι : ℝ) *
              (ε * (Real.sqrt (Fintype.card κ) * ‖x‖)) ^ 2 := by
        simp only [mul_pow, hs]
        ring
      have hle : ‖Matrix.toEuclideanLin A x‖ ^ 2
          ≤ (Real.sqrt (Fintype.card ι) * ε *
              Real.sqrt (Fintype.card κ) * ‖x‖) ^ 2 := by
        rw [hsq_eq]
        exact hnorm_sq
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
theorem _root_.Matrix.norm_toEuclideanLin_le_of_entry_le_square {𝕜 ι : Type*} [RCLike 𝕜]
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

end TauCeti
