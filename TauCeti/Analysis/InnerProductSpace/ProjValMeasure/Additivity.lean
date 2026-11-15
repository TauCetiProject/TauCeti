/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Orthogonal countable splitting and diagonal-measure laws for projection-valued measures

The diagonal scalar measure records the squared norm of the projection of a
Hilbert-space vector onto a measurable spectral region. For a countable
measurable partition, these squared norms sum to the squared norm of the
original vector. Because `P.proj B hB` is linear and multiplicative on intersections,
the diagonal measures inherit quadratic scaling under scalar multiplication, the
parallelogram identity on sums and differences, `2`-subadditivity on sums, and
measure restriction under a spectral projection. The identities apply to
projection-valued measures on arbitrary measurable spaces.

Adapted from Kitware's DKPS formalization in
`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Additivity.lean`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjValMeasure

/-- Squared extended norm of a spectral projection equals the diagonal mass
of the corresponding measurable set. -/
@[simp]
theorem enorm_sq_proj_apply (P : ProjValMeasure X H) (B : Set X)
    (hB : MeasurableSet B) (ξ : H) :
    ‖P.proj B hB ξ‖ₑ ^ 2 = (P.diag ξ) B := by
  have hfin : (P.diag ξ) B ≠ ⊤ :=
    measure_ne_top (μ := P.diag ξ) (s := B)
  calc
    ‖P.proj B hB ξ‖ₑ ^ 2 = ENNReal.ofReal (‖P.proj B hB ξ‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (((P.diag ξ) B).toReal) := by
      rw [P.norm_sq_proj_apply B hB ξ]
    _ = (P.diag ξ) B := ENNReal.ofReal_toReal hfin

/-- For a countable measurable partition, the squared extended norms of the
projected components sum to the squared extended norm of the original vector. -/
theorem tsum_enorm_sq_proj (P : ProjValMeasure X H) {ι : Type*} [Countable ι]
    (B : ι → Set X) (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcov : (⋃ k, B k) = Set.univ)
    (ξ : H) :
    ∑' k, ‖P.proj (B k) (hB k) ξ‖ₑ ^ 2 = ‖ξ‖ₑ ^ 2 := by
  calc
    ∑' k, ‖P.proj (B k) (hB k) ξ‖ₑ ^ 2 = ∑' k, (P.diag ξ) (B k) := by
      exact tsum_congr (fun k => P.enorm_sq_proj_apply (B k) (hB k) ξ)
    _ = (P.diag ξ) (⋃ k, B k) := (measure_iUnion hdisj hB).symm
    _ = (P.diag ξ) Set.univ := by rw [hcov]
    _ = ‖ξ‖ₑ ^ 2 := P.diag_univ ξ

/-- The diagonal measure at the zero vector is the zero measure. -/
@[simp]
theorem diag_zero (P : ProjValMeasure X H) : P.diag 0 = 0 := by
  ext B hB
  rw [← P.enorm_sq_proj_apply B hB 0]
  simp

/-- Scaling a vector by `c` scales its diagonal measure by `‖c‖ₑ ^ 2`. -/
theorem diag_smul (P : ProjValMeasure X H) (c : ℂ) (ξ : H) :
    P.diag (c • ξ) = (‖c‖ₑ ^ 2) • P.diag ξ := by
  ext B hB
  rw [smul_apply, ← P.enorm_sq_proj_apply B hB (c • ξ),
    ← P.enorm_sq_proj_apply B hB ξ, map_smul, eNorm_smul, mul_pow, smul_eq_mul]

/-- Negating a vector leaves its diagonal measure unchanged. -/
@[simp]
theorem diag_neg (P : ProjValMeasure X H) (ξ : H) : P.diag (-ξ) = P.diag ξ := by
  simpa using P.diag_smul (-1) ξ

/-- **Parallelogram law** for the diagonal measures of a projection-valued measure:
`P.diag (ξ + ψ) + P.diag (ξ - ψ) = 2 • (P.diag ξ + P.diag ψ)`. -/
theorem diag_add_diag_sub (P : ProjValMeasure X H) (ξ ψ : H) :
    P.diag (ξ + ψ) + P.diag (ξ - ψ) = (2 : ℝ≥0∞) • (P.diag ξ + P.diag ψ) := by
  ext B hB
  simp only [add_apply, smul_apply, smul_eq_mul,
    ← P.enorm_sq_proj_apply B hB, map_add, map_sub]
  have hpar := parallelogram_law_with_norm ℂ (P.proj B hB ξ) (P.proj B hB ψ)
  have hreal :
      ‖P.proj B hB ξ + P.proj B hB ψ‖ ^ 2 + ‖P.proj B hB ξ - P.proj B hB ψ‖ ^ 2 =
        2 * (‖P.proj B hB ξ‖ ^ 2 + ‖P.proj B hB ψ‖ ^ 2) := by
    linarith
  have hof := congrArg ENNReal.ofReal hreal
  simpa [ENNReal.ofReal_add, ENNReal.ofReal_mul, ENNReal.ofReal_pow, norm_nonneg,
    ofReal_norm] using hof

/-- The diagonal measure of `ξ + ψ` is bounded by `2 • (P.diag ξ + P.diag ψ)`. -/
theorem diag_add_le (P : ProjValMeasure X H) (ξ ψ : H) :
    P.diag (ξ + ψ) ≤ (2 : ℝ≥0∞) • (P.diag ξ + P.diag ψ) := by
  rw [← P.diag_add_diag_sub ξ ψ]
  exact Measure.le_add_right le_rfl

/-- Projecting a vector onto a measurable set `B` restricts its diagonal measure to `B`. -/
theorem diag_proj (P : ProjValMeasure X H) {B : Set X} (hB : MeasurableSet B) (ξ : H) :
    P.diag (P.proj B hB ξ) = (P.diag ξ).restrict B := by
  ext C hC
  rw [Measure.restrict_apply hC, ← P.enorm_sq_proj_apply C hC, ← mul_apply_eq_comp,
    P.proj_inter, P.enorm_sq_proj_apply]

end ProjValMeasure
end TauCeti
