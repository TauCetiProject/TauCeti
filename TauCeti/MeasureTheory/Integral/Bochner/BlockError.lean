/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Errors of sums of integrated kernels

For almost everywhere strongly measurable kernels, the sum of the nonnegative integrals of
the termwise errors controls the change in a block of summed Bochner integrals. A finite
error budget makes the two blocks converge or diverge together.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- The extended distance between two sums of integrals is bounded by the sum of the
integrated pointwise extended distances. A finite error budget forces the series of
integrals to be summable together; otherwise the inequality is automatic. -/
theorem edist_tsum_integral_le_tsum_lintegral_edist {α V I : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    {μ : Measure α} {K L : I → α → V}
    (hK : ∀ i, AEStronglyMeasurable (K i) μ) (hL : ∀ i, AEStronglyMeasurable (L i) μ) :
    edist (∑' i, ∫ x, K i x ∂μ) (∑' i, ∫ x, L i x ∂μ) ≤
      ∑' i, ∫⁻ x, edist (K i x) (L i x) ∂μ := by
  by_cases hV : ¬ CompleteSpace V
  · simp [integral_of_not_completeSpace hV]
  let : CompleteSpace V := not_not.mp hV
  simp only [eDist_eq_eNorm_sub]
  by_cases hE : (∑' i, ∫⁻ x, ‖K i x - L i x‖ₑ ∂μ) = ∞
  · rw [hE]
    exact le_top
  have hterm (i : I) : ‖(∫ x, K i x ∂μ) - ∫ x, L i x ∂μ‖ₑ ≤ ∫⁻ x, ‖K i x - L i x‖ₑ ∂μ := by
    have hEi : Integrable (fun x ↦ K i x - L i x) μ :=
      ⟨(hK i).sub (hL i),
        (le_tsum (fun j ↦ ∫⁻ x, ‖K j x - L j x‖ₑ ∂μ) i).trans_lt (lt_top_iff_ne_top.mpr hE)⟩
    by_cases hKi : Integrable (K i) μ
    · have hLi : Integrable (L i) μ :=
        (hKi.sub hEi).congr (.of_forall fun x ↦ sub_sub_cancel (K i x) (L i x))
      rw [← integral_sub hKi hLi]
      exact eNorm_integral_le_lintegral_eNorm _
    · have hLi : ¬ Integrable (L i) μ := fun hi ↦ hKi <|
        (hEi.add hi).congr (.of_forall fun x ↦ sub_add_cancel (K i x) (L i x))
      simp [integral_undef hKi, integral_undef hLi]
  have he : Summable fun i ↦ (∫ x, K i x ∂μ) - ∫ x, L i x ∂μ :=
    .of_eNorm (ne_top_of_le_ne_top hE (tsum_le_tsum hterm))
  by_cases hk : Summable fun i ↦ ∫ x, K i x ∂μ
  · have hl : Summable fun i ↦ ∫ x, L i x ∂μ := by
      simpa only [sub_sub_cancel] using hk.sub he
    rw [← hk.tsum_sub hl]
    exact eNorm_tsum_le_tsum_eNorm.trans (tsum_le_tsum hterm)
  · have hl : ¬ Summable (fun i ↦ ∫ x, L i x ∂μ) := fun hl ↦ hk <| by
      simpa only [sub_add_cancel] using he.add hl
    simp [tsum_eq_zero_of_not_summable hk, tsum_eq_zero_of_not_summable hl]

end MeasureTheory
