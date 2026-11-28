/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The resolvent transform at real points

For a measure `μ` on the real line, Mathlib's `MeasureTheory.resolventTransform` can be taken
with values in `ℝ` at a real point `x`: it is then the real integral `∫ (t - x)⁻¹ dμ(t)`. This
real-valued transform is the restriction of the complex one to the real axis
(`MeasureTheory.Measure.resolventTransform_ofReal`). Real points outside the support are where
the outlier eigenvalues of perturbed random matrices are located, through secular equations in
the real transform.

For a finite measure carried by `(-∞, b]` and a point `x > b`, the integrand `(t - x)⁻¹` lies in
`[-(x - b)⁻¹, 0]` almost everywhere, so the transform lies in `[-μ(ℝ) / (x - b), 0]`.

## Main results

* `MeasureTheory.Measure.resolventTransform_ofReal`: at a real point, the complex transform is the
  real one.
* `MeasureTheory.resolventTransform_nonpos_of_ae_le`,
  `MeasureTheory.neg_div_sub_le_resolventTransform_of_ae_le`: above the support, the real
  transform of a finite measure lies in `[-μ(ℝ) / (x - b), 0]`.
-/

public section

noncomputable section

open Set

namespace MeasureTheory

/-- At a real point, the complex resolvent transform of a measure on the real line is the real
resolvent transform. -/
@[simp, norm_cast]
theorem Measure.resolventTransform_ofReal (μ : Measure ℝ) (x : ℝ) :
    resolventTransform μ (x : ℂ) = ((resolventTransform μ x : ℝ) : ℂ) := by
  rw [resolventTransform_apply, resolventTransform_apply, ← integral_complex_ofReal]
  refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
  simp [resolvent, Ring.inverse_eq_inv']

variable {μ : Measure ℝ} {b x : ℝ}

/-- If `μ` is carried by `(-∞, b]` and `b < x`, the real resolvent transform of `μ` at `x` is
nonpositive. -/
theorem resolventTransform_nonpos_of_ae_le (hb : ∀ᵐ t ∂μ, t ≤ b) (hx : b < x) :
    resolventTransform μ x ≤ 0 := by
  rw [resolventTransform_apply]
  refine integral_nonpos_of_ae ?_
  filter_upwards [hb] with t ht
  simpa [resolvent, Ring.inverse_eq_inv'] using ht.trans hx.le

/-- If the finite measure `μ` is carried by `(-∞, b]` and `b < x`, the real resolvent transform of
`μ` at `x` is at least `-μ(ℝ) / (x - b)`. -/
theorem neg_div_sub_le_resolventTransform_of_ae_le [IsFiniteMeasure μ]
    (hb : ∀ᵐ t ∂μ, t ≤ b) (hx : b < x) :
    -(μ.real univ / (x - b)) ≤ resolventTransform μ x := by
  have hsupp : μ.support ⊆ Iic b := Measure.support_subset_of_isClosed isClosed_Iic hb
  have hint : Integrable (resolvent (R := ℝ) x) μ :=
    integrable_resolvent fun ⟨t, ht, htx⟩ ↦ by
      have : t ≤ b := hsupp ht
      simp only [Algebra.algebraMap_self, RingHom.id_apply] at htx
      linarith
  rw [resolventTransform_apply]
  calc -(μ.real univ / (x - b)) = ∫ _, -(x - b)⁻¹ ∂μ := by
        rw [integral_const, smul_eq_mul]
        ring
    _ ≤ ∫ t, resolvent (R := ℝ) x t ∂μ := by
      refine integral_mono_ae (integrable_const _) hint ?_
      filter_upwards [hb] with t ht
      simp only [resolvent, Algebra.algebraMap_self, RingHom.id_apply, Ring.inverse_eq_inv']
      rw [← inv_neg, neg_sub]
      exact (inv_le_inv_of_neg (by linarith) (by linarith)).2 (by linarith)

end MeasureTheory
