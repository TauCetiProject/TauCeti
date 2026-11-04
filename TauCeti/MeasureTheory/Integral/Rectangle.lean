/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integrals over closed rectangles in the plane

Over a closed rectangle `[a₁, b₁] × [a₂, b₂]` in `ℝ × ℝ`, the fundamental theorem of calculus in one
coordinate shows that a partial derivative of a function which takes the same values on the two
opposite sides of the rectangle integrates to zero. Together with the vanishing of a continuous
nonnegative function with zero integral, this is how energy identities on a fundamental domain of
a doubly (twisted) periodic map are used.

## Main declarations

* `TauCeti.setIntegral_rect_eq_zero_of_hasDerivAt_fst`,
  `TauCeti.setIntegral_rect_eq_zero_of_hasDerivAt_snd`: a partial derivative of a function with
  equal values on the two opposite sides integrates to zero over the rectangle.
* `TauCeti.eqOn_zero_of_setIntegral_rect_eq_zero`: a continuous nonnegative function with zero
  integral over a nondegenerate rectangle vanishes on it.
-/

public section

open Set MeasureTheory

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a₁ b₁ a₂ b₂ : ℝ}

/-- A derivative in the first coordinate of a function with equal values on the vertical sides
`{a₁} × ℝ` and `{b₁} × ℝ` integrates to zero over the rectangle `[a₁, b₁] × [a₂, b₂]`. -/
theorem setIntegral_rect_eq_zero_of_hasDerivAt_fst {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun s ↦ Φ (s, t)) (φ (s, t)) s)
    (hper : ∀ t, Φ (b₁, t) = Φ (a₁, t)) : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = 0 := by
  have hint : Integrable φ ((volume.restrict (Icc a₁ b₁)).prod (volume.restrict (Icc a₂ b₂))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hφ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod_symm _ hint]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t ↦ ?_)
  dsimp only [Pi.zero_apply]
  rcases lt_or_ge b₁ a₁ with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hΦ s t)
      ((hφ.comp (Continuous.prodMk_left t)).intervalIntegrable _ _), hper, sub_self]

/-- A derivative in the second coordinate of a function with equal values on the horizontal
sides `ℝ × {a₂}` and `ℝ × {b₂}` integrates to zero over the rectangle `[a₁, b₁] × [a₂, b₂]`. -/
theorem setIntegral_rect_eq_zero_of_hasDerivAt_snd {Φ φ : ℝ × ℝ → E}
    (hφ : Continuous φ) (hΦ : ∀ s t, HasDerivAt (fun t ↦ Φ (s, t)) (φ (s, t)) t)
    (hper : ∀ s, Φ (s, b₂) = Φ (s, a₂)) : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, φ z = 0 := by
  have hint : Integrable φ ((volume.restrict (Icc a₁ b₁)).prod (volume.restrict (Icc a₂ b₂))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hφ.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, integral_prod _ hint]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun s ↦ ?_)
  dsimp only [Pi.zero_apply]
  rcases lt_or_ge b₂ a₂ with hab | hab
  · simp [Icc_eq_empty_of_lt hab]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hΦ s t)
      ((hφ.comp (Continuous.prodMk_right s)).intervalIntegrable _ _), hper, sub_self]

/-- A continuous nonnegative function with zero integral over a nondegenerate rectangle
`[a₁, b₁] × [a₂, b₂]` vanishes on it. -/
theorem eqOn_zero_of_setIntegral_rect_eq_zero {f : ℝ × ℝ → ℝ} (h₁ : a₁ < b₁) (h₂ : a₂ < b₂)
    (hf : Continuous f) (hf0 : 0 ≤ f) (hint : ∫ z in Icc a₁ b₁ ×ˢ Icc a₂ b₂, f z = 0) :
    EqOn f 0 (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := by
  have hR : IsCompact (Icc a₁ b₁ ×ˢ Icc a₂ b₂) := isCompact_Icc.prod isCompact_Icc
  have hae := (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall hf0)
    (hf.continuousOn.integrableOn_compact hR)).1 hint
  have hU : EqOn f 0 (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) :=
    Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae_restrict_of_subset
      (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self) hae) (isOpen_Ioo.prod isOpen_Ioo)
      hf.continuousOn continuousOn_const
  have hcl : closure (Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) = Icc a₁ b₁ ×ˢ Icc a₂ b₂ := by
    rw [closure_prod_eq, closure_Ioo h₁.ne, closure_Ioo h₂.ne]
  rw [← hcl]
  exact hU.of_subset_closure hf.continuousOn continuousOn_const subset_closure subset_rfl

end TauCeti

end
