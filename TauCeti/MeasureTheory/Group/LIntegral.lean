/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Averaged translations of lower Lebesgue integrals

For a left and right invariant s-finite measure `μ` on a measurable group `G`, the change of
variables `x = b(p) y k⁻¹`, averaged over an s-finite measure on the translation parameters
`(p, k) ∈ P × K` with `K` a subgroup, moves a weight `g` from the old variable `y` to the new
variable `x` (`MeasureTheory.lintegral_mul_lintegral_translate`). The proof combines Tonelli's
theorem with left and right invariance of `μ`.

## References

The statement and proof are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache
2.0, Copyright 2026 Anthropic PBC), `src/Lib/Adelic/QuotientMeasure/IwasawaUnfolding.lean`
(the Fubini and translation step of `New.lintegral_iwasawa`).
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- **Change of variables `x = b(p) y k⁻¹`, averaged over a measure on the translations.** For a
left and right invariant s-finite measure `μ` on `G`, a measurable `b : P → G`, a subgroup `K` and
an s-finite measure `π` on `P × K`,
`∫ g(y) ∫ f(b(p) y k⁻¹) dπ(p, k) dμ(y) = ∫ (∫ g(b(p)⁻¹ x k) dπ(p, k)) f(x) dμ(x)`. -/
theorem lintegral_mul_lintegral_translate {G P : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul₂ G] [MeasurableInv G] [MeasurableSpace P] {K : Subgroup G} (μ : Measure G)
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [SFinite μ] {π : Measure (P × K)} [SFinite π]
    {b : P → G} (hb : Measurable b) {g f : G → ℝ≥0∞} (hg : Measurable g) (hf : Measurable f) :
    ∫⁻ y, g y * ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π ∂μ =
      ∫⁻ x, (∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π) * f x ∂μ := by
  have : MeasurableInv K := ⟨measurable_subtypeVal.inv.subtype_mk⟩
  calc ∫⁻ y, g y * ∫⁻ h, f (b h.1 * y * h.2⁻¹) ∂π ∂μ
    _ = ∫⁻ h, ∫⁻ y, g y * f (b h.1 * y * h.2⁻¹) ∂μ ∂π := by
      simp (disch := fun_prop) only [← lintegral_const_mul]
      exact lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ h, ∫⁻ x, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂μ ∂π := by
      congr with ⟨p, k⟩
      rw [← lintegral_mul_left_eq_self _ (b p)⁻¹, ← lintegral_mul_right_eq_self _ (k : G)]
      simp [mul_assoc]
    _ = ∫⁻ x, ∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) * f x ∂π ∂μ :=
      lintegral_lintegral_swap (by fun_prop)
    _ = ∫⁻ x, (∫⁻ h, g ((b h.1)⁻¹ * (x * h.2)) ∂π) * f x ∂μ :=
      lintegral_congr fun x ↦ lintegral_mul_const _ (by fun_prop)

end MeasureTheory
