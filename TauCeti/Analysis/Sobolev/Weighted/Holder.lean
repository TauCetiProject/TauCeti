/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Weighted
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Hölder multiplication for Bartnik weighted Lebesgue classes

For a Hölder triple `p⁻¹ + q⁻¹ = r⁻¹`, multiplication adds Bartnik weights:
`Lᵖ_δ × Lᵠ_ε → Lʳ_(δ+ε)`. More generally, every bounded real bilinear map acts
between these classes with the same operator-norm bound as in the unweighted inequality.
The exponents include `∞`. The product, integrability and integral norm estimates require
neither finite-dimensionality nor completeness. For weighted `Lᵖ` inputs and a complete target,
the integral estimate bounds the weighted Bochner volume pairing. For an incomplete target,
Mathlib defines the Bochner integral to be zero, so that estimate is trivial.
The norm inequality has positive output exponent; product membership also covers exponent zero.

The reference measure must give no mass to the origin, where the radius weight can vanish.
This includes the intended exterior-domain measures. The result also gives the weighted
dual pairing `Lᵖ_δ × Lᵠ_(-n-δ) → L¹` for conjugate exponents.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Lemma 9.1.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
  {μ : Measure E} {p q r : ℝ≥0∞}

omit [MeasurableSpace E] [OpensMeasurableSpace E] in
/-- The radial weights of a Hölder product multiply to its output weight away from zero. -/
private theorem weight_bilin_eq [ENNReal.HolderTriple p q r]
    (B : F →L[ℝ] G →L[ℝ] H) (δ ε : ℝ)
    (hr : r ≠ 0) {x : E} (hx : x ≠ 0) (u : F) (v : G) :
    ‖x‖ ^ (-(δ + ε) - Module.finrank ℝ E * r⁻¹.toReal) • B u v =
      B (‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • u)
        (‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • v) := by
  have hp : p ≠ 0 := ne_bot_of_le_ne_bot hr (ENNReal.HolderTriple.le p q r)
  have hq : q ≠ 0 := ne_bot_of_le_ne_bot hr (ENNReal.HolderTriple.le q p r)
  have hexp : -(δ + ε) - Module.finrank ℝ E * r⁻¹.toReal =
      (-δ - Module.finrank ℝ E * p⁻¹.toReal) +
        (-ε - Module.finrank ℝ E * q⁻¹.toReal) := by
    rw [ENNReal.HolderTriple.inv_eq p q r,
      ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp) (ENNReal.inv_ne_top.2 hq)]
    ring
  rw [hexp, Real.rpow_add (norm_pos_iff.2 hx)]
  simp only [map_smul, smul_apply, smul_smul, mul_comm]

omit [OpensMeasurableSpace E] in
/-- Complementary radial weights cancel almost everywhere in a conjugate bilinear pairing. -/
private theorem weight_bilin_ae_eq_of_add_eq_neg_finrank [ENNReal.HolderConjugate p q]
    (B : F →L[ℝ] G →L[ℝ] H) {δ ε : ℝ} {f : E → F} {g : E → G}
    (hδε : δ + ε = -(Module.finrank ℝ E : ℝ)) (h0 : ∀ᵐ x ∂μ, x ≠ 0) :
    (fun x ↦ B (‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • f x)
      (‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • g x)) =ᵐ[μ]
      fun x ↦ B (f x) (g x) := by
  filter_upwards [h0] with x hx
  rw [← weight_bilin_eq (r := 1) B δ ε (by simp) hx]
  simp only [hδε, inv_one, ENNReal.toReal_one, mul_one, neg_neg, sub_self,
    Real.rpow_zero, one_smul]

omit [OpensMeasurableSpace E] in
/-- A bounded bilinear map satisfies Hölder's inequality with the sum of the Bartnik weights
at a positive output exponent, without measurability assumptions on the functions.
The reference measure gives no mass to the origin. -/
theorem _root_.ContinuousLinearMap.weightedELpNorm_bilin_le [ENNReal.HolderTriple p q r]
    (B : F →L[ℝ] G →L[ℝ] H)
    (hr : 0 < r)
    (h0 : ∀ᵐ x ∂μ, x ≠ 0) {f : E → F} {g : E → G}
    (δ ε : ℝ) :
    weightedELpNorm (fun x ↦ B (f x) (g x)) r (δ + ε) μ ≤
      ‖B‖ₑ * weightedELpNorm f p δ μ * weightedELpNorm g q ε μ := by
  have heq : (fun x ↦ ‖x‖ ^ (-(δ + ε) - Module.finrank ℝ E * r⁻¹.toReal) •
      B (f x) (g x)) =ᵐ[μ] fun x ↦
        B (‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • f x)
          (‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • g x) := by
    filter_upwards [h0] with x hx
    exact weight_bilin_eq B δ ε hr.ne' hx _ _
  simp only [weightedELpNorm_def]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_eNorm_of_pos (p := p) (q := q) (r := r)
    (B · ·) ‖B‖ₑ B.continuous₂.comp_aestronglyMeasurable₂
    (.of_forall fun _ ↦ B.le_opENorm₂ ..) hr

/-- A bounded bilinear map sends weighted `Lᵖ` and `Lᵠ` functions into weighted `Lʳ`,
adding the Bartnik weights. -/
theorem MemWeightedLp.bilin [ENNReal.HolderTriple p q r]
    {δ ε : ℝ} {f : E → F} {g : E → G}
    (hf : MemWeightedLp f p δ μ) (hg : MemWeightedLp g q ε μ)
    (B : F →L[ℝ] G →L[ℝ] H) (h0 : ∀ᵐ x ∂μ, x ≠ 0) :
    MemWeightedLp (fun x ↦ B (f x) (g x)) r (δ + ε) μ := by
  by_cases hr : r = 0
  · subst r
    apply memWeightedLp_iff_memLp.2
    apply memLp_zero_iff_aestronglyMeasurable.2
    exact (measurable_norm.pow_const _).aestronglyMeasurable.smul
      (B.continuous₂.comp_aestronglyMeasurable₂
        (hf.aestronglyMeasurable h0) (hg.aestronglyMeasurable h0))
  refine memWeightedLp_iff.2 ((B.weightedELpNorm_bilin_le (p := p) (q := q)
    (pos_iff_ne_zero.2 hr) h0 δ ε).trans_lt ?_)
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top eNorm_lt_top
    (memWeightedLp_iff.1 hf)) (memWeightedLp_iff.1 hg)

/-- Weighted real multiplication adds the Bartnik decay orders. -/
theorem MemWeightedLp.mul [ENNReal.HolderTriple p q r]
    {δ ε : ℝ} {f g : E → ℝ} (hf : MemWeightedLp f p δ μ)
    (hg : MemWeightedLp g q ε μ) (h0 : ∀ᵐ x ∂μ, x ≠ 0) :
    MemWeightedLp (f * g) r (δ + ε) μ :=
  hf.bilin hg (ContinuousLinearMap.mul ℝ ℝ) h0

omit [OpensMeasurableSpace E] in
/-- Complementary Bartnik weights give an integrable bilinear pairing at Hölder conjugate
exponents: the weights sum to minus the dimension. -/
theorem MemWeightedLp.integrable_bilin [ENNReal.HolderConjugate p q]
    {δ ε : ℝ} {f : E → F} {g : E → G}
    (hf : MemWeightedLp f p δ μ) (hg : MemWeightedLp g q ε μ)
    (B : F →L[ℝ] G →L[ℝ] H) (h0 : ∀ᵐ x ∂μ, x ≠ 0)
    (hδε : δ + ε = -(Module.finrank ℝ E : ℝ)) :
    Integrable (fun x ↦ B (f x) (g x)) μ := by
  have hmem := B.memLp_of_bilin 1 (memWeightedLp_iff_memLp.1 hf)
    (memWeightedLp_iff_memLp.1 hg)
  apply memLp_one_iff_integrable.1
  exact (memLp_congr_ae (weight_bilin_ae_eq_of_add_eq_neg_finrank
    (p := p) (q := q) (f := f) (g := g) B hδε h0)).1 hmem

omit [OpensMeasurableSpace E] in
/-- The norm of the totalized Bochner integral is bounded by the weighted Hölder product.
For weighted `Lᵖ` inputs and a complete target, this bounds the weighted volume pairing;
`MemWeightedLp.integrable_bilin` supplies integrability. The inequality itself needs no
measurability or finiteness hypotheses on the functions. For an incomplete target,
Mathlib defines the integral to be zero and the bound is trivial. -/
theorem _root_.ContinuousLinearMap.eNorm_integral_bilin_le_weightedELpNorm
    [ENNReal.HolderConjugate p q]
    {δ ε : ℝ} {f : E → F} {g : E → G}
    (B : F →L[ℝ] G →L[ℝ] H) (h0 : ∀ᵐ x ∂μ, x ≠ 0)
    (hδε : δ + ε = -(Module.finrank ℝ E : ℝ)) :
    ‖∫ x, B (f x) (g x) ∂μ‖ₑ ≤
      ‖B‖ₑ * weightedELpNorm f p δ μ * weightedELpNorm g q ε μ := by
  calc
    ‖∫ x, B (f x) (g x) ∂μ‖ₑ ≤ eLpNorm (fun x ↦ B (f x) (g x)) 1 μ :=
      (eNorm_integral_le_lintegral_eNorm _).trans lintegral_eNorm_le_eLpNorm_one
    _ = weightedELpNorm (fun x ↦ B (f x) (g x)) 1 (δ + ε) μ := by
      simpa only [hδε, inv_one, ENNReal.toReal_one, mul_one] using
        (weightedELpNorm_neg_finrank_mul (fun x ↦ B (f x) (g x)) 1 μ).symm
    _ ≤ _ := B.weightedELpNorm_bilin_le (p := p) (q := q) zero_lt_one h0 δ ε

end TauCeti
