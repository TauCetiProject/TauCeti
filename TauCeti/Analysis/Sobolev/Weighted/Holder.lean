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
The exponents include `∞`; no finite-dimensionality or completeness assumption is needed.

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
  have hp : p ≠ 0 := ne_of_gt ((pos_iff_ne_zero.2 hr).trans_le
    (ENNReal.HolderTriple.le p q r))
  have hq : q ≠ 0 := ne_of_gt ((pos_iff_ne_zero.2 hr).trans_le
    (ENNReal.HolderTriple.le q p r))
  simp only [map_smul, smul_apply, smul_smul]
  rw [← Real.rpow_add (norm_pos_iff.2 hx)]
  congr 2
  rw [ENNReal.HolderTriple.inv_eq p q r,
    ENNReal.toReal_add (ENNReal.inv_ne_top.2 hp) (ENNReal.inv_ne_top.2 hq)]
  ring

/-- A bounded bilinear map satisfies Hölder's inequality with the sum of the Bartnik weights.
The reference measure is supported away from the zero radius. -/
theorem weightedELpNorm_bilin_le [ENNReal.HolderTriple p q r]
    (B : F →L[ℝ] G →L[ℝ] H)
    (h0 : ∀ᵐ x ∂μ, x ≠ 0) {f : E → F} {g : E → G}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (δ ε : ℝ) :
    weightedELpNorm (fun x ↦ B (f x) (g x)) r (δ + ε) μ ≤
      ‖B‖ₑ * weightedELpNorm f p δ μ * weightedELpNorm g q ε μ := by
  have hfm : AEStronglyMeasurable
      (fun x ↦ ‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • f x) μ :=
    (by fun_prop : Measurable fun x : E ↦
      ‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal)).aestronglyMeasurable.smul hf
  have hgm : AEStronglyMeasurable
      (fun x ↦ ‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • g x) μ :=
    (by fun_prop : Measurable fun x : E ↦
      ‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal)).aestronglyMeasurable.smul hg
  by_cases hr : r = 0
  · have hm : AEStronglyMeasurable
        (fun x ↦ ‖x‖ ^ (-(δ + ε) - Module.finrank ℝ E * r⁻¹.toReal) •
          B (f x) (g x)) μ :=
      (by fun_prop : Measurable fun x : E ↦
        ‖x‖ ^ (-(δ + ε) - Module.finrank ℝ E * r⁻¹.toReal)).aestronglyMeasurable.smul
          (B.continuous₂.comp_aestronglyMeasurable₂ hf hg)
    subst r
    rw [weightedELpNorm_def, eLpNorm_exponent_zero hm]
    exact bot_le
  have heq : (fun x ↦ ‖x‖ ^ (-(δ + ε) - Module.finrank ℝ E * r⁻¹.toReal) •
      B (f x) (g x)) =ᵐ[μ] fun x ↦
        B (‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • f x)
          (‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • g x) := by
    filter_upwards [h0] with x hx
    exact weight_bilin_eq B δ ε hr hx _ _
  simp only [weightedELpNorm_def]
  rw [eLpNorm_congr_ae heq]
  exact eLpNorm_le_eNorm_mul_eLpNorm_mul_eLpNorm (p := p) (q := q) (r := r) B hfm hgm

/-- A bounded bilinear map sends weighted `Lᵖ` and `Lᵠ` functions into weighted `Lʳ`,
adding the Bartnik weights. -/
theorem MemWeightedLp.bilin [ENNReal.HolderTriple p q r]
    {δ ε : ℝ} {f : E → F} {g : E → G}
    (hf : MemWeightedLp f p δ μ) (hg : MemWeightedLp g q ε μ)
    (B : F →L[ℝ] G →L[ℝ] H) (h0 : ∀ᵐ x ∂μ, x ≠ 0) :
    MemWeightedLp (fun x ↦ B (f x) (g x)) r (δ + ε) μ := by
  refine memWeightedLp_iff.2 ((weightedELpNorm_bilin_le (p := p) (q := q) B h0
    (hf.aestronglyMeasurable h0) (hg.aestronglyMeasurable h0) δ ε).trans_lt ?_)
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
  apply (memLp_congr_ae ?_).1 hmem
  filter_upwards [h0] with x hx
  rw [← weight_bilin_eq (r := 1) B δ ε (by simp) hx]
  simp [hδε]

omit [OpensMeasurableSpace E] in
/-- The weighted Hölder dual pairing has norm at most the product of the weighted norms
times the norm of the bilinear map. -/
theorem eNorm_integral_bilin_le_weightedELpNorm [ENNReal.HolderConjugate p q]
    {δ ε : ℝ} {f : E → F} {g : E → G}
    (hf : MemWeightedLp f p δ μ) (hg : MemWeightedLp g q ε μ)
    (B : F →L[ℝ] G →L[ℝ] H) (h0 : ∀ᵐ x ∂μ, x ≠ 0)
    (hδε : δ + ε = -(Module.finrank ℝ E : ℝ)) :
    ‖∫ x, B (f x) (g x) ∂μ‖ₑ ≤
      ‖B‖ₑ * weightedELpNorm f p δ μ * weightedELpNorm g q ε μ := by
  have heq : (fun x ↦ B (‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • f x)
      (‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • g x)) =ᵐ[μ]
      fun x ↦ B (f x) (g x) := by
    filter_upwards [h0] with x hx
    rw [← weight_bilin_eq (r := 1) B δ ε (by simp) hx]
    simp [hδε]
  calc
    ‖∫ x, B (f x) (g x) ∂μ‖ₑ ≤ eLpNorm (fun x ↦ B (f x) (g x)) 1 μ := by
      rw [eLpNorm_one_eq_lintegral_eNorm (hf.integrable_bilin hg B h0 hδε).aestronglyMeasurable]
      exact eNorm_integral_le_lintegral_eNorm _
    _ = eLpNorm (fun x ↦ B (‖x‖ ^ (-δ - Module.finrank ℝ E * p⁻¹.toReal) • f x)
        (‖x‖ ^ (-ε - Module.finrank ℝ E * q⁻¹.toReal) • g x)) 1 μ :=
      (eLpNorm_congr_ae heq).symm
    _ ≤ _ := by
      simpa only [weightedELpNorm_def] using
        eLpNorm_le_eNorm_mul_eLpNorm_mul_eLpNorm (p := p) (q := q) (r := 1) B
          (memWeightedLp_iff_memLp.1 hf).aestronglyMeasurable
          (memWeightedLp_iff_memLp.1 hg).aestronglyMeasurable

end TauCeti
