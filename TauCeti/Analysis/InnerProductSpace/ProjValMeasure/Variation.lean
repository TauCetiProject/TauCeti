/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT-6
-/
module

public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Additivity
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Polarization

/-!
# The sharp variation estimate for polarized spectral measures

For the complex measure `P.polarizedComplexMeasure ψ ξ` associated with a normalized
projection-valued measure, we prove

`(P.polarizedComplexMeasure ψ ξ).variation univ ≤ ofReal (‖ψ‖ * ‖ξ‖)`,

and more generally on every measurable set `B`:

`(P.polarizedComplexMeasure ψ ξ).variation B ≤ ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖)`.

This sharp bound makes the polarized complex measure a finite-variation measure, absolutely
continuous with respect to both `P.diag ψ` and `P.diag ξ`, and yields Cauchy–Schwarz `L²`
domination for integration against its variation:

`∫⁻ x, g x ∂(P.polarizedComplexMeasure ψ ξ).variation`
`  ≤ ‖ψ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`.

In particular, every measurable symbol with finite second moment against `P.diag ξ` is integrable
against `P.polarizedComplexMeasure ψ ξ` for every `ψ : H`, with `L¹` norm bounded by
`‖ψ‖ * √(∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ))`.

On the diagonal, the variation of `P.polarizedComplexMeasure ξ ξ` is exactly `P.diag ξ`.

The underlying PVM and polarized-measure constructions are adapted from the
AIQ-Kitware DKPS formalization (Apache-2.0):
https://github.com/AIQ-Kitware/aiq-dkps-formalization.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, Section 3.1.
* K. Schmüdgen, *Unbounded Self-adjoint Operators on Hilbert Space*, Springer GTM 265, 2012,
  Section 4.2.
-/

public section

open MeasureTheory
open scoped InnerProductSpace ENNReal NNReal

namespace TauCeti.ProjValMeasure

variable {X H : Type*} [MeasurableSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The sharp variation bound for nonzero vectors. -/
private theorem polarizedComplexMeasure_variation_univ_le_of_ne_zero
    (P : ProjValMeasure X H) {ψ ξ : H} (hψz : ψ ≠ 0) (hξz : ξ ≠ 0) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  have hψ : 0 < ‖ψ‖ := norm_pos_iff.mpr hψz
  have hξ : 0 < ‖ξ‖ := norm_pos_iff.mpr hξz
  let a : ℝ≥0 := ⟨‖ξ‖ / (2 * ‖ψ‖), by positivity⟩
  let b : ℝ≥0 := ⟨‖ψ‖ / (2 * ‖ξ‖), by positivity⟩
  have ha : (a : ℝ) = ‖ξ‖ / (2 * ‖ψ‖) := rfl
  have hb : (b : ℝ) = ‖ψ‖ / (2 * ‖ξ‖) := rfl
  let m : Measure X := a • P.diag ψ + b • P.diag ξ
  have hm (B : Set X) :
      m.real B = (a : ℝ) * (P.diag ψ).real B + (b : ℝ) * (P.diag ξ).real B := by
    simp only [m]
    rw [measureReal_add_apply, measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply]
  have hmajor : (P.polarizedComplexMeasure ψ ξ).variation ≤ m := by
    apply VectorMeasure.variation_le_of_forall_eNorm_le
    intro B hB
    have hbound : ‖P.polarizedComplexMeasure ψ ξ B‖ ≤ m.real B := by
      rw [hm B, ha, hb]
      exact P.norm_polarizedComplexMeasure_apply_le B hB
    simpa only [measureReal_def, ofReal_norm] using
      (ENNReal.ofReal_le_of_le_toReal hbound)
  have hmass : m.real Set.univ = ‖ψ‖ * ‖ξ‖ := by
    rw [hm Set.univ, P.diag_real_univ, P.diag_real_univ, ha, hb]
    field_simp [ne_of_gt hψ, ne_of_gt hξ]
    ring
  calc
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤ m Set.univ := hmajor Set.univ
    _ = ENNReal.ofReal (m.real Set.univ) :=
        (ofReal_measureReal (μ := m) (s := Set.univ)).symm
    _ = ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by rw [hmass]

/-- The variation of a polarized spectral measure has the sharp mass bound. -/
theorem polarizedComplexMeasure_variation_univ_le (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation Set.univ ≤
      ENNReal.ofReal (‖ψ‖ * ‖ξ‖) := by
  by_cases hψz : ψ = 0
  · subst ψ
    rw [P.polarizedComplexMeasure_zero_left, VectorMeasure.variation_zero]
    simp
  by_cases hξz : ξ = 0
  · subst ξ
    rw [P.polarizedComplexMeasure_zero_right, VectorMeasure.variation_zero]
    simp
  exact P.polarizedComplexMeasure_variation_univ_le_of_ne_zero hψz hξz

/-- The variation of a polarized complex measure is finite. -/
instance instIsFiniteMeasurePolarizedVariation (P : ProjValMeasure X H) (ψ ξ : H) :
    IsFiniteMeasure (P.polarizedComplexMeasure ψ ξ).variation := by
  refine ⟨?_⟩
  exact (P.polarizedComplexMeasure_variation_univ_le ψ ξ).trans_lt
    ENNReal.ofReal_lt_top

/-- The variation of the diagonal polarized measure is the diagonal measure. -/
@[simp]
theorem variation_polarizedComplexMeasure_self (P : ProjValMeasure X H) (ξ : H) :
    (P.polarizedComplexMeasure ξ ξ).variation = P.diag ξ := by
  rw [polarizedComplexMeasure_self_eq_withDensityᵥ,
    Measure.variation_withDensityᵥ (integrable_const _)]
  simp

/-- Projecting the second vector onto a measurable set `B` restricts the polarized complex measure
to `B`. -/
@[simp]
theorem polarizedComplexMeasure_proj_right (P : ProjValMeasure X H) {B : Set X}
    (hB : MeasurableSet B) (ψ ξ : H) :
    P.polarizedComplexMeasure ψ (P.proj B hB ξ) = (P.polarizedComplexMeasure ψ ξ).restrict B := by
  ext C hC
  rw [P.polarizedComplexMeasure_apply ψ (P.proj B hB ξ) C hC,
    VectorMeasure.restrict_apply _ hB hC,
    P.polarizedComplexMeasure_apply ψ ξ (C ∩ B) (hC.inter hB),
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, P.proj_inter]

/-- Projecting the first vector onto a measurable set `B` restricts the polarized complex measure
to `B`. -/
@[simp]
theorem polarizedComplexMeasure_proj_left (P : ProjValMeasure X H) {B : Set X}
    (hB : MeasurableSet B) (ψ ξ : H) :
    P.polarizedComplexMeasure (P.proj B hB ψ) ξ = (P.polarizedComplexMeasure ψ ξ).restrict B := by
  ext C hC
  have hsym : ⟪P.proj B hB ψ, P.proj C hC ξ⟫_ℂ = ⟪ψ, P.proj B hB (P.proj C hC ξ)⟫_ℂ :=
    (P.isSelfAdjoint_proj B hB).isSymmetric ψ (P.proj C hC ξ)
  rw [P.polarizedComplexMeasure_apply (P.proj B hB ψ) ξ C hC, hsym,
    ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def, P.proj_mul_comm B C hB hC,
    P.proj_inter C B hC hB, ← P.polarizedComplexMeasure_apply ψ ξ (C ∩ B) (hC.inter hB),
    VectorMeasure.restrict_apply _ hB hC]

/-- **Setwise sharp variation estimate** for a polarized spectral measure: on every measurable set
`B`, the variation is bounded by `‖P(B) ψ‖ * ‖P(B) ξ‖`. -/
theorem variation_polarizedComplexMeasure_apply_le (P : ProjValMeasure X H) (ψ ξ : H)
    {B : Set X} (hB : MeasurableSet B) :
    (P.polarizedComplexMeasure ψ ξ).variation B ≤
      ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) := by
  have hrestrict :
      P.polarizedComplexMeasure (P.proj B hB ψ) (P.proj B hB ξ) =
        (P.polarizedComplexMeasure ψ ξ).restrict B := by
    rw [P.polarizedComplexMeasure_proj_right hB, P.polarizedComplexMeasure_proj_left hB,
      (P.polarizedComplexMeasure ψ ξ).restrict_restrict hB hB, Set.inter_self]
  calc (P.polarizedComplexMeasure ψ ξ).variation B
      = (P.polarizedComplexMeasure ψ ξ).variation.restrict B Set.univ := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    _ = ((P.polarizedComplexMeasure ψ ξ).restrict B).variation Set.univ := by
          rw [VectorMeasure.variation_restrict hB]
    _ = (P.polarizedComplexMeasure (P.proj B hB ψ) (P.proj B hB ξ)).variation Set.univ := by
          rw [hrestrict]
    _ ≤ ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) :=
          P.polarizedComplexMeasure_variation_univ_le _ _

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is absolutely continuous with respect to
`P.diag ξ`. -/
theorem variation_polarizedComplexMeasure_absolutelyContinuous_right
    (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≪ P.diag ξ := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hB₀ => ?_
  have hsq : ‖P.proj B hB ξ‖ₑ ^ 2 = 0 := (P.enorm_sq_proj_apply B hB ξ).trans hB₀
  rw [sq_eq_zero_iff, eNorm_eq_zero] at hsq
  exact nonpos_iff_eq_zero.1 <|
    (P.variation_polarizedComplexMeasure_apply_le ψ ξ hB).trans (by simp [hsq])

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is absolutely continuous with respect to
`P.diag ψ`. -/
theorem variation_polarizedComplexMeasure_absolutelyContinuous_left
    (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≪ P.diag ψ := by
  refine Measure.AbsolutelyContinuous.mk fun B hB hB₀ => ?_
  have hsq : ‖P.proj B hB ψ‖ₑ ^ 2 = 0 := (P.enorm_sq_proj_apply B hB ψ).trans hB₀
  rw [sq_eq_zero_iff, eNorm_eq_zero] at hsq
  exact nonpos_iff_eq_zero.1 <|
    (P.variation_polarizedComplexMeasure_apply_le ψ ξ hB).trans (by simp [hsq])

private theorem simpleFunc_lintegral_variation_polarizedComplexMeasure_le
    (P : ProjValMeasure X H) (ψ ξ : H) (φ : SimpleFunc X ℝ≥0∞) :
    φ.lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ x, φ x ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  have hstep :
      φ.lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
        ∑ c ∈ φ.range, ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ψ‖ₑ *
          (c * ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ξ‖ₑ) := by
    rw [SimpleFunc.lintegral]
    refine Finset.sum_le_sum fun c _ => ?_
    have hB := φ.measurableSet_fiber c
    have hvar : (P.polarizedComplexMeasure ψ ξ).variation (φ ⁻¹' {c}) ≤
        ‖P.proj (φ ⁻¹' {c}) hB ψ‖ₑ * ‖P.proj (φ ⁻¹' {c}) hB ξ‖ₑ := by
      refine (P.variation_polarizedComplexMeasure_apply_le ψ ξ hB).trans_eq ?_
      rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]
    calc c * (P.polarizedComplexMeasure ψ ξ).variation (φ ⁻¹' {c})
        ≤ c * (‖P.proj (φ ⁻¹' {c}) hB ψ‖ₑ * ‖P.proj (φ ⁻¹' {c}) hB ξ‖ₑ) := by gcongr
      _ = ‖P.proj (φ ⁻¹' {c}) hB ψ‖ₑ * (c * ‖P.proj (φ ⁻¹' {c}) hB ξ‖ₑ) := by ac_rfl
  have hcs := ENNReal.inner_le_Lp_mul_Lq φ.range
    (fun c => ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ψ‖ₑ)
    (fun c => c * ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ξ‖ₑ)
    Real.HolderConjugate.two_two
  have hψ :
      (∑ c ∈ φ.range, ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ψ‖ₑ ^ (2 : ℝ)) ^
          (1 / 2 : ℝ) = ‖ψ‖ₑ := by
    have hsum : ∑ c ∈ φ.range, ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ψ‖ₑ ^ (2 : ℝ) =
        ‖ψ‖ₑ ^ (2 : ℝ) := by
      have h1 : (1 : SimpleFunc X ℝ≥0∞).lintegral (P.diag ψ) = ‖ψ‖ₑ ^ 2 := by
        rw [← SimpleFunc.lintegral_eq_lintegral]
        simp [P.diag_univ ψ]
      calc ∑ c ∈ φ.range, ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ψ‖ₑ ^ (2 : ℝ)
          = ∑ c ∈ φ.range, 1 * (P.diag ψ) (φ ⁻¹' {c}) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [ENNReal.rpow_ofNat, P.enorm_sq_proj_apply, one_mul]
        _ = (φ.map fun _ => (1 : ℝ≥0∞)).lintegral (P.diag ψ) :=
              (SimpleFunc.map_lintegral (fun _ => (1 : ℝ≥0∞)) φ).symm
        _ = ‖ψ‖ₑ ^ (2 : ℝ) := by
              have hmap : φ.map (fun _ => (1 : ℝ≥0∞)) = 1 := by ext; rfl
              rw [hmap, h1, ENNReal.rpow_ofNat]
    rw [hsum, ← ENNReal.rpow_mul, mul_one_div_cancel (by positivity), ENNReal.rpow_one]
  have hξ :
      ∑ c ∈ φ.range, (c * ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ξ‖ₑ) ^ (2 : ℝ) =
        ∫⁻ x, φ x ^ 2 ∂(P.diag ξ) := by
    calc ∑ c ∈ φ.range, (c * ‖P.proj (φ ⁻¹' {c}) (φ.measurableSet_fiber c) ξ‖ₑ) ^ (2 : ℝ)
        = ∑ c ∈ φ.range, c ^ 2 * (P.diag ξ) (φ ⁻¹' {c}) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [ENNReal.rpow_ofNat, mul_pow, P.enorm_sq_proj_apply]
      _ = (φ.map fun y => y ^ 2).lintegral (P.diag ξ) :=
            (SimpleFunc.map_lintegral (fun y : ℝ≥0∞ => y ^ 2) φ).symm
      _ = ∫⁻ x, φ x ^ 2 ∂(P.diag ξ) := by
            rw [← SimpleFunc.lintegral_eq_lintegral]
            rfl
  exact hstep.trans (by rwa [hψ, hξ] at hcs)

/-- **Cauchy–Schwarz domination** for integration against the variation of a polarized spectral
measure: for every `g : X → ℝ≥0∞`, the lower Lebesgue integral of `g` against
`(P.polarizedComplexMeasure ψ ξ).variation` is bounded by
`‖ψ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`. -/
theorem lintegral_variation_polarizedComplexMeasure_le
    (P : ProjValMeasure X H) (ψ ξ : H) (g : X → ℝ≥0∞) :
    ∫⁻ x, g x ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ x, g x ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  rw [lintegral_def]
  refine iSup₂_le fun φ hφ =>
    (simpleFunc_lintegral_variation_polarizedComplexMeasure_le P ψ ξ φ).trans ?_
  gcongr with x
  exact hφ x

/-- A function that is almost everywhere strongly measurable for the variation of
`P.polarizedComplexMeasure ψ ξ` and has finite second moment against `P.diag ξ` is integrable
against `(P.polarizedComplexMeasure ψ ξ).variation`. -/
theorem integrable_variation_polarizedComplexMeasure_of_lintegral_pow_two_lt_top
    {E : Type*} [SeminormedAddCommGroup E] (P : ProjValMeasure X H) (ψ ξ : H) {f : X → E}
    (hf : AEStronglyMeasurable f (P.polarizedComplexMeasure ψ ξ).variation)
    (hξ : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(P.diag ξ) < ∞) :
    Integrable f (P.polarizedComplexMeasure ψ ξ).variation := by
  refine ⟨hf, (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun x => ‖f x‖ₑ).trans_lt ?_⟩
  exact ENNReal.mul_lt_top eNorm_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hξ.ne)

/-- **Cauchy–Schwarz `L¹`–`L²` bound** for the variation of a polarized spectral measure: whenever
`x ↦ ‖f x‖ ^ 2` is integrable against `P.diag ξ`,
`∫ x, ‖f x‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤ ‖ψ‖ * √(∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le
    {E : Type*} [SeminormedAddCommGroup E] (P : ProjValMeasure X H) (ψ ξ : H) {f : X → E}
    (hξ : Integrable (fun x => ‖f x‖ ^ 2) (P.diag ξ)) :
    ∫ x, ‖f x‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ * Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ)) := by
  by_cases hint : Integrable (fun x => ‖f x‖) (P.polarizedComplexMeasure ψ ξ).variation
  · have hlin : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂(P.diag ξ) = ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hξ (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      refine lintegral_congr fun x => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have hle := P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun x => ‖f x‖ₑ
    have hpow : ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂(P.diag ξ))) := by
      rw [Real.sqrt_eq_rpow,
        ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun _ => sq_nonneg _) (by positivity)]
    rw [hlin, hpow, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)] at hle
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      hint.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    refine (lintegral_congr fun x => ?_).trans_le hle
    rw [ofReal_norm]
  · rw [integral_undef hint]
    positivity

end TauCeti.ProjValMeasure
