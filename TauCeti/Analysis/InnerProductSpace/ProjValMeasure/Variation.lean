/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6, The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Null
public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Polarization
public import Mathlib.MeasureTheory.VectorMeasure.Integral
public import Mathlib.MeasureTheory.VectorMeasure.Variation.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# Variation and Cauchy–Schwarz estimates for polarized spectral measures

For the complex measure `P.polarizedComplexMeasure ψ ξ` associated with a normalized
projection-valued measure, we prove

`(P.polarizedComplexMeasure ψ ξ).variation univ ≤ ofReal (‖ψ‖ * ‖ξ‖)`

and, by restricting to any measurable set `B` via `P.proj B hB`, the local bound

`(P.polarizedComplexMeasure ψ ξ).variation B ≤ ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖)`.

Summing over measurable partitions and applying Cauchy–Schwarz yields the `L²` domination
`∫⁻ t, g t ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
  ‖ψ‖ₑ * (∫⁻ t, g t ^ 2 ∂(P.diag ξ)) ^ (1 / 2)`.

In particular, every measurable symbol `f : X → ℂ` with finite second spectral moment against
`P.diag ξ` is integrable against `P.polarizedComplexMeasure ψ ξ` for every `ψ : H`, with
`∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤ ‖ψ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ))`.

On the diagonal, the variation of `P.polarizedComplexMeasure ξ ξ` is `P.diag ξ`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, AMS GSM 99, 2009, §3.1, Theorem 3.2.
* The underlying PVM and polarized-measure constructions are adapted from the
  AIQ-Kitware DKPS formalization (Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization.
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

/-- On any measurable set `B`, the variation of `P.polarizedComplexMeasure ψ ξ` is bounded by
`‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖`. -/
theorem variation_polarizedComplexMeasure_apply_le (P : ProjValMeasure X H) (ψ ξ : H)
    {B : Set X} (hB : MeasurableSet B) :
    (P.polarizedComplexMeasure ψ ξ).variation B ≤
      ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) := by
  calc
    (P.polarizedComplexMeasure ψ ξ).variation B
        = ((P.polarizedComplexMeasure ψ ξ).restrict B).variation Set.univ := by
          rw [VectorMeasure.variation_restrict hB, Measure.restrict_apply_univ]
    _ = (P.polarizedComplexMeasure (P.proj B hB ψ) (P.proj B hB ξ)).variation Set.univ := by
          rw [P.polarizedComplexMeasure_proj_proj ψ ξ B hB]
    _ ≤ ENNReal.ofReal (‖P.proj B hB ψ‖ * ‖P.proj B hB ξ‖) :=
          P.polarizedComplexMeasure_variation_univ_le _ _

/-- Extended-norm form of `variation_polarizedComplexMeasure_apply_le`. -/
theorem variation_polarizedComplexMeasure_apply_le_enorm (P : ProjValMeasure X H) (ψ ξ : H)
    {B : Set X} (hB : MeasurableSet B) :
    (P.polarizedComplexMeasure ψ ξ).variation B ≤
      ‖P.proj B hB ψ‖ₑ * ‖P.proj B hB ξ‖ₑ := by
  refine (P.variation_polarizedComplexMeasure_apply_le ψ ξ hB).trans_eq ?_
  rw [ENNReal.ofReal_mul (norm_nonneg _), ofReal_norm, ofReal_norm]

/-- The variation of `P.polarizedComplexMeasure ψ ξ` is dominated by the sum of the two diagonal
measures `P.diag ψ + P.diag ξ`. -/
theorem variation_polarizedComplexMeasure_le_add_diag (P : ProjValMeasure X H) (ψ ξ : H) :
    (P.polarizedComplexMeasure ψ ξ).variation ≤ P.diag ψ + P.diag ξ := by
  refine Measure.le_iff.2 fun B hB => ?_
  rw [_root_.add_apply, ← P.enorm_sq_proj_apply B hB ψ, ← P.enorm_sq_proj_apply B hB ξ]
  refine (P.variation_polarizedComplexMeasure_apply_le_enorm ψ ξ hB).trans ?_
  rcases le_total ‖P.proj B hB ψ‖ₑ ‖P.proj B hB ξ‖ₑ with hle | hle
  · calc
      ‖P.proj B hB ψ‖ₑ * ‖P.proj B hB ξ‖ₑ ≤ ‖P.proj B hB ξ‖ₑ ^ 2 := by
        rw [sq]; gcongr
      _ ≤ ‖P.proj B hB ψ‖ₑ ^ 2 + ‖P.proj B hB ξ‖ₑ ^ 2 := le_add_self
  · calc
      ‖P.proj B hB ψ‖ₑ * ‖P.proj B hB ξ‖ₑ ≤ ‖P.proj B hB ψ‖ₑ ^ 2 := by
        rw [sq]; gcongr
      _ ≤ ‖P.proj B hB ψ‖ₑ ^ 2 + ‖P.proj B hB ξ‖ₑ ^ 2 := le_self_add

/-- Statements holding `P`-almost everywhere hold almost everywhere for the variation of every
polarized complex measure of `P`. -/
theorem ae_variation_polarizedComplexMeasure_of_ae (P : ProjValMeasure X H) (ψ ξ : H)
    {R : X → Prop} (hR : ∀ᶠ x in P.ae, R x) :
    ∀ᵐ x ∂(P.polarizedComplexMeasure ψ ξ).variation, R x :=
  Measure.absolutelyContinuous_of_le (P.variation_polarizedComplexMeasure_le_add_diag ψ ξ)
    (ae_add_measure_iff.2 ⟨P.ae_diag_of_ae ψ hR, P.ae_diag_of_ae ξ hR⟩)

/-- Cauchy–Schwarz bound for simple nonnegative functions integrated against the variation of a
polarized complex measure. -/
private theorem simpleFunc_lintegral_variation_polarizedComplexMeasure_le
    (P : ProjValMeasure X H) (ψ ξ : H) (s : SimpleFunc X ℝ≥0∞) :
    s.lintegral (P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ t, s t ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  have hcs := ENNReal.inner_le_Lp_mul_Lq s.range
    (fun c => ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ)
    (fun c => c * ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ξ‖ₑ) .two_two
  have h1 : ∑ c ∈ s.range, (‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ) ^ (2 : ℝ) ≤
      ‖ψ‖ₑ ^ 2 := by
    simp_rw [ENNReal.rpow_two, P.enorm_sq_proj_apply]
    rw [← P.diag_univ ψ]
    exact sum_measure_le_measure_univ
      (fun c _ => (s.measurableSet_fiber c).nullMeasurableSet)
      (fun _ _ _ _ hne => (Disjoint.preimage s (Set.disjoint_singleton.2 hne)).aedisjoint)
  have h1' : (∑ c ∈ s.range, (‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ) ^ (2 : ℝ)) ^
      (1 / 2 : ℝ) ≤ ‖ψ‖ₑ := by
    calc
      _ ≤ (‖ψ‖ₑ ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h1 (by positivity)
      _ = ‖ψ‖ₑ := by rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul, mul_one_div_cancel two_ne_zero,
        ENNReal.rpow_one]
  have h2 : ∑ c ∈ s.range, (c * ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ξ‖ₑ) ^ (2 : ℝ) =
      ∫⁻ t, s t ^ 2 ∂(P.diag ξ) := by
    have hmap : ∫⁻ t, s t ^ 2 ∂(P.diag ξ) = (s.map (· ^ 2)).lintegral (P.diag ξ) := by
      simpa [SimpleFunc.coe_map] using (s.map (· ^ 2)).lintegral_eq_lintegral (P.diag ξ)
    rw [hmap, SimpleFunc.map_lintegral]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.rpow_two, ENNReal.rpow_two,
      P.enorm_sq_proj_apply]
  calc
    s.lintegral (P.polarizedComplexMeasure ψ ξ).variation
        = ∑ c ∈ s.range, c * (P.polarizedComplexMeasure ψ ξ).variation (s ⁻¹' {c}) := rfl
    _ ≤ ∑ c ∈ s.range,
          ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ψ‖ₑ *
            (c * ‖P.proj (s ⁻¹' {c}) (s.measurableSet_fiber c) ξ‖ₑ) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [mul_left_comm]
        have hvar := P.variation_polarizedComplexMeasure_apply_le_enorm ψ ξ
          (s.measurableSet_fiber c)
        gcongr
    _ ≤ ‖ψ‖ₑ * (∫⁻ t, s t ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
        refine hcs.trans ?_
        rw [h2]
        gcongr

/-- **Cauchy–Schwarz domination** for Lebesgue integration against the variation of a polarized
spectral measure: `∫⁻ g d|μ_(ψ,ξ)| ≤ ‖ψ‖ₑ * (∫⁻ g² d(P.diag ξ))^(1/2)`. -/
theorem lintegral_variation_polarizedComplexMeasure_le (P : ProjValMeasure X H) (ψ ξ : H)
    (g : X → ℝ≥0∞) :
    ∫⁻ t, g t ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ₑ * (∫⁻ t, g t ^ 2 ∂(P.diag ξ)) ^ (1 / 2 : ℝ) := by
  rw [lintegral_def]
  refine iSup₂_le fun s hs => ?_
  refine (P.simpleFunc_lintegral_variation_polarizedComplexMeasure_le ψ ξ s).trans ?_
  gcongr with t
  exact hs t

/-- Every measurable symbol `f : X → ℂ` with finite second spectral moment against `P.diag ξ` is
integrable against the polarized complex measure `P.polarizedComplexMeasure ψ ξ`. -/
theorem integrable_polarizedComplexMeasure_of_lintegral_sq_lt_top (P : ProjValMeasure X H)
    (ψ ξ : H) {f : X → ℂ} (hf : Measurable f)
    (hξ : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) < ∞) :
    (P.polarizedComplexMeasure ψ ξ).Integrable f := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  refine (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hξ.ne)

/-- **Cauchy–Schwarz bound** for the real variation integral of a measurable symbol:
`∫ t, ‖f t‖ ∂|μ_(ψ,ξ)| ≤ ‖ψ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ))`. -/
theorem integral_norm_variation_polarizedComplexMeasure_le (P : ProjValMeasure X H) (ψ ξ : H)
    {f : X → ℂ} (hf : Measurable f) (hξ : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) < ∞) :
    ∫ t, ‖f t‖ ∂(P.polarizedComplexMeasure ψ ξ).variation ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  have hle := ENNReal.toReal_mono
    (ENNReal.mul_ne_top eNorm_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hξ.ne))
    (P.lintegral_variation_polarizedComplexMeasure_le ψ ξ fun t => ‖f t‖ₑ)
  rw [← integral_norm_eq_lintegral_eNorm hf.aestronglyMeasurable] at hle
  refine hle.trans_eq ?_
  have hsq : ∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂(P.diag ξ) = ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) := by
    refine lintegral_congr fun t => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← Real.sqrt_eq_rpow,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hf.norm.pow_const 2).aestronglyMeasurable,
    hsq]
  simp

/-- **Cauchy–Schwarz bound** for integration against a polarized complex measure:
`‖∫ᵛ t, f t ∂[mul ℝ ℂ; μ_(ψ,ξ)]‖ ≤ ‖ψ‖ * √(∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ))`. -/
theorem norm_integral_polarizedComplexMeasure_le (P : ProjValMeasure X H) (ψ ξ : H)
    {f : X → ℂ} (hf : Measurable f) (hξ : ∫⁻ t, ‖f t‖ₑ ^ 2 ∂(P.diag ξ) < ∞) :
    ‖∫ᵛ t, f t ∂[ContinuousLinearMap.mul ℝ ℂ; P.polarizedComplexMeasure ψ ξ]‖ ≤
      ‖ψ‖ * Real.sqrt (∫ t, ‖f t‖ ^ 2 ∂(P.diag ξ)) := by
  refine VectorMeasure.norm_integral_le_integral_norm.trans ?_
  rw [ContinuousLinearMap.opNorm_mul, one_mul]
  exact P.integral_norm_variation_polarizedComplexMeasure_le ψ ξ hf hξ

end TauCeti.ProjValMeasure
