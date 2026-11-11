/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Basic
public import TauCeti.Analysis.Distribution.TestFunction.FormCurrent
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The mass of the current of a form

Let `E` be an oriented real vector space of dimension `j + l` and `Ω` an open subset of `E`. The
current `[ω] ζ = ∫_Ω ω ∧ ζ` of a `j`-form `ω` (`Orientation.formCurrent`) has mass controlled by
the `L¹` norm of `ω`: for every additive Haar measure `μ` there is a constant `C`, depending only
on `μ` and the degrees, with

`localMass [ω] U ≤ C ∫_{Ω ∩ U} ‖ω‖ dμ`

for every form `ω` and every set `U` (`Orientation.exists_localMass_formCurrent_le`). In particular
the current of a form that is locally integrable on `Ω` has locally finite mass
(`Orientation.hasLocallyFiniteMass_formCurrent`). The pointwise norm is the operator norm of
alternating maps, as in `Distribution.mass`. The constant comes from the bound
`‖ω ∧ ζ‖ ≤ (j + l).choose j ‖ω‖ ‖ζ‖` and the comparison of `μ` with the Haar measure of a basis.

A uniform bound on `∫_Ω ‖ω‖` for a family of forms therefore bounds the masses of their currents
uniformly, which places them in a weakly compact set
(`Distribution.isCompact_image_coe_mass_le`).

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7.
-/

public section

namespace Orientation

open MeasureTheory TopologicalSpace TestFunction Module ContinuousAlternatingMap Distribution
open scoped Distributions ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {j l : ℕ} {n : ℕ∞}

/-- **Mass of the current of a form.** For an additive Haar measure `μ` there is a constant `C`
with `localMass [ω] U ≤ C ∫_{Ω ∩ U} ‖ω‖ dμ` for every `j`-form `ω` and every set `U`, where
`[ω] ζ = ∫_Ω ω ∧ ζ` is the current of `ω`. -/
theorem exists_localMass_formCurrent_le (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ C : ℝ≥0, ∀ (ω : E → E [⋀^Fin j]→L[ℝ] ℝ) (U : Set E),
      localMass (o.formCurrent Ω ω : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) U ≤
        C * ∫⁻ x in Ω ∩ U, ‖ω x‖ₑ ∂μ := by
  by_cases h : finrank ℝ E = j + l
  swap
  · exact ⟨0, fun ω U ↦ by simp [formCurrent_eq_zero_of_finrank_ne o Ω ω h, localMass_zero]⟩
  let b := finBasisOfFinrankEq ℝ E h
  let c := Measure.addHaarScalarFactor b.addHaar μ
  let K : ℝ≥0 := (j + l).choose j * ∏ i, ‖b i‖₊
  refine ⟨K * c, fun ω U ↦ localMass_le_iff.2 fun ζ hζU hζ ↦ ?_⟩
  by_cases hω : LocallyIntegrableOn ω Ω μ
  swap
  · simp [formCurrent_of_not_locallyIntegrableOn o Ω hω]
  rw [formCurrent_apply_eq_signBasis_mul o Ω b hω, enorm_mul]
  have hsign : ‖(o.signBasis b : ℝ)‖ₑ = 1 := by
    rcases Int.units_eq_one_or (o.signBasis b) with hs | hs <;> simp [hs]
  have hsupp : tsupport ζ ⊆ Ω ∩ U := Set.subset_inter ζ.tsupport_subset hζU
  -- Pointwise, `|(ω ∧ ζ) b| ≤ K ‖ω‖`, and the integrand vanishes off the support of `ζ`.
  have hpt (x : E) : ‖wedge (ω x) (ζ x) b‖ₑ ≤ (tsupport ζ).indicator (fun x ↦ K * ‖ω x‖ₑ) x := by
    by_cases hx : x ∈ tsupport ζ
    · rw [Set.indicator_of_mem hx, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal,
        ← ENNReal.ofReal_mul (by positivity)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ‖wedge (ω x) (ζ x) b‖ ≤ ‖wedge (ω x) (ζ x)‖ * ∏ i, ‖b i‖ :=
            (wedge (ω x) (ζ x)).le_opNorm _
        _ ≤ (j + l).choose j * ‖ω x‖ * ‖ζ x‖ * ∏ i, ‖b i‖ := by
            gcongr
            exact norm_wedge_le _ _
        _ ≤ (j + l).choose j * ‖ω x‖ * 1 * ∏ i, ‖b i‖ := by
            gcongr
            exact hζ x
        _ = K * ‖ω x‖ := by simp [K]; ring
    · simp [Set.indicator_of_notMem hx, image_eq_zero_of_notMem_tsupport hx, wedge_def]
  calc ‖(o.signBasis b : ℝ)‖ₑ * ‖∫ x, wedge (ω x) (ζ x) b ∂b.addHaar‖ₑ
      ≤ ∫⁻ x, ‖wedge (ω x) (ζ x) b‖ₑ ∂b.addHaar := by
        rw [hsign, one_mul]
        exact enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ x, (tsupport ζ).indicator (fun x ↦ K * ‖ω x‖ₑ) x ∂b.addHaar := lintegral_mono hpt
    _ = ∫⁻ x in tsupport ζ, K * ‖ω x‖ₑ ∂b.addHaar :=
        lintegral_indicator (isClosed_tsupport _).measurableSet _
    _ ≤ ∫⁻ x in Ω ∩ U, K * ‖ω x‖ₑ ∂b.addHaar := lintegral_mono_set hsupp
    _ = (K * c : ℝ≥0) * ∫⁻ x in Ω ∩ U, ‖ω x‖ₑ ∂μ := by
        rw [Measure.isAddLeftInvariant_eq_smul b.addHaar μ, Measure.restrict_smul,
          lintegral_smul_measure, lintegral_const_mul' _ _ ENNReal.coe_ne_top, ENNReal.smul_def,
          smul_eq_mul]
        push_cast
        ring

/-- **Global mass of the current of a form.** For an additive Haar measure `μ` there is a constant
`C` with `mass [ω] ≤ C ∫_Ω ‖ω‖ dμ` for every `j`-form `ω`. -/
theorem exists_mass_formCurrent_le (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    ∃ C : ℝ≥0, ∀ ω : E → E [⋀^Fin j]→L[ℝ] ℝ,
      mass (o.formCurrent Ω ω : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) ≤
        C * ∫⁻ x in Ω, ‖ω x‖ₑ ∂μ := by
  obtain ⟨C, hC⟩ := o.exists_localMass_formCurrent_le (n := n) Ω μ
  exact ⟨C, fun ω ↦ by simpa [localMass_univ] using hC ω Set.univ⟩

/-- The current of a form that is locally integrable on `Ω` has **locally finite mass**. -/
theorem hasLocallyFiniteMass_formCurrent (o : Orientation ℝ E (Fin (j + l))) (Ω : Opens E)
    {μ : Measure E} [μ.IsAddHaarMeasure] {ω : E → E [⋀^Fin j]→L[ℝ] ℝ}
    (hω : LocallyIntegrableOn ω Ω μ) :
    HasLocallyFiniteMass (o.formCurrent Ω ω : 𝓓^{n}(Ω, E [⋀^Fin l]→L[ℝ] ℝ) →L[ℝ] ℝ) := by
  obtain ⟨C, hC⟩ := o.exists_localMass_formCurrent_le (n := n) Ω μ
  refine (hasLocallyFiniteMass_iff_localMass_ne_top _).2 fun K hK hKΩ ↦ ?_
  have hint : IntegrableOn ω K μ := hω.integrableOn_compact_subset hKΩ hK
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ?_) (hC ω K)
  rw [Set.inter_eq_right.2 hKΩ]
  exact hint.hasFiniteIntegral.ne

end Orientation
