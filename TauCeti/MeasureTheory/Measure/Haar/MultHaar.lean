/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# The multiplicative Haar measure `dt / t` on the positive reals

`TauCeti.multHaar` is the measure `dt / t` on `ℝ`, concentrated on `(0, ∞)`: Lebesgue measure on
`(0, ∞)` with density `t⁻¹`. It is the image of Lebesgue measure under `Real.exp`
(`TauCeti.map_volume_exp`), so it is invariant under every dilation `t ↦ c t` with `c > 0`
(`TauCeti.map_multHaar_mul_left`), is invariant under inversion (`TauCeti.map_multHaar_inv`),
and gives the interval `[1, e]` mass one.

It is the Haar measure of the multiplicative group `(0, ∞)` up to a scalar, and the scalar is
read off `[1, e]`: a measure on `ℝ` that does not charge `(-∞, 0]`, is invariant under the
positive dilations and is finite on `[1, e]` is its mass on `[1, e]` times `dt / t`
(`TauCeti.eq_smul_multHaar`). Through `Real.log` this is the uniqueness of additive Haar measure
on `ℝ`, Mathlib's `MeasureTheory.Measure.isAddLeftInvariant_eq_smul`. It is the form in which a
radial coordinate is split off a multiplicative Haar measure, as in the decomposition
`dy / y = d*x × dt / t` of the archimedean parameters of a number field.

Integrating against `dt / t` is integrating `t⁻¹ f(t)` over `(0, ∞)`
(`TauCeti.integral_multHaar_eq_setIntegral`, `TauCeti.integrable_multHaar_iff`). In particular the
Mellin transform `mellin f s = ∫_0^∞ t^(s-1) f(t) dt` is the integral of `t^s f(t)` against
`dt / t` (`TauCeti.integral_multHaar_cpow_smul`), and Mathlib's `MellinConvergent` is the
integrability of `t^s f(t)` against `dt / t` (`TauCeti.integrable_multHaar_cpow_smul_iff`).
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal

namespace TauCeti

/-- The multiplicative Haar measure `dt / t` on `ℝ`: Lebesgue measure on `(0, ∞)` with density
`t⁻¹`. -/
noncomputable def multHaar : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal t⁻¹

/-- The defining formula of `dt / t`, as Lebesgue measure on `(0, ∞)` with density `t⁻¹`. -/
theorem multHaar_def :
    multHaar = (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal t⁻¹ := (rfl)

instance : SigmaFinite multHaar := by
  rw [multHaar_def]
  infer_instance

/-- `dt / t` is the image of Lebesgue measure under the exponential. -/
theorem map_volume_exp : volume.map Real.exp = multHaar := by
  ext s hs
  have himage : s ∩ Ioi 0 = Real.exp '' (Real.exp ⁻¹' s) := by
    ext t
    constructor
    · rintro ⟨hts, ht⟩
      exact ⟨Real.log t, by rwa [mem_preimage, Real.exp_log ht], Real.exp_log ht⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨hu, Real.exp_pos u⟩
  rw [map_apply Real.measurable_exp hs, multHaar_def, withDensity_apply _ hs, restrict_restrict hs,
    himage, lintegral_image_eq_lintegral_abs_deriv_mul (Real.measurable_exp hs)
      (fun u _ ↦ (Real.hasDerivAt_exp u).hasDerivWithinAt) Real.exp_injective.injOn,
    ← setLIntegral_one]
  refine setLIntegral_congr_fun (Real.measurable_exp hs) fun u _ ↦ ?_
  rw [abs_of_pos (Real.exp_pos u), ← ENNReal.ofReal_mul (Real.exp_pos u).le,
    mul_inv_cancel₀ (Real.exp_ne_zero u), ENNReal.ofReal_one]

/-- `dt / t` gives an interval `[a, b]` with `0 < a ≤ b` mass `log b - log a`. -/
theorem multHaar_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    multHaar (Icc a b) = ENNReal.ofReal (Real.log b - Real.log a) := by
  have hpre : Real.exp ⁻¹' Icc a b = Icc (Real.log a) (Real.log b) := by
    ext u
    simp [Real.log_le_iff_le_exp ha, Real.le_log_iff_exp_le (ha.trans_le hab)]
  rw [← map_volume_exp, map_apply Real.measurable_exp measurableSet_Icc, hpre, Real.volume_Icc]

/-- `dt / t` gives the interval `[1, e]` mass one. -/
@[simp]
theorem multHaar_Icc_one_exp_one : multHaar (Icc 1 (Real.exp 1)) = 1 := by
  rw [multHaar_Icc one_pos (Real.one_le_exp zero_le_one), Real.log_exp, Real.log_one, sub_zero,
    ENNReal.ofReal_one]

/-- `dt / t` does not charge `(-∞, 0]`. -/
@[simp]
theorem multHaar_Iic_zero : multHaar (Iic 0) = 0 := by
  rw [← map_volume_exp, map_apply Real.measurable_exp measurableSet_Iic]
  convert measure_empty (μ := (volume : Measure ℝ))
  exact eq_empty_of_forall_notMem fun u hu ↦ (Real.exp_pos u).not_ge hu

/-- `dt / t`-almost every point is positive. -/
theorem ae_pos_multHaar : ∀ᵐ t ∂multHaar, 0 < t :=
  ae_iff.2 (by simp only [not_lt]; exact multHaar_Iic_zero)

/-- A function continuous on `(0, ∞)` is almost everywhere strongly measurable for `dt / t`. -/
theorem _root_.ContinuousOn.aestronglyMeasurable_multHaar {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] {f : ℝ → β} (hf : ContinuousOn f (Ioi 0)) :
    AEStronglyMeasurable f multHaar := by
  rw [multHaar_def]
  exact (hf.aestronglyMeasurable measurableSet_Ioi).mono_ac
    (withDensity_absolutelyContinuous _ _)

/-- `dt / t` is invariant under the dilations `t ↦ c t`, `c > 0`. -/
theorem map_multHaar_mul_left {c : ℝ} (hc : 0 < c) : multHaar.map (c * ·) = multHaar := by
  have hcomp : (c * ·) ∘ Real.exp = Real.exp ∘ (Real.log c + ·) := by
    ext u
    simp [Real.exp_add, Real.exp_log hc]
  rw [← map_volume_exp, map_map (measurable_const_mul c) Real.measurable_exp, hcomp,
    ← map_map Real.measurable_exp (measurable_const_add _), map_add_left_eq_self]

/-- `dt / t` is invariant under inversion on `(0, ∞)`. -/
theorem map_multHaar_inv : multHaar.map Inv.inv = multHaar := by
  have hcomp : Inv.inv ∘ Real.exp = Real.exp ∘ Neg.neg := by
    ext u
    simp [Real.exp_neg]
  rw [← map_volume_exp, map_map measurable_inv Real.measurable_exp, hcomp,
    ← map_map Real.measurable_exp measurable_neg, map_neg_eq_self]

/-- **Uniqueness of `dt / t`.** A measure on `ℝ` that does not charge `(-∞, 0]`, is invariant
under the dilations `t ↦ c t` for `c > 0`, and is finite on `[1, e]` is its mass on `[1, e]` times
`dt / t`. -/
theorem eq_smul_multHaar {ρ : Measure ℝ} (h0 : ρ (Iic 0) = 0)
    (hρ : ∀ c : ℝ, 0 < c → ρ.map (c * ·) = ρ) (hfin : ρ (Icc 1 (Real.exp 1)) ≠ ∞) :
    ρ = ρ (Icc 1 (Real.exp 1)) • multHaar := by
  have hae : ∀ᵐ t ∂ρ, 0 < t := ae_iff.mpr (by simp only [not_lt]; exact h0)
  -- `τ`, the image of `ρ` under `log`, is translation invariant
  set τ := ρ.map Real.log with hτ
  have hτ_inv : IsAddLeftInvariant τ := by
    refine ⟨fun a ↦ ?_⟩
    have hcomp : (a + ·) ∘ Real.log =ᵐ[ρ] Real.log ∘ (Real.exp a * ·) := by
      filter_upwards [hae] with t ht
      simp [Real.log_mul (Real.exp_ne_zero a) ht.ne']
    rw [hτ, map_map (measurable_const_add a) Real.measurable_log, map_congr hcomp,
      ← map_map Real.measurable_log (measurable_const_mul _), hρ _ (Real.exp_pos a)]
  have hτ_Icc : τ (Icc 0 1) = ρ (Icc 1 (Real.exp 1)) := by
    rw [hτ, map_apply Real.measurable_log measurableSet_Icc]
    refine measure_congr (ae_eq_set.mpr ⟨?_, ?_⟩)
    · refine measure_mono_null (fun t ⟨⟨ht0, ht1⟩, hnot⟩ ↦ ?_) h0
      rw [mem_Iic]
      by_contra! hpos
      exact hnot ⟨(Real.log_nonneg_iff hpos).mp ht0, (Real.log_le_iff_le_exp hpos).mp ht1⟩
    · refine measure_mono_null (fun t ⟨⟨ht1, hte⟩, hnot⟩ ↦ ?_) measure_empty
      exact hnot ⟨Real.log_nonneg ht1,
        (Real.log_le_iff_le_exp (one_pos.trans_le ht1)).mpr hte⟩
  have hτ_fin : IsFiniteMeasureOnCompacts τ :=
    ⟨fun _ hK ↦ measure_lt_top_of_isCompact_of_isAddLeftInvariant' (U := Icc 0 1)
      (by simp) (hτ_Icc ▸ hfin) hK⟩
  -- so it is a multiple of Lebesgue measure, and the multiple is its mass on `[0, 1]`
  have hτ_eq : τ = τ (Icc 0 1) • volume := by
    have h := isAddLeftInvariant_eq_smul τ volume
    have hc : τ (Icc 0 1) = addHaarScalarFactor τ volume := by
      conv_lhs => rw [h]
      simp [Real.volume_Icc]
    rwa [hc]
  have hρτ : ρ = τ.map Real.exp := by
    rw [hτ, map_map Real.measurable_exp Real.measurable_log]
    conv_lhs => rw [← map_id (μ := ρ)]
    exact map_congr (by filter_upwards [hae] with t ht using (Real.exp_log ht).symm)
  conv_lhs => rw [hρτ, hτ_eq]
  rw [Measure.map_smul, map_volume_exp, hτ_Icc]
  exact Real.measurable_exp.aemeasurable

/-! ### Integrals against `dt / t` -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A function is integrable against `dt / t` exactly when `t⁻¹ • f t` is integrable on
`(0, ∞)`. -/
theorem integrable_multHaar_iff {f : ℝ → E} :
    Integrable f multHaar ↔ IntegrableOn (fun t ↦ t⁻¹ • f t) (Ioi 0) := by
  rw [multHaar_def, integrable_withDensity_iff_integrable_smul'
    measurable_inv.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top), IntegrableOn]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)]

/-- The integral against `dt / t` is the integral of `t⁻¹ • f t` over `(0, ∞)`. -/
theorem integral_multHaar_eq_setIntegral (f : ℝ → E) :
    ∫ t, f t ∂multHaar = ∫ t in Ioi 0, t⁻¹ • f t := by
  rw [multHaar_def, integral_withDensity_eq_integral_toReal_smul
    measurable_inv.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr ht.le)]

end Integral

section Mellin

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- On `(0, ∞)`, `t⁻¹ • (t ^ s • v) = t ^ (s - 1) • v`. -/
private theorem inv_smul_cpow_smul {t : ℝ} (ht : 0 < t) (s : ℂ) (v : E) :
    t⁻¹ • ((t : ℂ) ^ s • v) = (t : ℂ) ^ (s - 1) • v := by
  rw [← Complex.coe_smul, smul_smul, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr ht.ne'),
    Complex.cpow_one, Complex.ofReal_inv, inv_mul_eq_div]

/-- **The Mellin transform is an integral against `dt / t`:**
`mellin f s = ∫ t ^ s f(t) dt / t`. -/
theorem integral_multHaar_cpow_smul (f : ℝ → E) (s : ℂ) :
    ∫ t, (t : ℂ) ^ s • f t ∂multHaar = mellin f s := by
  rw [integral_multHaar_eq_setIntegral, mellin]
  exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ inv_smul_cpow_smul ht s (f t)

/-- The Mellin transform of `f` converges at `s` exactly when `t ^ s f(t)` is integrable against
`dt / t`. -/
theorem integrable_multHaar_cpow_smul_iff {f : ℝ → E} {s : ℂ} :
    Integrable (fun t : ℝ ↦ (t : ℂ) ^ s • f t) multHaar ↔ MellinConvergent f s := by
  rw [integrable_multHaar_iff, MellinConvergent]
  exact integrableOn_congr_fun (fun t ht ↦ inv_smul_cpow_smul ht s (f t)) measurableSet_Ioi

end Mellin

end TauCeti
