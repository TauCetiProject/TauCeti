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
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Group.Arithmetic

/-!
# The multiplicative Haar measure `dt / t` on the positive reals

`TauCeti.multHaar` is the measure `dt / t` on `ℝ`, concentrated on `(0, ∞)`: Lebesgue measure on
`(0, ∞)` with density `t⁻¹`. It is the image of Lebesgue measure under `Real.exp`
(`TauCeti.map_volume_exp`); in particular `Real.exp` is quasi-measure-preserving from Lebesgue
measure to Lebesgue measure on `(0, ∞)` (`TauCeti.quasiMeasurePreserving_exp`). It is invariant
under every dilation `t ↦ c t` with `c > 0` (`TauCeti.map_multHaar_mul_left`,
`TauCeti.eLpNorm_comp_mul_left_multHaar`), is invariant under
inversion (`TauCeti.map_multHaar_inv`), and gives the interval `[1, e]` mass one. The power map
`t ↦ t ^ γ`, `γ ≠ 0`, sends it to `|γ|⁻¹ dt / t` (`TauCeti.map_multHaar_rpow`), so it multiplies
`L^q(dt / t)` seminorms by `|γ| ^ (-1 / q)` (`TauCeti.eLpNorm_comp_rpow_multHaar`).

The map `t ↦ c / t` for `c > 0` preserves `dt / t`
(`TauCeti.measurePreserving_div_left_multHaar`).
At a positive cutoff `a`, the reflection `t ↦ a² / t` carries the upper ray to the lower part of
`(0, ∞)` with their restricted measures (`TauCeti.measurePreserving_sq_div_multHaar_restrict_Ioi`).
Under reciprocal symmetry, integrability is equivalent to integrability on the upper ray
(`TauCeti.integrable_multHaar_iff_of_sq_div`), and the full integral at a positive cutoff is twice
the upper-ray integral (`TauCeti.integral_multHaar_eq_two_smul_of_sq_div`).

It is the Haar measure of the multiplicative group `(0, ∞)` up to a scalar, and the scalar is
read off `[1, e]`: a measure on `ℝ` that does not charge `(-∞, 0]`, is invariant under the
positive dilations and is finite on `[1, e]` is its mass on `[1, e]` times `dt / t`
(`TauCeti.eq_smul_multHaar`). Through `Real.log` this is the uniqueness of additive Haar measure
on `ℝ`, Mathlib's `MeasureTheory.Measure.isAddLeftInvariant_eq_smul`. It is the form in which a
radial coordinate is split off a multiplicative Haar measure, as in the decomposition
`dy / y = d*x × dt / t` of the archimedean parameters of a number field.

Integrating against `dt / t` is integrating `t⁻¹ f(t)` over `(0, ∞)`
(`TauCeti.lintegral_multHaar_eq_setLIntegral`, `TauCeti.setLIntegral_multHaar_eq_setLIntegral`,
`TauCeti.setLIntegral_eq_setLIntegral_multHaar`, `TauCeti.integral_multHaar_eq_setIntegral`,
`TauCeti.integrable_multHaar_iff`); in particular `∫_a^b dt / t = log b - log a`
(`TauCeti.setLIntegral_Icc_ofReal_inv`). `dt / t` and Lebesgue measure on `(0, ∞)` are mutually
absolutely continuous (`TauCeti.multHaar_absolutelyContinuous_volume_Ioi`,
`TauCeti.volume_Ioi_absolutelyContinuous_multHaar`) and share the same almost-everywhere filter
(`TauCeti.ae_multHaar_eq_ae_volume_Ioi`), converting `Lᵖ(0, ∞)` seminorms into weighted
`Lᵖ(dt / t)` seminorms (`TauCeti.eLpNorm_volume_Ioi_eq_eLpNorm_multHaar`), and a right-continuous
function on `(0, ∞)` has `dt / t`-essential supremum equal to its pointwise supremum
(`TauCeti.essSup_multHaar_eq_iSup_Ioi`). Half-line power integrals evaluate explicitly
(`TauCeti.lintegral_Iic_multHaar_rpow`, `TauCeti.lintegral_Ici_multHaar_rpow_neg`). In
particular the Mellin transform `mellin f s = ∫_0^∞ t^(s-1) f(t) dt` is the integral of
`t^s f(t)` against `dt / t` (`TauCeti.integral_multHaar_cpow_smul`), and Mathlib's
`MellinConvergent` is the integrability of `t^s f(t)` against `dt / t`
(`TauCeti.integrable_multHaar_cpow_smul_iff`). The integral of `u ^ α min 1 u⁻¹ ^ (α + β)` against
`du / u` is `α⁻¹ + β⁻¹` (`TauCeti.lintegral_multHaar_rpow_mul_min_inv_rpow`), and by dilation the
kernel `s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)` has integral `θ₀⁻¹ + θ₁⁻¹` in each variable
(`TauCeti.lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_right`,
`TauCeti.lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_left`).

For `b > 1` the geometric intervals `[c b ^ (μ j), c b ^ (μ j + |μ|))`, `j ∈ ℕ`, are pairwise
disjoint, each of `dt / t`-measure `|μ| log b`. Integrating over them compares a sequence with a
function that dominates its `j`-th term on the `j`-th interval: the sum of the sequence is at most
`(|μ| log b)⁻¹` times the integral (`TauCeti.ofReal_mul_tsum_le_lintegral_multHaar`), and likewise
for `ℓ^q` and `L^q(dt / t)` norms (`TauCeti.ofReal_rpow_mul_eLpNorm_count_le_eLpNorm_multHaar`).
The intervals with `j ∈ ℤ` give the same comparison for two-sided sequences
(`TauCeti.ofReal_mul_tsum_int_le_lintegral_multHaar`). This is how dyadic sums are bounded by
integrals against `dt / t`.
-/

public section

open MeasureTheory Measure Set
open scoped ENNReal Topology

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

/-- The exponential is quasi-measure-preserving from Lebesgue measure to Lebesgue measure on
`(0, ∞)`: preimages under `Real.exp` of null subsets of `(0, ∞)` are null. -/
theorem quasiMeasurePreserving_exp :
    QuasiMeasurePreserving Real.exp volume (volume.restrict (Ioi (0 : ℝ))) :=
  ⟨Real.measurable_exp.aemeasurable, by
    rw [map_volume_exp, multHaar_def]
    exact withDensity_absolutelyContinuous _ _⟩

/-- `dt / t` gives an interval `[a, b]` with `0 < a ≤ b` mass `log b - log a`. -/
theorem multHaar_Icc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    multHaar (Icc a b) = ENNReal.ofReal (Real.log b - Real.log a) := by
  have hpre : Real.exp ⁻¹' Icc a b = Icc (Real.log a) (Real.log b) := by
    ext u
    simp [Real.log_le_iff_le_exp ha, Real.le_log_iff_exp_le (ha.trans_le hab)]
  rw [← map_volume_exp, map_apply Real.measurable_exp measurableSet_Icc, hpre, Real.volume_Icc]

/-- `dt / t` gives an interval `[a, b)` with `0 < a ≤ b` mass `log b - log a`. -/
theorem multHaar_Ico {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    multHaar (Ico a b) = ENNReal.ofReal (Real.log b - Real.log a) := by
  have hpre : Real.exp ⁻¹' Ico a b = Ico (Real.log a) (Real.log b) := by
    ext u
    simp [Real.log_le_iff_le_exp ha, Real.lt_log_iff_exp_lt (ha.trans_le hab)]
  rw [← map_volume_exp, map_apply Real.measurable_exp measurableSet_Ico, hpre, Real.volume_Ico]

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

/-- Restricting `dt / t` to an upper ray with nonpositive cutoff leaves it unchanged. -/
@[simp]
theorem multHaar_restrict_Ioi_of_nonpos {a : ℝ} (ha : a ≤ 0) :
    multHaar.restrict (Ioi a) = multHaar :=
  Measure.restrict_eq_self_of_ae_mem (ae_pos_multHaar.mono fun _ ht ↦ ha.trans_lt ht)

instance : NullSingletonClass multHaar := by
  rw [multHaar_def]
  infer_instance

/-- `dt / t` and Lebesgue measure on `(0, ∞)` have the same almost-everywhere filter. -/
theorem ae_multHaar_eq_ae_volume_Ioi :
    ae multHaar = ae (volume.restrict (Ioi (0 : ℝ))) := by
  rw [multHaar_def]
  refine le_antisymm (withDensity_absolutelyContinuous _ _).ae_le
    (withDensity_absolutelyContinuous' measurable_inv.ennreal_ofReal.aemeasurable ?_).ae_le
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
  exact (ENNReal.ofReal_pos.2 (inv_pos.2 ht)).ne'

/-- `dt / t` is absolutely continuous with respect to Lebesgue measure on `(0, ∞)`. -/
theorem multHaar_absolutelyContinuous_volume_Ioi :
    multHaar ≪ volume.restrict (Ioi (0 : ℝ)) :=
  Measure.ae_le_iff_absolutelyContinuous.1 ae_multHaar_eq_ae_volume_Ioi.le

/-- Lebesgue measure on `(0, ∞)` is absolutely continuous with respect to `dt / t`. -/
theorem volume_Ioi_absolutelyContinuous_multHaar :
    volume.restrict (Ioi (0 : ℝ)) ≪ multHaar :=
  Measure.ae_le_iff_absolutelyContinuous.1 ae_multHaar_eq_ae_volume_Ioi.ge

/-- A function is almost everywhere strongly measurable for Lebesgue measure on `(0, ∞)` if and
only if it is almost everywhere strongly measurable for `dt / t`. -/
theorem aestronglyMeasurable_volume_Ioi_iff_multHaar {β : Type*} [TopologicalSpace β]
    {f : ℝ → β} :
    AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) ↔ AEStronglyMeasurable f multHaar :=
  ⟨fun h ↦ h.mono_ac multHaar_absolutelyContinuous_volume_Ioi,
    fun h ↦ h.mono_ac volume_Ioi_absolutelyContinuous_multHaar⟩

/-- A function continuous on `(0, ∞)` is almost everywhere strongly measurable for `dt / t`. -/
theorem _root_.ContinuousOn.aestronglyMeasurable_multHaar {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] {f : ℝ → β} (hf : ContinuousOn f (Ioi 0)) :
    AEStronglyMeasurable f multHaar :=
  (hf.aestronglyMeasurable measurableSet_Ioi).mono_ac multHaar_absolutelyContinuous_volume_Ioi

/-- `dt / t` is invariant under the dilations `t ↦ c t`, `c > 0`. -/
theorem map_multHaar_mul_left {c : ℝ} (hc : 0 < c) : multHaar.map (c * ·) = multHaar := by
  have hcomp : (c * ·) ∘ Real.exp = Real.exp ∘ (Real.log c + ·) := by
    ext u
    simp [Real.exp_add, Real.exp_log hc]
  rw [← map_volume_exp, map_map (measurable_const_mul c) Real.measurable_exp, hcomp,
    ← map_map Real.measurable_exp (measurable_const_add _), map_add_left_eq_self]

/-- The `L^q(dt / t)` seminorm is invariant under the dilations `t ↦ c * t`, `c > 0`. -/
theorem eLpNorm_comp_mul_left_multHaar {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    (f : ℝ → ε) {c : ℝ} (hc : 0 < c) (q : ℝ≥0∞) :
    eLpNorm (fun t ↦ f (c * t)) q multHaar = eLpNorm f q multHaar := by
  rw [← Function.comp_def, ← (measurableEmbedding_mulLeft₀ hc.ne').eLpNorm_map_measure,
    map_multHaar_mul_left hc]

/-- The image of `dt / t` under the power map `t ↦ t ^ γ`, `γ ≠ 0`, is `|γ|⁻¹ dt / t`. -/
theorem map_multHaar_rpow {γ : ℝ} (hγ : γ ≠ 0) :
    multHaar.map (· ^ γ) = ENNReal.ofReal |γ⁻¹| • multHaar := by
  have hcomp : (· ^ γ) ∘ Real.exp = Real.exp ∘ (γ * ·) := by
    ext u
    simp [← Real.exp_mul, mul_comm]
  rw [← map_volume_exp, map_map (measurable_id'.pow_const γ) Real.measurable_exp, hcomp,
    ← map_map Real.measurable_exp (measurable_const_mul γ), Real.map_volume_mul_left hγ,
    Measure.map_smul]
  exact Real.measurable_exp.aemeasurable

/-- Under the power map `t ↦ t ^ γ`, `γ ≠ 0`, the `L^q(dt / t)` seminorm is multiplied by
`|γ| ^ (-1 / q)`: `‖g (t ^ γ)‖_{L^q(dt / t)} = |γ| ^ (-1 / q) ‖g‖_{L^q(dt / t)}`, read in `[0, ∞]`
as `|γ⁻¹| ^ (1 / q)`. -/
theorem eLpNorm_comp_rpow_multHaar {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {g : ℝ → ε} (hg : AEStronglyMeasurable g multHaar) {γ : ℝ} (hγ : γ ≠ 0) (q : ℝ≥0∞) :
    eLpNorm (fun t ↦ g (t ^ γ)) q multHaar =
      ENNReal.ofReal |γ⁻¹| ^ (1 / q).toReal * eLpNorm g q multHaar := by
  have hc : ENNReal.ofReal |γ⁻¹| ≠ 0 := by simpa using hγ
  have hmap := map_multHaar_rpow hγ
  rw [← Function.comp_def, ← eLpNorm_map_measure (hmap ▸ hg.smul_measure _)
    (measurable_id'.pow_const γ).aemeasurable, hmap, eLpNorm_smul_measure_of_ne_zero hc,
    smul_eq_mul]

/-- `dt / t` is invariant under inversion on `(0, ∞)`. -/
theorem map_multHaar_inv : multHaar.map Inv.inv = multHaar := by
  have hcomp : Inv.inv ∘ Real.exp = Real.exp ∘ Neg.neg := by
    ext u
    simp [Real.exp_neg]
  rw [← map_volume_exp, map_map measurable_inv Real.measurable_exp, hcomp,
    ← map_map Real.measurable_exp measurable_neg, map_neg_eq_self]

/-- Division of a positive constant by the variable preserves `dt / t`. -/
theorem measurePreserving_div_left_multHaar {c : ℝ} (hc : 0 < c) :
    MeasurePreserving (c / ·) multHaar multHaar := by
  simpa only [Function.comp_def, div_eq_mul_inv] using
    MeasurePreserving.comp ⟨measurable_const_mul c, map_multHaar_mul_left hc⟩
      ⟨measurable_inv, map_multHaar_inv⟩

/-- Reciprocal reflection about a positive cutoff carries `dt / t` on the upper ray to
`dt / t` on the lower ray. -/
theorem measurePreserving_sq_div_multHaar_restrict_Ioi {a : ℝ} (ha : 0 < a) :
    MeasurePreserving (fun t : ℝ ↦ a ^ 2 / t) (multHaar.restrict (Ioi a))
      (multHaar.restrict (Ioo 0 a)) := by
  have hsq := sq_pos_of_pos ha
  have hcomp : (fun t : ℝ ↦ a ^ 2 / t) = (a ^ 2 * ·) ∘ Inv.inv :=
    funext fun t ↦ div_eq_mul_inv _ t
  have hpre : (fun t : ℝ ↦ a ^ 2 / t) ⁻¹' Ioo 0 a = Ioi a := by
    rw [hcomp, preimage_comp, preimage_const_mul_Ioo₀ _ _ hsq, zero_div, inv_preimage,
      inv_Ioo_0_left (div_pos ha hsq)]
    simp only [inv_div, pow_two, mul_div_cancel_left₀ _ ha.ne']
  simpa only [hpre] using
    (measurePreserving_div_left_multHaar hsq).restrict_preimage
      (measurableSet_Ioo (a := 0) (b := a))

section Fold

variable {E : Type*} [NormedAddCommGroup E] {f : ℝ → E} {a : ℝ}

/-- In the presence of reciprocal symmetry, integrability over `dt / t` can be checked just
above the symmetry point. -/
theorem integrable_multHaar_iff_of_sq_div
    (hsym : ∀ᵐ t ∂multHaar.restrict (Ioi a), f (a ^ 2 / t) = f t) :
    Integrable f multHaar ↔ IntegrableOn f (Ioi a) multHaar := by
  by_cases hnonpos : a ≤ 0
  · rw [IntegrableOn, multHaar_restrict_Ioi_of_nonpos hnonpos]
  have ha := lt_of_not_ge hnonpos
  refine ⟨fun h ↦ h.integrableOn, fun h ↦ ?_⟩
  have hlow := ((measurePreserving_sq_div_multHaar_restrict_Ioi ha).integrable_comp_emb
    (measurableEmbedding_divLeft₀ (pow_ne_zero 2 ha.ne')) (g := f)).mp
      (h.congr (Filter.EventuallyEq.symm hsym))
  have hleft : IntegrableOn f (Ioc 0 a) multHaar := by
    simpa only [IntegrableOn, Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := multHaar))] using hlow
  -- Use `(0,a]` and `(a,∞)` to cover the support of the measure.
  have hfull := hleft.union h
  rwa [Ioc_union_Ioi_eq_Ioi ha.le, IntegrableOn, multHaar_restrict_Ioi_of_nonpos le_rfl] at hfull

/-- A reciprocally symmetric function has twice its upper-ray integral against `dt / t`.
If the upper-ray integral is not integrable, both Bochner integrals have the junk value zero. -/
theorem integral_multHaar_eq_two_smul_of_sq_div [NormedSpace ℝ E] (ha : 0 < a)
    (hsym : ∀ᵐ t ∂multHaar.restrict (Ioi a), f (a ^ 2 / t) = f t) :
    ∫ t, f t ∂multHaar = 2 • ∫ t in Ioi a, f t ∂multHaar := by
  by_cases h : IntegrableOn f (Ioi a) multHaar
  · have hfull := (integrable_multHaar_iff_of_sq_div hsym).mpr h
    have hlow : (∫ t in Ioc 0 a, f t ∂multHaar) = ∫ t in Ioi a, f t ∂multHaar := by
      have hp := measurePreserving_sq_div_multHaar_restrict_Ioi ha
      rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := multHaar)).symm,
        ← hp.integral_comp (measurableEmbedding_divLeft₀ (pow_ne_zero 2 ha.ne')) f]
      exact integral_congr_ae hsym
    calc
      _ = ∫ t in Ioc 0 a ∪ Ioi a, f t ∂multHaar := by
        rw [Ioc_union_Ioi_eq_Ioi ha.le, multHaar_restrict_Ioi_of_nonpos le_rfl]
      _ = _ := by
        rw [setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi hfull.integrableOn h,
          hlow, two_nsmul]
  · rw [integral_undef (mt (integrable_multHaar_iff_of_sq_div hsym).mp h),
      integral_undef h, smul_zero]

end Fold

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

/-! ### Disjoint geometric intervals -/

section GeometricIntervals

/-- For `1 ≤ b`, the interval `[c b ^ x, c b ^ (x + |μ|))` has `dt / t`-measure `|μ| log b`. -/
theorem multHaar_Ico_mul_rpow {b c : ℝ} (hb : 1 ≤ b) (hc : 0 < c) (x μ : ℝ) :
    multHaar (Ico (c * b ^ x) (c * b ^ (x + |μ|))) = ENNReal.ofReal (|μ| * Real.log b) := by
  have hb0 : 0 < b := zero_lt_one.trans_le hb
  rw [multHaar_Ico (by positivity) (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hb (by simp)) hc.le),
    Real.log_mul hc.ne' (by positivity), Real.log_mul hc.ne' (by positivity),
    Real.log_rpow hb0, Real.log_rpow hb0]
  ring_nf

/-- For `1 ≤ b`, the intervals `[c b ^ (μ j), c b ^ (μ j + |μ|))` for `j ∈ ℤ` are pairwise
disjoint and have `dt / t`-measure `|μ| log b`. So if `g j ≤ f` on the `j`-th interval, then
`|μ| log b ∑ j, g j ≤ ∫ f dt / t`. -/
theorem ofReal_mul_tsum_int_le_lintegral_multHaar {b c μ : ℝ} (hb : 1 ≤ b) (hc : 0 < c)
    {f : ℝ → ℝ≥0∞} {g : ℤ → ℝ≥0∞}
    (h : ∀ j : ℤ, ∀ r ∈ Ico (c * b ^ (μ * j)) (c * b ^ (μ * j + |μ|)), g j ≤ f r) :
    ENNReal.ofReal (|μ| * Real.log b) * ∑' j, g j ≤ ∫⁻ r, f r ∂multHaar := by
  set S : ℤ → Set ℝ := fun j ↦ Ico (c * b ^ (μ * j)) (c * b ^ (μ * j + |μ|))
  have hS (j : ℤ) : multHaar (S j) = ENNReal.ofReal (|μ| * Real.log b) :=
    multHaar_Ico_mul_rpow hb hc _ μ
  have hdisj : Pairwise (Function.onFun Disjoint S) := by
    intro j k hjk
    have h1 : (1 : ℝ) ≤ |(j : ℝ) - k| := by
      rcases lt_or_gt_of_ne hjk with h | h
      · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_pos (by linarith)]
        linarith
      · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast h
        rw [abs_of_pos (by linarith)]
        linarith
    have hgap : |μ| ≤ |μ * j - μ * k| := by
      rw [← mul_sub, abs_mul]
      exact le_mul_of_one_le_right (abs_nonneg μ) h1
    simp only [Function.onFun, S, Set.Ico_disjoint_Ico]
    rcases le_total (μ * j) (μ * k) with hjk' | hjk'
    · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hjk')] at hgap
      exact (min_le_left _ _).trans <| (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) hc.le).trans (le_max_right _ _)
    · rw [abs_of_nonneg (sub_nonneg.2 hjk')] at hgap
      exact (min_le_right _ _).trans <| (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hb (by linarith)) hc.le).trans (le_max_left _ _)
  calc ENNReal.ofReal (|μ| * Real.log b) * ∑' j, g j = ∑' j, ∫⁻ _ in S j, g j ∂multHaar := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun j ↦ by rw [setLIntegral_const, hS, mul_comm]
    _ ≤ ∑' j, ∫⁻ r in S j, f r ∂multHaar :=
        tsum_le_tsum fun j ↦ setLIntegral_mono' measurableSet_Ico (h j)
    _ = ∫⁻ r in ⋃ j, S j, f r ∂multHaar :=
        (lintegral_iUnion (fun _ ↦ measurableSet_Ico) hdisj f).symm
    _ ≤ ∫⁻ r, f r ∂multHaar := setLIntegral_le_lintegral _ _

/-- The one-sided form of `ofReal_mul_tsum_int_le_lintegral_multHaar`: for `1 ≤ b`, if `g j ≤ f`
on the interval `[c b ^ (μ j), c b ^ (μ j + |μ|))` for every `j ∈ ℕ`, then
`|μ| log b ∑ j, g j ≤ ∫ f dt / t`. -/
theorem ofReal_mul_tsum_le_lintegral_multHaar {b c μ : ℝ} (hb : 1 ≤ b) (hc : 0 < c)
    {f : ℝ → ℝ≥0∞} {g : ℕ → ℝ≥0∞}
    (h : ∀ j : ℕ, ∀ r ∈ Ico (c * b ^ (μ * j)) (c * b ^ (μ * j + |μ|)), g j ≤ f r) :
    ENNReal.ofReal (|μ| * Real.log b) * ∑' j, g j ≤ ∫⁻ r, f r ∂multHaar := by
  -- extend `g` by zero to the negative indices
  rw [← tsum_extend_zero (Nat.cast_injective (R := ℤ)) g]
  refine ofReal_mul_tsum_int_le_lintegral_multHaar hb hc fun j r hr ↦ ?_
  by_cases hj : ∃ n : ℕ, (n : ℤ) = j
  · obtain ⟨n, rfl⟩ := hj
    rw [Nat.cast_injective.extend_apply]
    exact h n r (by simpa using hr)
  · rw [Function.extend_apply' _ _ _ hj, Pi.zero_apply]
    exact zero_le

/-- The `L^q` form of `ofReal_mul_tsum_le_lintegral_multHaar`: for `1 < b`, if `g j ≤ ‖f‖` on the
interval `[c b ^ (μ j), c b ^ (μ j + |μ|))`, then the `ℓ^q` norm of `g`, written as its `L^q`
seminorm for the counting measure, is at most `(|μ| log b) ^ (-1 / q)` times the `L^q(dt / t)`
norm of `f`. -/
theorem ofReal_rpow_mul_eLpNorm_count_le_eLpNorm_multHaar {b c μ : ℝ} {q : ℝ≥0∞} (hb : 1 < b)
    (hc : 0 < c) (hμ : μ ≠ 0) {ε : Type*} [TopologicalSpace ε] [ENorm ε] {f : ℝ → ε}
    (hf : AEStronglyMeasurable f multHaar) {g : ℕ → ℝ≥0∞}
    (h : ∀ j : ℕ, ∀ r ∈ Ico (c * b ^ (μ * j)) (c * b ^ (μ * j + |μ|)), g j ≤ ‖f r‖ₑ) :
    ENNReal.ofReal (|μ| * Real.log b) ^ q.toReal⁻¹ * eLpNorm g q count ≤
      eLpNorm f q multHaar := by
  have hL : 0 < |μ| * Real.log b := mul_pos (abs_pos.2 hμ) (Real.log_pos hb)
  rcases eq_or_ne q 0 with rfl | hq
  · rw [eLpNorm_exponent_zero .of_discrete, mul_zero]
    exact bot_le
  rcases eq_or_ne q ∞ with rfl | hq_top
  · -- `q = ∞`: each `g j` is below `‖f‖` on a set of positive measure
    rw [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul,
      eLpNorm_exponent_top .of_discrete, eLpNormEssSup_count, eLpNorm_exponent_top hf]
    refine iSup_le fun j ↦ ?_
    by_contra! hlt
    have hnull := ae_iff.1 (ae_lt_of_essSup_lt hlt)
    refine (ENNReal.ofReal_pos.2 hL).ne' ?_
    rw [← multHaar_Ico_mul_rpow hb.le hc (μ * j) μ]
    refine measure_mono_null (fun r hr ↦ ?_) hnull
    simp only [eNorm_eq_self, not_lt]
    exact h j r hr
  · -- finite `q`: integrate `g j ^ q ≤ ‖f‖ ^ q` over the intervals
    have hr : 0 < q.toReal := ENNReal.toReal_pos hq hq_top
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq hq_top .of_discrete, lintegral_count,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hq hq_top hf, one_div,
      ← ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hr.le)]
    refine ENNReal.rpow_le_rpow (ofReal_mul_tsum_le_lintegral_multHaar hb.le hc fun j r hr' ↦ ?_)
      (inv_nonneg.2 hr.le)
    simp only [eNorm_eq_self]
    exact ENNReal.rpow_le_rpow (h j r hr') hr.le

end GeometricIntervals

/-! ### Integrals against `dt / t` -/

section Integral

/-- The lower integral against `dt / t` is the lower integral of `t⁻¹ * f t` over `(0, ∞)`. -/
theorem lintegral_multHaar_eq_setLIntegral (f : ℝ → ℝ≥0∞) :
    ∫⁻ t, f t ∂multHaar = ∫⁻ t in Ioi 0, ENNReal.ofReal t⁻¹ * f t := by
  rw [multHaar_def, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    measurable_inv.ennreal_ofReal (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rfl

/-- On any measurable set `s`, the lower integral against `dt / t` is the lower integral of
`t⁻¹ * f t` over `s ∩ (0, ∞)`. -/
theorem setLIntegral_multHaar_eq_setLIntegral {s : Set ℝ} (hs : MeasurableSet s)
    (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in s, f t ∂multHaar = ∫⁻ t in s ∩ Ioi 0, ENNReal.ofReal t⁻¹ * f t := by
  rw [← lintegral_indicator hs, lintegral_multHaar_eq_setLIntegral,
    ← Measure.restrict_restrict hs, ← lintegral_indicator hs]
  exact setLIntegral_congr_fun measurableSet_Ioi fun t _ ↦
    (indicator_mul_right s (fun u ↦ ENNReal.ofReal u⁻¹) f).symm

/-- On a measurable subset `s` of `(0, ∞)`, the Lebesgue lower integral of `f` is the lower
integral of `t * f t` against `dt / t`. -/
theorem setLIntegral_eq_setLIntegral_multHaar {s : Set ℝ} (hs : MeasurableSet s)
    (hs0 : s ⊆ Ioi 0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ t in s, f t = ∫⁻ t in s, ENNReal.ofReal t * f t ∂multHaar := by
  rw [setLIntegral_multHaar_eq_setLIntegral hs, inter_eq_self_of_subset_left hs0]
  refine setLIntegral_congr_fun hs fun t ht ↦ ?_
  have ht0 : 0 < t := hs0 ht
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 ht0.le), inv_mul_cancel₀ ht0.ne',
    ENNReal.ofReal_one, one_mul]

/-- `∫_a^b dt / t = log b - log a` for `0 < a ≤ b`, as a Lebesgue lower integral. -/
theorem setLIntegral_Icc_ofReal_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ t in Icc a b, ENNReal.ofReal t⁻¹ = ENNReal.ofReal (Real.log b - Real.log a) := by
  rw [← multHaar_Icc ha hab, ← setLIntegral_one,
    setLIntegral_multHaar_eq_setLIntegral measurableSet_Icc,
    inter_eq_self_of_subset_left fun _ (ht : _ ∈ Icc a b) ↦ ha.trans_le ht.1]
  simp only [mul_one]

/-- A function with values in `ℝ≥0∞` that is right continuous on `(0, ∞)` has essential supremum
with respect to `dt / t` equal to its pointwise supremum on `(0, ∞)`. -/
theorem essSup_multHaar_eq_iSup_Ioi {f : ℝ → ℝ≥0∞}
    (hf : ∀ t > 0, ContinuousWithinAt f (Ici t) t) :
    essSup f multHaar = ⨆ t > 0, f t := by
  refine le_antisymm
    (essSup_le_of_ae_le _ (ae_pos_multHaar.mono fun t ht ↦ le_iSup₂_of_le t ht le_rfl))
    (iSup₂_le fun t ht ↦ ?_)
  by_contra! hlt
  obtain ⟨u, htu, hu⟩ := mem_nhdsGE_iff_exists_Ico_subset.1
    ((hf t ht).eventually (IsOpen.mem_nhds isOpen_Ioi hlt))
  have hpos : 0 < multHaar (Ico t u) := by
    rw [multHaar_Ico ht htu.le, ENNReal.ofReal_pos, sub_pos]
    exact Real.log_lt_log ht htu
  exact hpos.ne' (measure_mono_null hu (meas_essSup_lt (f := f)))

/-- A function `f : ℝ → ℝ≥0∞` is almost everywhere strongly measurable on `(0, ∞)` if and only
if `t ↦ ENNReal.ofReal (t ^ γ) * f t` is almost everywhere strongly measurable for `dt / t`. -/
theorem aestronglyMeasurable_volume_Ioi_iff_multHaar_rpow_mul (γ : ℝ) {f : ℝ → ℝ≥0∞} :
    AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))) ↔
      AEStronglyMeasurable (fun t : ℝ ↦ ENNReal.ofReal (t ^ γ) * f t) multHaar := by
  rw [aestronglyMeasurable_volume_Ioi_iff_multHaar]
  have hmul (c : ℝ) {g : ℝ → ℝ≥0∞} (hg : AEStronglyMeasurable g multHaar) :
      AEStronglyMeasurable (fun t : ℝ ↦ ENNReal.ofReal (t ^ c) * g t) multHaar :=
    ((by fun_prop : Measurable fun t : ℝ ↦
      ENNReal.ofReal (t ^ c)).aemeasurable.mul hg.aemeasurable).aestronglyMeasurable
  refine ⟨hmul γ, fun hf ↦ (hmul (-γ) hf).congr ?_⟩
  filter_upwards [ae_pos_multHaar] with t ht
  simp [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht]

/-- The `Lᵖ(0, ∞)` seminorm of `f : ℝ → ℝ≥0∞` is the `Lᵖ(dt / t)` seminorm of
`t ↦ t ^ (1 / p) * f t`. -/
theorem eLpNorm_volume_Ioi_eq_eLpNorm_multHaar {p : ℝ≥0∞} (f : ℝ → ℝ≥0∞) :
    eLpNorm f p (volume.restrict (Ioi 0)) =
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * f t) p multHaar := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict (Ioi 0))
  swap
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      eLpNorm_of_not_aestronglyMeasurable
        (mt (aestronglyMeasurable_volume_Ioi_iff_multHaar_rpow_mul p.toReal⁻¹).2 hf)]
  have hf' := (aestronglyMeasurable_volume_Ioi_iff_multHaar_rpow_mul p.toReal⁻¹).1 hf
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLpNorm_exponent_zero hf, eLpNorm_exponent_zero hf']
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLpNorm_exponent_top hf, eLpNorm_exponent_top hf', eLpNormEssSup_eq_essSup_eNorm,
      eLpNormEssSup_eq_essSup_eNorm]
    simp only [eNorm_eq_self, ENNReal.toReal_top, inv_zero, Real.rpow_zero, ENNReal.ofReal_one,
      one_mul]
    exact le_antisymm (essSup_mono_measure volume_Ioi_absolutelyContinuous_multHaar)
      (essSup_mono_measure multHaar_absolutelyContinuous_volume_Ioi)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop hf,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop hf']
  simp only [eNorm_eq_self]
  congr 1
  rw [lintegral_multHaar_eq_setLIntegral]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
  have hcancel : ENNReal.ofReal t⁻¹ * ENNReal.ofReal (t ^ p.toReal⁻¹) ^ p.toReal = 1 := by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity), Real.rpow_inv_rpow ht.le hp_pos.ne',
      ← ENNReal.ofReal_mul (by positivity)]
    simp [ht.ne']
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp_pos.le, ← mul_assoc, hcancel, one_mul]

private theorem setLIntegral_multHaar_rpow {s : Set ℝ} (hs : MeasurableSet s) (α : ℝ) :
    ∫⁻ x in s, ENNReal.ofReal (x ^ α) ∂multHaar =
      ∫⁻ x in s ∩ Ioi 0, ENNReal.ofReal (x ^ (α - 1)) := by
  rw [setLIntegral_multHaar_eq_setLIntegral hs]
  refine setLIntegral_congr_fun (hs.inter measurableSet_Ioi) fun x hx ↦ ?_
  rw [← ENNReal.ofReal_mul (inv_nonneg.2 hx.2.le), mul_comm, ← div_eq_mul_inv,
    ← Real.rpow_sub_one hx.2.ne']

/-- `∫_{s ≤ t} s ^ θ ds / s = t ^ θ / θ` for `0 < θ` and `0 < t`. -/
theorem lintegral_Iic_multHaar_rpow {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∫⁻ s in Iic t, ENNReal.ofReal (s ^ θ) ∂multHaar = ENNReal.ofReal (t ^ θ * θ⁻¹) := by
  rw [setLIntegral_multHaar_rpow measurableSet_Iic, Set.Iic_inter_Ioi,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, lintegral_ofReal_rpow_Ioo (by linarith) ht.le,
    sub_add_cancel, div_eq_mul_inv]

/-- `∫_{s ≥ t} s ^ (-θ) ds / s = t ^ (-θ) / θ` for `0 < θ` and `0 < t`. -/
theorem lintegral_Ici_multHaar_rpow_neg {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t) :
    ∫⁻ s in Ici t, ENNReal.ofReal (s ^ (-θ)) ∂multHaar = ENNReal.ofReal (t ^ (-θ) * θ⁻¹) := by
  rw [setLIntegral_multHaar_rpow measurableSet_Ici,
    inter_eq_self_of_subset_left (Ici_subset_Ioi.2 ht), ← Measure.restrict_congr_set Ioi_ae_eq_Ici,
    lintegral_ofReal_rpow_Ioi_of_lt (by linarith) ht, sub_add_cancel, neg_div_neg_eq,
    div_eq_mul_inv]

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

/-- `∫ u ^ α min 1 u⁻¹ ^ (α + β) du / u = α⁻¹ + β⁻¹` for `α, β > 0`: the integrand is `u ^ α` on
`(0, 1]` and `u ^ (-β)` on `[1, ∞)`. -/
theorem lintegral_multHaar_rpow_mul_min_inv_rpow {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫⁻ u, ENNReal.ofReal (u ^ α * min 1 u⁻¹ ^ (α + β)) ∂multHaar =
      ENNReal.ofReal (α⁻¹ + β⁻¹) := by
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (1 : ℝ))), compl_Iic,
    Measure.restrict_congr_set Ioi_ae_eq_Ici,
    ENNReal.ofReal_add (inv_nonneg.2 hα.le) (inv_nonneg.2 hβ.le)]
  congr 1
  · calc ∫⁻ u in Iic 1, ENNReal.ofReal (u ^ α * min 1 u⁻¹ ^ (α + β)) ∂multHaar
        = ∫⁻ u in Iic 1, ENNReal.ofReal (u ^ α) ∂multHaar := by
          refine lintegral_congr_ae
            (((ae_restrict_of_ae ae_pos_multHaar).and (ae_restrict_mem measurableSet_Iic)).mono
              fun u ⟨hu, hu1⟩ ↦ ?_)
          dsimp only
          rw [min_eq_left ((one_le_inv₀ hu).2 hu1), Real.one_rpow, mul_one]
      _ = ENNReal.ofReal α⁻¹ := by
          rw [lintegral_Iic_multHaar_rpow hα one_pos, Real.one_rpow, one_mul]
  · calc ∫⁻ u in Ici 1, ENNReal.ofReal (u ^ α * min 1 u⁻¹ ^ (α + β)) ∂multHaar
        = ∫⁻ u in Ici 1, ENNReal.ofReal (u ^ (-β)) ∂multHaar := by
          refine setLIntegral_congr_fun measurableSet_Ici fun u (hu1 : 1 ≤ u) ↦ ?_
          have hu : 0 < u := zero_lt_one.trans_le hu1
          rw [min_eq_right (inv_le_one_of_one_le₀ hu1), ← Real.rpow_neg_one,
            ← Real.rpow_mul hu.le, ← Real.rpow_add hu]
          ring_nf
      _ = ENNReal.ofReal β⁻¹ := by
          rw [lintegral_Ici_multHaar_rpow_neg hβ one_pos, Real.one_rpow, one_mul]

/-- The kernel `s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)` has integral `θ₀⁻¹ + θ₁⁻¹` in `r`
for every `s > 0`: the substitution `r = s u` turns it into `u ^ θ₁ min 1 u⁻¹ ^ (θ₀ + θ₁)`. -/
theorem lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_right {θ₀ θ₁ s : ℝ} (hθ₀ : 0 < θ₀)
    (hθ₁ : 0 < θ₁) (hs : 0 < s) :
    ∫⁻ r, ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) ∂multHaar =
      ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) := by
  have hmp : MeasurePreserving (s * ·) multHaar multHaar :=
    ⟨measurable_const_mul s, map_multHaar_mul_left hs⟩
  rw [← hmp.lintegral_comp (by fun_prop), add_comm θ₀⁻¹,
    ← lintegral_multHaar_rpow_mul_min_inv_rpow hθ₁ hθ₀]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_multHaar] with u hu
  congr 1
  have hm : min s⁻¹ (s * u)⁻¹ = s⁻¹ * min 1 u⁻¹ := by
    rw [mul_min_of_nonneg _ _ (inv_nonneg.2 hs.le), mul_one, mul_inv]
  rw [hm, Real.mul_rpow (inv_nonneg.2 hs.le) (le_min zero_le_one (inv_nonneg.2 hu.le)),
    Real.mul_rpow hs.le hu.le, Real.inv_rpow hs.le, add_comm θ₁ θ₀, Real.rpow_add hs]
  field_simp

/-- The kernel `s ^ θ₀ r ^ θ₁ min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)` has integral `θ₀⁻¹ + θ₁⁻¹` in `s`
for every `r > 0`, by the symmetry of the kernel under exchanging `(s, θ₀)` and `(r, θ₁)`. -/
theorem lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_left {θ₀ θ₁ r : ℝ} (hθ₀ : 0 < θ₀)
    (hθ₁ : 0 < θ₁) (hr : 0 < r) :
    ∫⁻ s, ENNReal.ofReal (s ^ θ₀ * r ^ θ₁ * min s⁻¹ r⁻¹ ^ (θ₀ + θ₁)) ∂multHaar =
      ENNReal.ofReal (θ₀⁻¹ + θ₁⁻¹) := by
  rw [add_comm θ₀⁻¹, ← lintegral_multHaar_rpow_mul_rpow_mul_min_inv_rpow_right hθ₁ hθ₀ hr]
  refine lintegral_congr fun s ↦ ?_
  rw [mul_comm (s ^ θ₀), min_comm, add_comm θ₀]

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

/-- No pure complex power `t ↦ (t : ℂ) ^ z` is integrable against `dt / t`, because
`t ^ (Re z - 1)` is not integrable on `(0, ∞)` for any `z : ℂ`. -/
theorem not_integrable_multHaar_cpow (z : ℂ) :
    ¬ Integrable (fun t : ℝ ↦ (t : ℂ) ^ z) multHaar := by
  intro h
  refine not_integrableOn_Ioi_rpow (z - 1).re ?_
  have hm : IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (z - 1) • (1 : ℂ)) (Ioi 0) :=
    integrable_multHaar_cpow_smul_iff.mp (by simpa only [smul_eq_mul, mul_one] using h)
  refine IntegrableOn.congr_fun hm.norm (fun t ht ↦ ?_) measurableSet_Ioi
  rw [smul_eq_mul, mul_one, Complex.norm_cpow_eq_rpow_re_of_pos ht]

/-- Because no pure complex power `t ↦ (t : ℂ) ^ z` is integrable against `dt / t`, its Bochner
integral vanishes for every `z : ℂ`. -/
theorem integral_multHaar_cpow_eq_zero (z : ℂ) :
    ∫ t : ℝ, (t : ℂ) ^ z ∂multHaar = 0 :=
  integral_undef (not_integrable_multHaar_cpow z)

end Mellin

end TauCeti
