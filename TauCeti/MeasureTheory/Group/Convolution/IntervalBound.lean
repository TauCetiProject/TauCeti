/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import TauCeti.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Measures on the real line with uniformly bounded interval masses

A measure `ν` on `ℝ` whose translates of a fixed interval `[a, b]` all have mass at most `B`
integrates every translate of a function dominated by `C` times the indicator of `[a, b]` to at
most `C * B`. Consequently, convolving such a measure with a finite measure gives a locally
finite measure, even when neither factor is compactly supported.

For a finite measure `μ` on `ℝ≥0` and a compactly supported continuous `f`, the function
`ψ z = ∫ f (x + z) dμ(x)` need not be compactly supported, but it is integrable against every
such `ν`, and `∫ ψ dν` is the integral of `f` against `μ ∗ ν`. Truncating `μ` to `[0, n]` makes
`ψ` compactly supported and changes `∫ ψ dν` by at most a multiple of `μ (n, ∞)`, uniformly in
`ν`. Consequently, convergence of the integrals of all compactly supported test functions along
measures with uniformly bounded interval masses carries over to `ψ`.

## Main results

* `MeasureTheory.lintegral_comp_add_le_of_le_indicator`: the integral of a translate of a
  function dominated by `C` times the indicator of `[a, b]` is at most `C * B`.
* `MeasureTheory.Measure.isLocallyFiniteMeasure_conv_of_measure_Icc_le`: the convolution of a
  finite measure with a measure of uniformly bounded interval masses is locally finite.
* `MeasureTheory.integral_map_coe_conv`: integrating `f` against `μ ∗ ν` is integrating
  `z ↦ ∫ f (x + z) dμ(x)` against `ν`.
* `MeasureTheory.tendsto_integral_integral_comp_add`: convergence of the integrals of compactly
  supported test functions along measures with uniformly bounded interval masses carries over to
  `z ↦ ∫ f (x + z) dμ(x)`.
-/

public section

open Set Filter Topology
open scoped ENNReal NNReal CompactlySupported

namespace MeasureTheory

/-- A function dominated by `C` times the indicator of `[a, b]` has translates whose integrals are
at most `C * B`, when `B` bounds the masses of all translates of `[a, b]`. -/
theorem lintegral_comp_add_le_of_le_indicator {ν : Measure ℝ} {g : ℝ → ℝ≥0∞} {a b : ℝ}
    {C B : ℝ≥0∞} (hg : ∀ y, g y ≤ (Icc a b).indicator (fun _ ↦ C) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (x : ℝ) :
    ∫⁻ z, g (x + z) ∂ν ≤ C * B := by
  calc ∫⁻ z, g (x + z) ∂ν ≤ ∫⁻ z, (Icc (-x + a) (-x + b)).indicator (fun _ ↦ C) z ∂ν := by
        refine lintegral_mono fun z ↦ (hg _).trans_eq ?_
        by_cases hz : z ∈ Icc (-x + a) (-x + b)
        · rw [indicator_of_mem hz, indicator_of_mem (show x + z ∈ Icc a b from
            ⟨by linarith [hz.1], by linarith [hz.2]⟩)]
        · rw [indicator_of_notMem hz, indicator_of_notMem (show x + z ∉ Icc a b from fun h ↦
            hz ⟨by linarith [h.1], by linarith [h.2]⟩)]
    _ = C * ν (Icc (-x + a) (-x + b)) := lintegral_indicator_const measurableSet_Icc C
    _ ≤ C * B := by gcongr; exact hν _

namespace Measure

/-- Convolving a finite measure with a measure whose intervals of a fixed positive length have
uniformly bounded mass gives a locally finite measure. -/
theorem isLocallyFiniteMeasure_conv_of_measure_Icc_le {ρ η : Measure ℝ} [IsFiniteMeasure ρ]
    [SFinite η] {r : ℝ} (hr : 0 < r) {B : ℝ≥0∞} (hη : ∀ c, η (Icc c (c + r)) ≤ B)
    (hB : B ≠ ∞) : IsLocallyFiniteMeasure (ρ ∗ η) := by
  refine ⟨fun x ↦ ⟨Icc (x - r / 2) (x + r / 2), Icc_mem_nhds (by linarith) (by linarith), ?_⟩⟩
  rw [← lintegral_indicator_one measurableSet_Icc,
    lintegral_conv (measurable_one.indicator measurableSet_Icc)]
  have hη' (c : ℝ) : η (Icc (c + (x - r / 2)) (c + (x + r / 2))) ≤ B := by
    have := hη (c + (x - r / 2))
    rwa [show c + (x - r / 2) + r = c + (x + r / 2) by ring] at this
  calc ∫⁻ y, ∫⁻ z, (Icc (x - r / 2) (x + r / 2)).indicator 1 (y + z) ∂η ∂ρ
      ≤ ∫⁻ y, 1 * B ∂ρ :=
        lintegral_mono fun y ↦ lintegral_comp_add_le_of_le_indicator (fun _ ↦ le_rfl) hη' y
    _ < ∞ := by
        rw [lintegral_const, one_mul]
        exact ENNReal.mul_lt_top hB.lt_top (measure_lt_top ρ _)

end Measure

section Translate

variable {μ : Measure ℝ≥0} {ν : Measure ℝ} {f : C_c(ℝ, ℝ)} {a b : ℝ} {C : ℝ≥0} {B : ℝ≥0∞}

/-- Integrating `‖f (x + z)‖ₑ` first against a measure `ν` whose translated intervals have mass
at most `B`, then against `μ` over `S`, gives at most `C * B * μ S`. -/
theorem lintegral_lintegral_enorm_comp_add_le
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (S : Set ℝ≥0) :
    ∫⁻ x in S, ∫⁻ z, ‖f (x + z)‖ₑ ∂ν ∂μ ≤ C * B * μ S :=
  calc ∫⁻ x in S, ∫⁻ z, ‖f (x + z)‖ₑ ∂ν ∂μ ≤ ∫⁻ _ in S, (C : ℝ≥0∞) * B ∂μ :=
        lintegral_mono fun x ↦ lintegral_comp_add_le_of_le_indicator hf hν x
    _ = C * B * μ S := setLIntegral_const S _

/-- The part of `x ↦ f (x + z)` integrated over `S` contributes at most `C * B * μ S` to every
integral against a measure whose translated intervals have mass at most `B`. -/
theorem lintegral_enorm_setIntegral_le [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (S : Set ℝ≥0) :
    ∫⁻ z, ‖∫ x in S, f (x + z) ∂μ‖ₑ ∂ν ≤ C * B * μ S := by
  calc ∫⁻ z, ‖∫ x in S, f (x + z) ∂μ‖ₑ ∂ν ≤ ∫⁻ z, ∫⁻ x in S, ‖f (x + z)‖ₑ ∂μ ∂ν :=
        lintegral_mono fun z ↦ eNorm_integral_le_lintegral_eNorm _
    _ = ∫⁻ x in S, ∫⁻ z, ‖f (x + z)‖ₑ ∂ν ∂μ :=
        lintegral_lintegral_swap (by fun_prop)
    _ ≤ C * B * μ S := lintegral_lintegral_enorm_comp_add_le hf hν S

/-- Integrating the translates of `f` over `S` against a finite measure gives a continuous
function. -/
theorem _root_.CompactlySupportedContinuousMap.continuous_setIntegral_comp_add [IsFiniteMeasure μ]
    (f : C_c(ℝ, ℝ)) (S : Set ℝ≥0) : Continuous fun z : ℝ ↦ ∫ x in S, f (x + z) ∂μ := by
  obtain ⟨D, hD⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  exact continuous_of_dominated (bound := fun _ ↦ D) (fun z ↦ by fun_prop)
    (fun z ↦ ae_of_all _ fun x ↦ hD _) (integrable_const D) (ae_of_all _ fun x ↦ by fun_prop)

/-- Integrating the translates of `f` over `S` against a finite measure gives a function that is
integrable against every measure whose translated intervals have uniformly bounded mass. -/
theorem integrable_setIntegral_comp_add [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (hB : B ≠ ∞) (S : Set ℝ≥0) :
    Integrable (fun z : ℝ ↦ ∫ x in S, f (x + z) ∂μ) ν :=
  ⟨(f.continuous_setIntegral_comp_add S).aestronglyMeasurable,
    (lintegral_enorm_setIntegral_le hf hν S).trans_lt (by finiteness)⟩

/-- Integrating against `μ ∗ ν` is integrating `z ↦ ∫ f (x + z) dμ(x)` against `ν`. -/
theorem integral_map_coe_conv [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (hB : B ≠ ∞) :
    ∫ y, f y ∂(μ.map ((↑) : ℝ≥0 → ℝ) ∗ ν) = ∫ z, ∫ x, f (x + z) ∂μ ∂ν := by
  have hint : Integrable f (ν ∗ μ.map ((↑) : ℝ≥0 → ℝ)) := by
    refine ⟨(map_continuous f).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, ← Measure.conv_comm, Measure.lintegral_conv (by fun_prop)]
    calc ∫⁻ y, ∫⁻ z, ‖f (y + z)‖ₑ ∂ν ∂μ.map ((↑) : ℝ≥0 → ℝ)
        ≤ ∫⁻ x, ∫⁻ z, ‖f (x + z)‖ₑ ∂ν ∂μ :=
          lintegral_map_le _ measurable_coe_nnreal_real.aemeasurable
      _ ≤ C * B * μ univ := by
          simpa using lintegral_lintegral_enorm_comp_add_le (μ := μ) hf hν univ
      _ < ∞ := by finiteness
  rw [Measure.conv_comm, integral_conv hint]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  dsimp only
  rw [integral_map measurable_coe_nnreal_real.aemeasurable (by fun_prop)]
  simp_rw [add_comm z]

/-- The part of `x ↦ f (x + z)` over `(n, ∞)` is uniformly small: splitting the integral over
`[0, n]` changes the integral against `ν` by at most `C * B * μ (n, ∞)`. -/
theorem dist_integral_setIntegral_Iic_le [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (hB : B ≠ ∞) (n : ℝ≥0) :
    dist (∫ z, ∫ x, f (x + z) ∂μ ∂ν) (∫ z, ∫ x in Iic n, f (x + z) ∂μ ∂ν) ≤
      (C * B * μ (Iic n)ᶜ).toReal := by
  obtain ⟨D, hD⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hsplit (z : ℝ) : ∫ x, f (x + z) ∂μ =
      ∫ x in Iic n, f (x + z) ∂μ + ∫ x in (Iic n)ᶜ, f (x + z) ∂μ :=
    (integral_add_compl measurableSet_Iic
      (.of_bound (by fun_prop) D (ae_of_all _ fun x ↦ hD _))).symm
  simp_rw [hsplit]
  rw [integral_add (integrable_setIntegral_comp_add hf hν hB _)
    (integrable_setIntegral_comp_add hf hν hB _), dist_eq_norm, add_sub_cancel_left,
    ← toReal_eNorm]
  exact ENNReal.toReal_mono (by finiteness) ((eNorm_integral_le_lintegral_eNorm _).trans
    (lintegral_enorm_setIntegral_le hf hν _))

/-- Restricted to `[0, n]`, the function `z ↦ ∫ f (x + z) dμ(x)` is compactly supported. -/
theorem hasCompactSupport_setIntegral_Iic
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y) (n : ℝ≥0) :
    HasCompactSupport fun z : ℝ ↦ ∫ x in Iic n, f (x + z) ∂μ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := a - n) (b := b)) fun z hz ↦
    setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  exact CompactlySupportedContinuousMap.eq_zero_of_enorm_le_indicator hf fun h ↦
    hz ⟨by linarith [h.1, NNReal.coe_le_coe.mpr hx], by linarith [h.2, x.coe_nonneg]⟩

/-- If the integrals of compactly supported test functions converge along a family of measures
whose translated intervals have uniformly bounded mass, then so do the integrals of
`z ↦ ∫ f (x + z) dμ(x)`, which need not be compactly supported. -/
theorem tendsto_integral_integral_comp_add [IsFiniteMeasure μ] {ι : Type*}
    {l : Filter ι} {ν' : ι → Measure ℝ} [∀ i, SFinite (ν' i)] [SFinite ν]
    (hlim : ∀ g : C_c(ℝ, ℝ), Tendsto (fun i ↦ ∫ x, g x ∂ν' i) l (𝓝 (∫ x, g x ∂ν)))
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν' : ∀ i c, ν' i (Icc (c + a) (c + b)) ≤ B) (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B)
    (hB : B ≠ ∞) :
    Tendsto (fun i ↦ ∫ z, ∫ x, f (x + z) ∂μ ∂ν' i) l (𝓝 (∫ z, ∫ x, f (x + z) ∂μ ∂ν)) := by
  -- The error made by truncating at `n` is at most `e n`, uniformly, and `e n → 0`.
  set e : ℕ → ℝ := fun n ↦ (C * B * μ (Iic (n : ℝ≥0))ᶜ).toReal
  have hinter : ⋂ n : ℕ, (Iic (n : ℝ≥0))ᶜ = ∅ := by
    ext x
    simpa using exists_nat_ge x
  have hμn : Tendsto (fun n : ℕ ↦ μ (Iic (n : ℝ≥0))ᶜ) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := μ)
      (fun n ↦ measurableSet_Iic.compl.nullMeasurableSet)
      (fun m n hmn ↦ compl_subset_compl.mpr (Iic_subset_Iic.mpr (Nat.cast_le.mpr hmn)))
      ⟨0, measure_ne_top μ _⟩
    rwa [hinter, measure_empty] at this
  have he : Tendsto e atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞) * B) hμn (Or.inr (by finiteness))
    rw [mul_zero] at this
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  -- On `[0, n]` the function is a compactly supported test function.
  let g : C_c(ℝ, ℝ) := ⟨⟨fun z ↦ ∫ x in Iic (n : ℝ≥0), f (x + z) ∂μ,
    f.continuous_setIntegral_comp_add _⟩, hasCompactSupport_setIntegral_Iic hf _⟩
  filter_upwards [Metric.tendsto_nhds.1 (hlim g) (ε / 3) (by positivity)] with i hi
  simp only [g, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk] at hi
  have h1 := dist_integral_setIntegral_Iic_le (μ := μ) hf (hν' i) hB n
  have h2 := dist_integral_setIntegral_Iic_le (μ := μ) hf hν hB n
  rw [dist_comm] at h2
  linarith [dist_triangle4 (∫ z, ∫ x, f (x + z) ∂μ ∂ν' i)
    (∫ z, ∫ x in Iic (n : ℝ≥0), f (x + z) ∂μ ∂ν' i)
    (∫ z, ∫ x in Iic (n : ℝ≥0), f (x + z) ∂μ ∂ν) (∫ z, ∫ x, f (x + z) ∂μ ∂ν)]

end Translate

end MeasureTheory
