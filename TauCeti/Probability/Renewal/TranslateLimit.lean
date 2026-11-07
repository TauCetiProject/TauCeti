/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.LocalBound
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import TauCeti.MeasureTheory.Group.Convolution.IntervalBound
import TauCeti.Topology.ContinuousMap.CompactlySupported
import Mathlib.MeasureTheory.Group.IntegralConvolution
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.UrysohnsLemma

/-!
# Limits of translated renewal measures are harmonic

Let `U = ∑ n, F^{∗n}` be the renewal measure of a probability measure `F` on `ℝ≥0` with
`F {0} < 1`, and regard it as a measure on the real line. Translating it by `-t` gives the measure
`Uₜ = U.map (s ↦ s - t)`, which sees the renewals near time `t`. The renewal equation
`U = δ₀ + F ∗ U` translates to

```text
Uₜ = δ_{-t} + F ∗ Uₜ.
```

As `t → ∞` the point mass `δ_{-t}` escapes to `-∞`. This file shows that consequently every vague
limit `η` of translates `U_{t i}` with `t i → ∞` is `F`-harmonic, `F ∗ η = η`. Vague convergence
is expressed directly by convergence of the integrals of all continuous compactly supported test
functions, and `η` is assumed locally finite. No assumption on the mean of `F` or on its lattice
structure is needed.

In Feller's proof of Blackwell's renewal theorem for nonlattice `F`, this harmonicity, combined
with the theorem that a uniformly locally bounded `F`-harmonic measure is a multiple of Lebesgue
measure, identifies every limit of the translates.

## Main results

* `MeasureTheory.Measure.map_renewalMeasure_eq_dirac_add_conv`: the translated renewal equation
  `Uₜ = δ_{-t} + F ∗ Uₜ`.
* `MeasureTheory.Measure.measure_Icc_le_of_tendsto_integral`: a locally finite vague limit `η` of
  translates `U_{t i}` inherits the local renewal bound, `η [a, b] ≤ U [0, b - a + 2]`, so its
  masses of intervals of a fixed length are bounded uniformly in their position.
* `MeasureTheory.Measure.map_coe_conv_eq_self_of_tendsto_integral`: a locally finite vague limit
  `η` of translates `U_{t i}` with `t i → ∞` satisfies `F ∗ η = η`.

## Implementation notes

Testing the translated renewal equation against `f` gives `∫ f dUₜ = f (-t) + ∫ ψ dUₜ` with
`ψ z = ∫ f (x + z) dF(x)`. The difficulty is that `f` is compactly supported but `ψ` need not be,
because `F` may have unbounded support. The local renewal bound `U [t, t + h] ≤ U [0, h]`
(`MeasureTheory.Measure.map_renewalMeasure_Icc_le`) bounds the mass of the translates, and of
their limit, on intervals of a fixed length uniformly in their position. Splitting `F` into its
parts on `[0, M]` and on `(M, ∞)` then shows that the second part contributes at most a constant
multiple of `F (M, ∞)` to every integral, uniformly along the translates, and the first part gives
a compactly supported test function.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal CompactlySupported

namespace MeasureTheory.Measure

variable (μ : Measure ℝ≥0)

/-- The renewal equation `U = δ₀ + μ ∗ U`, translated by `-t` on the real line: the translated
renewal measure `Uₜ` satisfies `Uₜ = δ_{-t} + μ ∗ Uₜ`. -/
theorem map_renewalMeasure_eq_dirac_add_conv [SFinite μ] (t : ℝ) :
    μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t) =
      dirac (-t) + μ.map ((↑) : ℝ≥0 → ℝ) ∗ μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t) := by
  have hcomp : (fun s : ℝ≥0 ↦ (s : ℝ) - t) = (fun x : ℝ ↦ x + -t) ∘ ((↑) : ℝ≥0 → ℝ) := by
    funext s
    simp [sub_eq_add_neg]
  have hcoe : (μ ∗ μ.renewalMeasure).map ((↑) : ℝ≥0 → ℝ) =
      μ.map ((↑) : ℝ≥0 → ℝ) ∗ μ.renewalMeasure.map ((↑) : ℝ≥0 → ℝ) :=
    map_conv_addMonoidHom NNReal.toRealHom.toAddMonoidHom measurable_coe_nnreal_real
  rw [hcomp, ← map_map (by fun_prop) measurable_coe_nnreal_real]
  conv_lhs => rw [renewalMeasure_eq_dirac_add_conv]
  rw [Measure.map_add _ _ measurable_coe_nnreal_real, Measure.map_add _ _ (by fun_prop),
    map_dirac' measurable_coe_nnreal_real, map_dirac' (by fun_prop), hcoe, ← conv_dirac,
    ← conv_dirac, conv_assoc]
  simp

section Harmonic

variable {μ} {ν : Measure ℝ} {f : C_c(ℝ, ℝ)} {a b : ℝ} {C : ℝ≥0} {B : ℝ≥0∞}

/-- The part of `x ↦ f (x + z)` integrated over `S` contributes at most `C * B * μ S` to every
integral against a measure whose translated intervals have mass at most `B`. -/
private theorem lintegral_enorm_setIntegral_le [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (S : Set ℝ≥0) :
    ∫⁻ z, ‖∫ x in S, f (x + z) ∂μ‖ₑ ∂ν ≤ C * B * μ S := by
  calc ∫⁻ z, ‖∫ x in S, f (x + z) ∂μ‖ₑ ∂ν ≤ ∫⁻ z, ∫⁻ x in S, ‖f (x + z)‖ₑ ∂μ ∂ν :=
        lintegral_mono fun z ↦ enorm_integral_le_lintegral_enorm _
    _ = ∫⁻ x in S, ∫⁻ z, ‖f (x + z)‖ₑ ∂ν ∂μ :=
        lintegral_lintegral_swap (by fun_prop)
    _ ≤ ∫⁻ x in S, C * B ∂μ :=
        lintegral_mono fun x ↦ lintegral_comp_add_le_of_le_indicator hf hν x
    _ = C * B * μ S := setLIntegral_const S _

private theorem integrable_setIntegral_comp_add [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (hB : B ≠ ∞) (S : Set ℝ≥0) :
    Integrable (fun z : ℝ ↦ ∫ x in S, f (x + z) ∂μ) ν := by
  obtain ⟨D, hD⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  have hcont : Continuous fun z : ℝ ↦ ∫ x in S, f (x + z) ∂μ :=
    continuous_of_dominated (bound := fun _ ↦ D) (fun z ↦ by fun_prop)
      (fun z ↦ ae_of_all _ fun x ↦ hD _) (integrable_const D) (ae_of_all _ fun x ↦ by fun_prop)
  exact ⟨hcont.aestronglyMeasurable, (lintegral_enorm_setIntegral_le hf hν S).trans_lt
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hB.lt_top) (measure_lt_top μ S))⟩

/-- Integrating against `μ ∗ ν` is integrating `z ↦ ∫ f (x + z) dμ(x)` against `ν`. -/
private theorem integral_map_coe_conv [IsFiniteMeasure μ] [SFinite ν]
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y)
    (hν : ∀ c, ν (Icc (c + a) (c + b)) ≤ B) (hB : B ≠ ∞) :
    ∫ y, f y ∂(μ.map ((↑) : ℝ≥0 → ℝ) ∗ ν) = ∫ z, ∫ x, f (x + z) ∂μ ∂ν := by
  have hint : Integrable f (ν ∗ μ.map ((↑) : ℝ≥0 → ℝ)) := by
    refine ⟨(map_continuous f).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, ← Measure.conv_comm, lintegral_conv (by fun_prop)]
    calc ∫⁻ y, ∫⁻ z, ‖f (y + z)‖ₑ ∂ν ∂μ.map ((↑) : ℝ≥0 → ℝ)
        ≤ ∫⁻ x, ∫⁻ z, ‖f (x + z)‖ₑ ∂ν ∂μ :=
          lintegral_map_le _ measurable_coe_nnreal_real.aemeasurable
      _ ≤ ∫⁻ x, (C : ℝ≥0∞) * B ∂μ :=
          lintegral_mono fun x ↦ lintegral_comp_add_le_of_le_indicator hf hν x
      _ < ∞ := by
          rw [lintegral_const]
          exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.coe_lt_top hB.lt_top)
            (measure_lt_top μ _)
  rw [Measure.conv_comm, integral_conv hint]
  refine integral_congr_ae (ae_of_all _ fun z ↦ ?_)
  dsimp only
  rw [integral_map measurable_coe_nnreal_real.aemeasurable (by fun_prop)]
  simp_rw [add_comm z]

/-- The part of `x ↦ f (x + z)` over `(n, ∞)` is uniformly small: splitting the integral over
`[0, n]` changes the integral against `ν` by at most `C * B * μ (n, ∞)`. -/
private theorem dist_integral_setIntegral_Iic_le [IsFiniteMeasure μ] [SFinite ν]
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
    ← toReal_enorm]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hB)
    (measure_ne_top μ _)) ((enorm_integral_le_lintegral_enorm _).trans
      (lintegral_enorm_setIntegral_le hf hν _))

/-- Restricted to `[0, n]`, the function `z ↦ ∫ f (x + z) dμ(x)` is compactly supported. -/
private theorem hasCompactSupport_setIntegral_Iic
    (hf : ∀ y, ‖f y‖ₑ ≤ (Icc a b).indicator (fun _ ↦ (C : ℝ≥0∞)) y) (n : ℝ≥0) :
    HasCompactSupport fun z : ℝ ↦ ∫ x in Iic n, f (x + z) ∂μ := by
  refine HasCompactSupport.intro (isCompact_Icc (a := a - n) (b := b)) fun z hz ↦
    setIntegral_eq_zero_of_forall_eq_zero fun x hx ↦ ?_
  have hxz : (x : ℝ) + z ∉ Icc a b := fun h ↦
    hz ⟨by linarith [h.1, NNReal.coe_le_coe.mpr hx], by linarith [h.2, x.coe_nonneg]⟩
  simpa [indicator_of_notMem hxz] using hf (x + z)

/-- If the integrals of compactly supported test functions converge along a family of measures
whose translated intervals have uniformly bounded mass, then so do the integrals of
`z ↦ ∫ f (x + z) dμ(x)`, which need not be compactly supported. -/
private theorem tendsto_integral_integral_comp_add [IsFiniteMeasure μ] {ι : Type*}
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
    have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞) * B) hμn
      (Or.inr (ENNReal.mul_ne_top ENNReal.coe_ne_top hB))
    rw [mul_zero] at this
    exact (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds (by positivity : 0 < ε / 3))).exists
  -- On `[0, n]` the function is a compactly supported test function.
  obtain ⟨D, hD⟩ := (map_continuous f).bounded_above_of_compact_support f.hasCompactSupport
  let g : C_c(ℝ, ℝ) := ⟨⟨fun z ↦ ∫ x in Iic (n : ℝ≥0), f (x + z) ∂μ,
    continuous_of_dominated (bound := fun _ ↦ D) (fun z ↦ by fun_prop)
      (fun z ↦ ae_of_all _ fun x ↦ hD _) (integrable_const D) (ae_of_all _ fun x ↦ by fun_prop)⟩,
    hasCompactSupport_setIntegral_Iic hf _⟩
  filter_upwards [Metric.tendsto_nhds.1 (hlim g) (ε / 3) (by positivity)] with i hi
  simp only [g, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk] at hi
  have h1 := dist_integral_setIntegral_Iic_le (μ := μ) hf (hν' i) hB n
  have h2 := dist_integral_setIntegral_Iic_le (μ := μ) hf hν hB n
  rw [dist_comm] at h2
  linarith [dist_triangle4 (∫ z, ∫ x, f (x + z) ∂μ ∂ν' i)
    (∫ z, ∫ x in Iic (n : ℝ≥0), f (x + z) ∂μ ∂ν' i)
    (∫ z, ∫ x in Iic (n : ℝ≥0), f (x + z) ∂μ ∂ν) (∫ z, ∫ x, f (x + z) ∂μ ∂ν)]

/-- A locally finite vague limit of translates of the renewal measure inherits the local renewal
bound, up to enlarging the length of the interval by `2`. -/
theorem measure_Icc_le_of_tendsto_integral [IsProbabilityMeasure μ] (hμ : μ {0} < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {t : ι → ℝ} {η : Measure ℝ} [IsLocallyFiniteMeasure η]
    (hη : ∀ f : C_c(ℝ, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μ.renewalMeasure.map
      (fun s : ℝ≥0 ↦ (s : ℝ) - t i)) l (𝓝 (∫ x, f x ∂η))) (a b : ℝ) :
    η (Icc a b) ≤ μ.renewalMeasure (Iic (b - a + 2).toNNReal) := by
  -- Compare with a Urysohn function equal to one on `[a, b]` and vanishing off `(a - 1, b + 1)`.
  obtain ⟨g, hg1, hg0, hgc, hg01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_Icc (a := a) (b := b)) (isOpen_Ioo (a := a - 1) (b := b + 1)).isClosed_compl
    (disjoint_compl_right_iff_subset.mpr (Icc_subset_Ioo (by linarith) (by linarith)))
  let gc : C_c(ℝ, ℝ) := ⟨g, hgc⟩
  have hlin (ν : Measure ℝ) [IsFiniteMeasureOnCompacts ν] :
      ENNReal.ofReal (∫ x, gc x ∂ν) = ∫⁻ x, ENNReal.ofReal (gc x) ∂ν :=
    ofReal_integral_eq_lintegral_ofReal gc.integrable (ae_of_all _ fun x ↦ (hg01 x).1)
  calc η (Icc a b) = ∫⁻ x, (Icc a b).indicator 1 x ∂η :=
        (lintegral_indicator_one measurableSet_Icc).symm
    _ ≤ ∫⁻ x, ENNReal.ofReal (gc x) ∂η := lintegral_mono fun x ↦ by
        by_cases hx : x ∈ Icc a b
        · simp [indicator_of_mem hx, gc, hg1 hx]
        · simp [indicator_of_notMem hx]
    _ = ENNReal.ofReal (∫ x, gc x ∂η) := (hlin η).symm
    _ ≤ μ.renewalMeasure (Iic (b - a + 2).toNNReal) := by
        refine le_of_tendsto' ((ENNReal.continuous_ofReal.tendsto _).comp (hη gc)) fun i ↦ ?_
        have := μ.isLocallyFiniteMeasure_map_renewalMeasure hμ (t i)
        rw [Function.comp_apply, hlin]
        calc ∫⁻ x, ENNReal.ofReal (gc x) ∂μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i)
            ≤ ∫⁻ x, (Icc (a - 1) (b + 1)).indicator 1 x
                ∂μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i) := lintegral_mono fun x ↦ by
              by_cases hx : x ∈ Ioo (a - 1) (b + 1)
              · simpa [indicator_of_mem (Ioo_subset_Icc_self hx), gc] using (hg01 x).2
              · simp [gc, hg0 hx]
          _ = μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i) (Icc (a - 1) (b + 1)) :=
              lintegral_indicator_one measurableSet_Icc
          _ ≤ μ.renewalMeasure (Iic (b - a + 2).toNNReal) := by
              rw [show b - a + 2 = b + 1 - (a - 1) by ring]
              exact μ.map_renewalMeasure_Icc_le (t i) (a - 1) (b + 1)

end Harmonic

variable [IsProbabilityMeasure μ]

/-- **Limits of translated renewal measures are harmonic.** Let `μ` be a probability measure on
`ℝ≥0` with `μ {0} < 1` and renewal measure `U`. If the translates `U.map (s ↦ s - t i)` converge
vaguely to a locally finite measure `η` on the real line, in the sense that the integrals of all
continuous compactly supported functions converge, along translations `t i → ∞`, then
`μ ∗ η = η`, with `μ` regarded as a measure on the real line.

Neither a finite mean nor a nonlattice hypothesis is needed. Local finiteness of `η` cannot be
dropped: the integrals of compactly supported functions do not determine a measure that is
infinite on compact sets. -/
theorem map_coe_conv_eq_self_of_tendsto_integral (hμ : μ {0} < 1) {ι : Type*} {l : Filter ι}
    [l.NeBot] {t : ι → ℝ} (ht : Tendsto t l atTop) (η : Measure ℝ) [IsLocallyFiniteMeasure η]
    (hη : ∀ f : C_c(ℝ, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μ.renewalMeasure.map
      (fun s : ℝ≥0 ↦ (s : ℝ) - t i)) l (𝓝 (∫ x, f x ∂η))) :
    μ.map ((↑) : ℝ≥0 → ℝ) ∗ η = η := by
  -- Local finiteness of the translates makes test functions integrable against them.
  have hU (i : ι) : IsLocallyFiniteMeasure (μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i)) :=
    μ.isLocallyFiniteMeasure_map_renewalMeasure hμ _
  -- The convolution `μ ∗ η` is locally finite, since `η` has uniformly bounded interval masses.
  have : IsLocallyFiniteMeasure (μ.map ((↑) : ℝ≥0 → ℝ) ∗ η) :=
    isLocallyFiniteMeasure_conv_of_measure_Icc_le two_pos (fun c ↦ by
      simpa [show (2 : ℝ≥0) + 2 = 4 by norm_num] using
        measure_Icc_le_of_tendsto_integral hμ hη c (c + 2))
      (μ.renewalMeasure_Iic_lt_top hμ (4 : ℝ).toNNReal).ne
  refine ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  obtain ⟨C, a, b, hf⟩ := f.exists_enorm_le_indicator
  set B := μ.renewalMeasure (Iic (b - a + 2).toNNReal)
  have hB : B ≠ ∞ := (μ.renewalMeasure_Iic_lt_top hμ _).ne
  have hBη (c : ℝ) : η (Icc (c + a) (c + b)) ≤ B := by
    simpa [show c + b - (c + a) = b - a by ring] using
      measure_Icc_le_of_tendsto_integral hμ hη (c + a) (c + b)
  have hBU (i : ι) (c : ℝ) :
      μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i) (Icc (c + a) (c + b)) ≤ B :=
    (μ.map_renewalMeasure_Icc_le _ _ _).trans (measure_mono (Iic_subset_Iic.mpr
      (Real.toNNReal_le_toNNReal (by linarith))))
  -- By the translated renewal equation, `∫ f dUᵢ = f (-tᵢ) + ∫ ψ dUᵢ` for
  -- `ψ z = ∫ f (x + z) dμ(x)`, and `f (-tᵢ)` vanishes eventually.
  have hdecomp (i : ι) : ∫ x, f x ∂μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i) =
      f (-t i) + ∫ z, ∫ x, f (x + z) ∂μ ∂μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i) := by
    have hi : Integrable f (μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i)) := f.integrable
    rw [map_renewalMeasure_eq_dirac_add_conv] at hi
    conv_lhs => rw [map_renewalMeasure_eq_dirac_add_conv]
    rw [integral_add_measure (integrable_add_measure.1 hi).1 (integrable_add_measure.1 hi).2,
      integral_dirac, integral_map_coe_conv hf (hBU i) hB]
  have hlim : Tendsto (fun i ↦ f (-t i)) l (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ht.eventually (eventually_gt_atTop (-a))] with i hi
    have hti : -t i ∉ Icc a b := fun h ↦ by linarith [h.1]
    exact (by simpa [indicator_of_notMem hti] using hf (-t i) : f (-t i) = 0).symm
  have h1 : Tendsto (fun i ↦ ∫ z, ∫ x, f (x + z) ∂μ
      ∂μ.renewalMeasure.map (fun s : ℝ≥0 ↦ (s : ℝ) - t i)) l (𝓝 (∫ x, f x ∂η)) := by
    have := (hη f).sub hlim
    rw [sub_zero] at this
    refine this.congr fun i ↦ ?_
    rw [hdecomp]
    ring
  rw [integral_map_coe_conv hf hBη hB]
  exact tendsto_nhds_unique (tendsto_integral_integral_comp_add hη hf hBU hBη hB) h1

end MeasureTheory.Measure
