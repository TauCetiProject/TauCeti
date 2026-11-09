/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Translate.Bounds
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
`Uₜ = U.map (s ↦ s - t)` (`MeasureTheory.Measure.translatedRenewalMeasure`), which sees the
renewals near time `t`. The renewal equation `U = δ₀ + F ∗ U` translates to

```text
Uₜ = δ_{-t} + F ∗ Uₜ
```

(`MeasureTheory.Measure.translatedRenewalMeasure_eq_dirac_add_conv`).

As `t → ∞` the point mass `δ_{-t}` escapes to `-∞`. This file shows that consequently every vague
limit `η` of translates `U_{t i}` with `t i → ∞` is `F`-harmonic, `F ∗ η = η`. Vague convergence
is expressed directly by convergence of the integrals of all continuous compactly supported test
functions, and `η` is assumed locally finite. No assumption on the mean of `F` or on its lattice
structure is needed.

In Feller's proof of Blackwell's renewal theorem for nonlattice `F`, this harmonicity, combined
with the theorem that a uniformly locally bounded `F`-harmonic measure is a multiple of Lebesgue
measure, identifies every limit of the translates.

## Main results

* `MeasureTheory.Measure.measure_Icc_le_of_tendsto_integral`: a locally finite vague limit `η` of
  translates `U_{t i}` inherits the local renewal bound, `η [a, b] ≤ U [0, b - a + 2]`, so its
  masses of intervals of a fixed length are bounded uniformly in their position.
* `MeasureTheory.Measure.map_coe_conv_eq_self_of_tendsto_integral`: a locally finite vague limit
  `η` of translates `U_{t i}` with `t i → ∞` satisfies `F ∗ η = η`.

## Implementation notes

Testing the translated renewal equation against `f` gives `∫ f dUₜ = f (-t) + ∫ ψ dUₜ` with
`ψ z = ∫ f (x + z) dF(x)`. The difficulty is that `f` is compactly supported but `ψ` need not be,
because `F` may have unbounded support. The local renewal bound `U [t, t + h] ≤ U [0, h]`
(`MeasureTheory.Measure.translatedRenewalMeasure_Icc_add_le`) bounds the mass of the translates,
and of their limit, on intervals of a fixed length uniformly in their position. Splitting `F` into
its parts on `[0, M]` and on `(M, ∞)` then shows that the second part contributes at most a
constant multiple of `F (M, ∞)` to every integral, uniformly along the translates, and the first
part gives a compactly supported test function.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal CompactlySupported

namespace MeasureTheory.Measure

variable {μ : Measure ℝ≥0}

/-- A locally finite vague limit of translates of the renewal measure inherits the local renewal
bound, up to enlarging the length of the interval by `2`. -/
theorem measure_Icc_le_of_tendsto_integral [IsProbabilityMeasure μ] (hμ : μ {0} < 1)
    {ι : Type*} {l : Filter ι} [l.NeBot] {t : ι → ℝ} {η : Measure ℝ} [IsLocallyFiniteMeasure η]
    (hη : ∀ f : C_c(ℝ, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μ.translatedRenewalMeasure (t i)) l
      (𝓝 (∫ x, f x ∂η))) (a b : ℝ) :
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
        have := μ.isLocallyFiniteMeasure_translatedRenewalMeasure hμ (t i)
        rw [Function.comp_apply, hlin]
        calc ∫⁻ x, ENNReal.ofReal (gc x) ∂μ.translatedRenewalMeasure (t i)
            ≤ ∫⁻ x, (Icc (a - 1) (b + 1)).indicator 1 x
                ∂μ.translatedRenewalMeasure (t i) := lintegral_mono fun x ↦ by
              by_cases hx : x ∈ Ioo (a - 1) (b + 1)
              · simpa [indicator_of_mem (Ioo_subset_Icc_self hx), gc] using (hg01 x).2
              · simp [gc, hg0 hx]
          _ = μ.translatedRenewalMeasure (t i) (Icc (a - 1) (b + 1)) :=
              lintegral_indicator_one measurableSet_Icc
          _ ≤ μ.renewalMeasure (Iic (b - a + 2).toNNReal) := by
              refine (measure_mono (Icc_subset_Icc_right ?_)).trans
                (μ.translatedRenewalMeasure_Icc_add_le (t i) (a - 1) (b - a + 2).toNNReal)
              linarith [Real.le_coe_toNNReal (b - a + 2)]

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
    (hη : ∀ f : C_c(ℝ, ℝ), Tendsto (fun i ↦ ∫ x, f x ∂μ.translatedRenewalMeasure (t i)) l
      (𝓝 (∫ x, f x ∂η))) :
    μ.map ((↑) : ℝ≥0 → ℝ) ∗ η = η := by
  -- Local finiteness of the translates makes test functions integrable against them.
  have hU (i : ι) : IsLocallyFiniteMeasure (μ.translatedRenewalMeasure (t i)) :=
    μ.isLocallyFiniteMeasure_translatedRenewalMeasure hμ _
  -- The convolution `μ ∗ η` is locally finite, since `η` has uniformly bounded interval masses.
  have : IsLocallyFiniteMeasure (μ.map ((↑) : ℝ≥0 → ℝ) ∗ η) :=
    isLocallyFiniteMeasure_conv_of_measure_Icc_le two_pos (fun c ↦ by
      have := measure_Icc_le_of_tendsto_integral hμ hη c (c + 2)
      rwa [show c + 2 - c + 2 = (4 : ℝ) by ring] at this)
      (μ.renewalMeasure_Iic_lt_top hμ (4 : ℝ).toNNReal).ne
  refine ext_of_integral_eq_on_compactlySupported fun f ↦ ?_
  obtain ⟨C, a, b, hf⟩ := f.exists_enorm_le_indicator
  set B := μ.renewalMeasure (Iic (b - a + 2).toNNReal)
  have hB : B ≠ ∞ := (μ.renewalMeasure_Iic_lt_top hμ _).ne
  have hBη (c : ℝ) : η (Icc (c + a) (c + b)) ≤ B := by
    simpa [show c + b - (c + a) = b - a by ring] using
      measure_Icc_le_of_tendsto_integral hμ hη (c + a) (c + b)
  have hBU (i : ι) (c : ℝ) :
      μ.translatedRenewalMeasure (t i) (Icc (c + a) (c + b)) ≤ B :=
    (measure_mono (Icc_subset_Icc_right (by linarith [Real.le_coe_toNNReal (b - a)]))).trans
      ((μ.translatedRenewalMeasure_Icc_add_le (t i) (c + a) (b - a).toNNReal).trans
        (measure_mono (Iic_subset_Iic.mpr (Real.toNNReal_le_toNNReal (by linarith)))))
  -- By the translated renewal equation, `∫ f dUᵢ = f (-tᵢ) + ∫ ψ dUᵢ` for
  -- `ψ z = ∫ f (x + z) dμ(x)`, and `f (-tᵢ)` vanishes eventually.
  have hdecomp (i : ι) : ∫ x, f x ∂μ.translatedRenewalMeasure (t i) =
      f (-t i) + ∫ z, ∫ x, f (x + z) ∂μ ∂μ.translatedRenewalMeasure (t i) := by
    have hi : Integrable f (μ.translatedRenewalMeasure (t i)) := f.integrable
    rw [translatedRenewalMeasure_eq_dirac_add_conv] at hi
    conv_lhs => rw [translatedRenewalMeasure_eq_dirac_add_conv]
    rw [integral_add_measure (integrable_add_measure.1 hi).1 (integrable_add_measure.1 hi).2,
      integral_dirac, integral_map_coe_conv hf (hBU i) hB]
  have hlim : Tendsto (fun i ↦ f (-t i)) l (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [ht.eventually (eventually_gt_atTop (-a))] with i hi
    exact (CompactlySupportedContinuousMap.eq_zero_of_enorm_le_indicator hf
      fun h ↦ by linarith [h.1]).symm
  have h1 : Tendsto (fun i ↦ ∫ z, ∫ x, f (x + z) ∂μ
      ∂μ.translatedRenewalMeasure (t i)) l (𝓝 (∫ x, f x ∂η)) := by
    have := (hη f).sub hlim
    rw [sub_zero] at this
    refine this.congr fun i ↦ ?_
    rw [hdecomp]
    ring
  rw [integral_map_coe_conv hf hBη hB]
  exact tendsto_nhds_unique (tendsto_integral_integral_comp_add hη hf hBU hBη hB) h1

end MeasureTheory.Measure
