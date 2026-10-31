/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Typeclasses.Finite
public import TauCeti.Probability.Renewal.Measure

/-!
# Convolution with a measure on the half-line and the renewal equation

For a function `h : ℝ≥0 → ℝ` and a measure `μ` on `ℝ≥0`, the convolution

```text
(h ∗ μ) t = ∫_{[0, t]} h (t - s) μ(ds)
```

integrates over both endpoints of `[0, t]`. It is the operation in the renewal equation
`g = h + g ∗ F` of renewal theory, where `F` is the law of the increments of a renewal process,
`h` is a known forcing term and `g` is the unknown.

The first part of the file develops the convolution for measurable `h` that are bounded on each
interval `[0, t]` and measures that are finite on each such interval: measurability in `t`, the
bound `|(h ∗ μ) t| ≤ C · μ [0, T]` for `t ≤ T` when `|h| ≤ C` on `[0, T]`, linearity in `h` and in
the measure, and the associativity `(h ∗ μ) ∗ ν = h ∗ (μ ∗ ν)`. When the renewal measure
`U = ∑ n, F^{∗n}` of `F` is finite on `[0, T]`, the series `∑ n, (h ∗ F^{∗n}) t` converges
absolutely, uniformly for `t ∈ [0, T]`, and its sum is `(h ∗ U) t`.

The second part solves the renewal equation. If the renewal measure of `F` is locally finite,
which holds for a probability measure `F` with `F {0} < 1`
(`MeasureTheory.Measure.isLocallyFiniteMeasure_renewalMeasure`), then `g = h ∗ U` solves
`g = h + g ∗ F`, and it is the only solution that is measurable and bounded on each interval
`[0, t]`. Uniqueness iterates the equation: the difference `d` of two solutions satisfies
`d = d ∗ F^{∗n}` for every `n`, and `F^{∗n} [0, t] → 0` because these masses sum to `U [0, t]`.

## Main definitions

* `TauCeti.Probability.renewalConv` — the convolution `(h ∗ μ) t = ∫_{[0, t]} h (t - s) μ(ds)`.

## Main results

* `TauCeti.Probability.measurable_renewalConv` — measurability in time.
* `TauCeti.Probability.abs_renewalConv_le` — the bound by the mass of `[0, T]`.
* `TauCeti.Probability.renewalConv_renewalConv` — associativity `(h ∗ μ) ∗ ν = h ∗ (μ ∗ ν)`.
* `TauCeti.Probability.tendstoUniformlyOn_sum_renewalConv_convolutionPower` — uniform convergence
  of `∑ n, h ∗ F^{∗n}` on `[0, T]`, and `TauCeti.Probability.renewalConv_renewalMeasure`,
  identifying its sum with `h ∗ U`.
* `TauCeti.Probability.renewalConv_renewalMeasure_eq_add` — `h ∗ U` solves `g = h + g ∗ F`.
* `TauCeti.Probability.eq_zero_of_renewalConv_eq_self` — the homogeneous equation `d = d ∗ F`
  has no nonzero locally bounded measurable solution.
* `TauCeti.Probability.eq_renewalConv_renewalMeasure` — uniqueness of locally bounded measurable
  solutions.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {h g : ℝ≥0 → ℝ} {μ ν : Measure ℝ≥0} {s t T : ℝ≥0} {C : ℝ}

/-! ### Convolution of a function with a measure on the half-line -/

/-- The convolution `(h ∗ μ) t = ∫_{[0, t]} h (t - s) μ(ds)` of a function `h` on the half-line
with a measure `μ` on `ℝ≥0`. Both endpoints of `[0, t]` are included, so an atom of `μ` at zero
contributes `μ {0} · h t`. This is the convolution in the renewal equation `g = h + g ∗ F`. -/
def renewalConv (h : ℝ≥0 → ℝ) (μ : Measure ℝ≥0) (t : ℝ≥0) : ℝ :=
  ∫ s in Iic t, h (t - s) ∂μ

theorem renewalConv_def (h : ℝ≥0 → ℝ) (μ : Measure ℝ≥0) (t : ℝ≥0) :
    renewalConv h μ t = ∫ s in Iic t, h (t - s) ∂μ := (rfl)

/-- The convolution as an integral over the whole half-line of the integrand cut off at `t`. -/
theorem renewalConv_eq_integral_indicator (h : ℝ≥0 → ℝ) (μ : Measure ℝ≥0) (t : ℝ≥0) :
    renewalConv h μ t = ∫ s, (Iic t).indicator (fun s ↦ h (t - s)) s ∂μ := by
  rw [renewalConv_def, integral_indicator measurableSet_Iic]

@[simp]
theorem renewalConv_zero_measure (h : ℝ≥0 → ℝ) (t : ℝ≥0) : renewalConv h 0 t = 0 := by
  simp [renewalConv_def]

@[simp]
theorem renewalConv_zero_left (μ : Measure ℝ≥0) (t : ℝ≥0) : renewalConv 0 μ t = 0 := by
  simp [renewalConv_def]

/-- Convolution with the point mass at zero is the identity. -/
@[simp]
theorem renewalConv_dirac_zero (h : ℝ≥0 → ℝ) (t : ℝ≥0) :
    renewalConv h (Measure.dirac 0) t = h t := by
  classical
  simp [renewalConv_def, setIntegral_dirac]

/-- The integrand of `renewalConv h μ t` is integrable when `h` is measurable and bounded on
`[0, t]` and `μ` is finite on `[0, t]`. -/
theorem integrableOn_Iic_sub (hh : Measurable h) (hC : ∀ s ≤ t, |h s| ≤ C)
    (hμ : μ (Iic t) ≠ ∞) : IntegrableOn (fun s ↦ h (t - s)) (Iic t) μ := by
  refine Measure.integrableOn_of_bounded hμ (hh.comp (by fun_prop)).aestronglyMeasurable
    (M := C) ?_
  exact (ae_restrict_iff' measurableSet_Iic).2 (ae_of_all _ fun s _ ↦ hC _ tsub_le_self)

/-- The convolution is measurable in time. No boundedness of `h` is needed. -/
@[fun_prop]
theorem measurable_renewalConv (hh : Measurable h) (μ : Measure ℝ≥0) [SFinite μ] :
    Measurable (renewalConv h μ) := by
  have hf : StronglyMeasurable (Function.uncurry fun t s : ℝ≥0 ↦
      (Iic t).indicator (fun s ↦ h (t - s)) s) := by
    refine Measurable.stronglyMeasurable ?_
    have : (Function.uncurry fun t s : ℝ≥0 ↦ (Iic t).indicator (fun s ↦ h (t - s)) s) =
        {p : ℝ≥0 × ℝ≥0 | p.2 ≤ p.1}.indicator fun p ↦ h (p.1 - p.2) := by
      ext p
      simp [Set.indicator_apply, Function.uncurry]
    rw [this]
    exact (hh.comp (by fun_prop)).indicator (measurableSet_le measurable_snd measurable_fst)
  have := hf.integral_prod_right (ν := μ)
  simpa only [← renewalConv_eq_integral_indicator] using this.measurable

/-- **Local bound for the convolution.** If `|h| ≤ C` on `[0, T]` and `μ` is finite on `[0, T]`,
then `|(h ∗ μ) t| ≤ C · μ [0, T]` for every `t ≤ T`. -/
theorem abs_renewalConv_le (hC : ∀ s ≤ T, |h s| ≤ C) (hμ : μ (Iic T) ≠ ∞) (ht : t ≤ T) :
    |renewalConv h μ t| ≤ C * μ.real (Iic T) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0 zero_le)
  have hsub : Iic t ⊆ Iic T := Iic_subset_Iic.2 ht
  calc |renewalConv h μ t| ≤ C * μ.real (Iic t) := by
        rw [← Real.norm_eq_abs, renewalConv_def]
        refine norm_setIntegral_le_of_norm_le_const
          ((measure_mono hsub).trans_lt hμ.lt_top) fun s _ ↦ ?_
        rw [Real.norm_eq_abs]
        exact hC _ (tsub_le_self.trans ht)
    _ ≤ C * μ.real (Iic T) := mul_le_mul_of_nonneg_left (measureReal_mono hsub hμ) hC0

/-! ### Linearity -/

/-- The convolution is additive in the function at time `t`, provided both shifted functions
`s ↦ h₁ (t - s)` and `s ↦ h₂ (t - s)` are integrable on `[0, t]`. -/
theorem renewalConv_add {h₁ h₂ : ℝ≥0 → ℝ}
    (hi₁ : IntegrableOn (fun s ↦ h₁ (t - s)) (Iic t) μ)
    (hi₂ : IntegrableOn (fun s ↦ h₂ (t - s)) (Iic t) μ) :
    renewalConv (h₁ + h₂) μ t = renewalConv h₁ μ t + renewalConv h₂ μ t := by
  simp only [renewalConv_def, Pi.add_apply]
  exact integral_add hi₁ hi₂

/-- The convolution of a difference is the difference of the convolutions at time `t`, provided
both shifted functions `s ↦ h₁ (t - s)` and `s ↦ h₂ (t - s)` are integrable on `[0, t]`. -/
theorem renewalConv_sub {h₁ h₂ : ℝ≥0 → ℝ}
    (hi₁ : IntegrableOn (fun s ↦ h₁ (t - s)) (Iic t) μ)
    (hi₂ : IntegrableOn (fun s ↦ h₂ (t - s)) (Iic t) μ) :
    renewalConv (h₁ - h₂) μ t = renewalConv h₁ μ t - renewalConv h₂ μ t := by
  simp only [renewalConv_def, Pi.sub_apply]
  exact integral_sub hi₁ hi₂

/-- The convolution commutes with scalar multiplication of the function. No integrability is
needed, since the Bochner integral commutes with scalar multiplication unconditionally. -/
@[simp]
theorem renewalConv_smul (c : ℝ) (h : ℝ≥0 → ℝ) (μ : Measure ℝ≥0) :
    renewalConv (c • h) μ = c • renewalConv h μ := by
  ext t
  simp only [renewalConv_def, Pi.smul_apply]
  exact integral_smul c _

/-- The convolution commutes with negation of the function, with no integrability assumption. -/
@[simp]
theorem renewalConv_neg (h : ℝ≥0 → ℝ) (μ : Measure ℝ≥0) :
    renewalConv (-h) μ = -renewalConv h μ := by
  simpa using renewalConv_smul (-1) h μ

/-- The convolution is additive in the measure at time `t`, provided the shifted function
`s ↦ h (t - s)` is integrable on `[0, t]` for both measures. -/
theorem renewalConv_add_measure (hμ : IntegrableOn (fun s ↦ h (t - s)) (Iic t) μ)
    (hν : IntegrableOn (fun s ↦ h (t - s)) (Iic t) ν) :
    renewalConv h (μ + ν) t = renewalConv h μ t + renewalConv h ν t := by
  simp only [renewalConv_def, Measure.restrict_add]
  exact integral_add_measure hμ hν

/-! ### Associativity -/

/-- The inner integral of the iterated convolution: integrating the integrand of
`renewalConv h μ t` shifted by `s` gives `(h ∗ μ) (t - s)` for `s ≤ t` and zero otherwise. -/
private theorem integral_indicator_add_eq (h : ℝ≥0 → ℝ) (μ : Measure ℝ≥0) (t s : ℝ≥0) :
    ∫ u, (Iic t).indicator (fun v ↦ h (t - v)) (s + u) ∂μ =
      (Iic t).indicator (fun s ↦ renewalConv h μ (t - s)) s := by
  by_cases hs : s ≤ t
  · rw [indicator_of_mem (mem_Iic.2 hs), renewalConv_eq_integral_indicator]
    refine integral_congr_ae (ae_of_all _ fun u ↦ ?_)
    simp only [indicator_apply, mem_Iic, le_tsub_iff_left hs, tsub_tsub]
  · rw [indicator_of_notMem (by simpa using hs)]
    refine (integral_congr_ae (ae_of_all _ fun u ↦ ?_)).trans (integral_zero _ _)
    exact indicator_of_notMem (fun h' ↦ hs (le_self_add.trans (mem_Iic.1 h'))) _

/-- **Associativity of the convolution**, `(h ∗ μ) ∗ ν = h ∗ (μ ∗ ν)`, for `h` measurable and
bounded on `[0, t]` and measures finite on `[0, t]`. Iterating it with
`MeasureTheory.Measure.convolutionPower_succ` gives `(h ∗ F^{∗n}) ∗ F = h ∗ F^{∗(n + 1)}`. -/
theorem renewalConv_renewalConv [SFinite μ] [SFinite ν] (hh : Measurable h)
    (hC : ∀ s ≤ t, |h s| ≤ C) (hμ : μ (Iic t) ≠ ∞) (hν : ν (Iic t) ≠ ∞) :
    renewalConv (renewalConv h μ) ν t = renewalConv h (μ ∗ ν) t := by
  have hfin : (ν ∗ μ) (Iic t) ≠ ∞ :=
    ((Measure.conv_Iic_le ν μ t).trans_lt (ENNReal.mul_lt_top hν.lt_top hμ.lt_top)).ne
  have hint : Integrable ((Iic t).indicator fun v ↦ h (t - v)) (ν ∗ μ) :=
    (integrable_indicator_iff measurableSet_Iic).2 (integrableOn_Iic_sub hh hC hfin)
  rw [Measure.conv_comm, renewalConv_eq_integral_indicator h, integral_conv hint,
    renewalConv_eq_integral_indicator]
  simp_rw [integral_indicator_add_eq]

/-! ### The series `∑ n, h ∗ F^{∗n}` -/

section Series

/-- The terms of `∑ n, h ∗ F^{∗n}` are dominated, uniformly on `[0, T]`, by a summable sequence. -/
private theorem abs_renewalConv_convolutionPower_le (hC : ∀ s ≤ T, |h s| ≤ C)
    (hU : μ.renewalMeasure (Iic T) ≠ ∞) (n : ℕ) (ht : t ≤ T) :
    |renewalConv h (μ.convolutionPower n) t| ≤ C * (μ.convolutionPower n).real (Iic T) :=
  abs_renewalConv_le hC
    (ne_top_of_le_ne_top hU (Measure.convolutionPower_le_renewalMeasure μ n _)) ht

/-- **Absolute convergence of `∑ n, (h ∗ F^{∗n}) t`** when `h` is bounded on `[0, T]`, the
renewal measure of `F` is finite on `[0, T]`, and `t ≤ T`. -/
theorem summable_abs_renewalConv_convolutionPower (hC : ∀ s ≤ T, |h s| ≤ C)
    (hU : μ.renewalMeasure (Iic T) ≠ ∞) (ht : t ≤ T) :
    Summable fun n ↦ |renewalConv h (μ.convolutionPower n) t| :=
  ((Measure.summable_convolutionPower_real hU).mul_left C).of_nonneg_of_le (fun _ ↦ abs_nonneg _)
    fun n ↦ abs_renewalConv_convolutionPower_le hC hU n ht

/-- **Uniform convergence of `∑ n, h ∗ F^{∗n}` on bounded intervals**: if `h` is bounded on
`[0, T]` and the renewal measure of `F` is finite on `[0, T]`, the partial sums converge
uniformly on `[0, T]`. -/
theorem tendstoUniformlyOn_sum_renewalConv_convolutionPower (hC : ∀ s ≤ T, |h s| ≤ C)
    (hU : μ.renewalMeasure (Iic T) ≠ ∞) :
    TendstoUniformlyOn (fun N t ↦ ∑ n ∈ Finset.range N, renewalConv h (μ.convolutionPower n) t)
      (fun t ↦ ∑' n, renewalConv h (μ.convolutionPower n) t) atTop (Iic T) :=
  tendstoUniformlyOn_tsum_nat ((Measure.summable_convolutionPower_real hU).mul_left C)
    fun n _ ht ↦ by
      rw [Real.norm_eq_abs]
      exact abs_renewalConv_convolutionPower_le hC hU n ht

/-- **The sum of the series is the convolution with the renewal measure**:
`(h ∗ U) t = ∑ n, (h ∗ F^{∗n}) t` for `h` measurable and bounded on `[0, t]`, when the renewal
measure `U` of `F` is finite on `[0, t]`. -/
theorem renewalConv_renewalMeasure (hh : Measurable h) (hC : ∀ s ≤ t, |h s| ≤ C)
    (hU : μ.renewalMeasure (Iic t) ≠ ∞) :
    renewalConv h μ.renewalMeasure t = ∑' n, renewalConv h (μ.convolutionPower n) t := by
  have hint := integrableOn_Iic_sub hh hC hU
  simp_rw [renewalConv_def]
  rw [Measure.renewalMeasure_def, IntegrableOn, Measure.restrict_sum _ measurableSet_Iic] at hint
  rw [Measure.renewalMeasure_def, Measure.restrict_sum _ measurableSet_Iic]
  exact integral_sum_measure hint

end Series

/-! ### The renewal equation -/

section RenewalEquation

variable [IsLocallyFiniteMeasure μ.renewalMeasure]

/-- `h ∗ U` is bounded on each `[0, T]` when `h` is, for a locally finite renewal measure `U`. -/
private theorem abs_renewalConv_renewalMeasure_le (hC : ∀ s ≤ T, |h s| ≤ C) :
    ∀ s ≤ T, |renewalConv h μ.renewalMeasure s| ≤ C * μ.renewalMeasure.real (Iic T) :=
  fun _ ↦ abs_renewalConv_le hC measure_Iic_lt_top.ne

/-- **Existence for the renewal equation.** If the renewal measure `U` of `F` is locally finite
and `h` is measurable and bounded on `[0, t]`, then `g = h ∗ U` satisfies the renewal equation
`g t = h t + (g ∗ F) t`. -/
theorem renewalConv_renewalMeasure_eq_add [SFinite μ] (hh : Measurable h)
    (hC : ∀ s ≤ t, |h s| ≤ C) :
    renewalConv h μ.renewalMeasure t =
      h t + renewalConv (renewalConv h μ.renewalMeasure) μ t := by
  have := Measure.isLocallyFiniteMeasure_of_renewalMeasure μ
  have hUt : μ.renewalMeasure (Iic t) ≠ ∞ := measure_Iic_lt_top.ne
  -- `μ ∗ U ≤ U` by the renewal equation for measures, so it is finite on `[0, t]`.
  have hconv : (μ ∗ μ.renewalMeasure) (Iic t) ≠ ∞ := by
    refine ne_top_of_le_ne_top hUt ?_
    conv_rhs => rw [Measure.renewalMeasure_eq_dirac_add_conv]
    exact le_add_self
  rw [renewalConv_renewalConv hh hC hUt measure_Iic_lt_top.ne, Measure.conv_comm]
  conv_lhs => rw [Measure.renewalMeasure_eq_dirac_add_conv]
  rw [renewalConv_add_measure (integrableOn_Iic_sub hh hC (by simp))
    (integrableOn_Iic_sub hh hC hconv), renewalConv_dirac_zero]

/-- **The homogeneous renewal equation has only the trivial solution.** If the renewal measure of
`F` is locally finite and `d` is measurable, bounded on each `[0, t]`, and satisfies `d = d ∗ F`,
then `d = 0`. -/
theorem eq_zero_of_renewalConv_eq_self [SFinite μ] {d : ℝ≥0 → ℝ} (hd : Measurable d)
    (hdb : ∀ t, ∃ C, ∀ s ≤ t, |d s| ≤ C) (hfix : renewalConv d μ = d) : d = 0 := by
  have := Measure.isLocallyFiniteMeasure_of_renewalMeasure μ
  -- Iterating, `d = d ∗ F^{∗n}` for every `n`.
  have hpow : ∀ n t, renewalConv d (μ.convolutionPower n) t = d t := fun n ↦ by
    induction n with
    | zero => simp
    | succ n ih =>
      intro t
      obtain ⟨C, hC⟩ := hdb t
      rw [Measure.convolutionPower_succ, ← renewalConv_renewalConv hd hC
        (ne_top_of_le_ne_top measure_Iic_lt_top.ne
          (Measure.convolutionPower_le_renewalMeasure μ n _)) measure_Iic_lt_top.ne,
        funext ih, hfix]
  -- The masses `F^{∗n} [0, t]` are summable, hence tend to zero, so `d t = 0`.
  ext t
  obtain ⟨C, hC⟩ := hdb t
  have hlim : Tendsto (fun n ↦ C * (μ.convolutionPower n).real (Iic t)) atTop (𝓝 0) := by
    simpa using ((Measure.summable_convolutionPower_real
      measure_Iic_lt_top.ne).tendsto_atTop_zero).const_mul C
  have hle : ∀ n, |d t| ≤ C * (μ.convolutionPower n).real (Iic t) := fun n ↦ by
    rw [← hpow n t]
    exact abs_renewalConv_convolutionPower_le hC measure_Iic_lt_top.ne n le_rfl
  simpa using ge_of_tendsto' hlim hle

/-- **Uniqueness for the renewal equation.** If the renewal measure `U` of `F` is locally finite,
`h` is measurable and bounded on each `[0, t]`, and `g` is a measurable solution of
`g = h + g ∗ F` that is bounded on each `[0, t]`, then `g = h ∗ U`. -/
theorem eq_renewalConv_renewalMeasure [SFinite μ] (hh : Measurable h)
    (hhb : ∀ t, ∃ C, ∀ s ≤ t, |h s| ≤ C) (hg : Measurable g)
    (hgb : ∀ t, ∃ C, ∀ s ≤ t, |g s| ≤ C) (hgeq : g = h + renewalConv g μ) :
    g = renewalConv h μ.renewalMeasure := by
  have := Measure.isLocallyFiniteMeasure_of_renewalMeasure μ
  -- The difference of the two solutions solves the homogeneous equation.
  refine sub_eq_zero.1 (eq_zero_of_renewalConv_eq_self (μ := μ)
    (hg.sub (measurable_renewalConv hh _)) (fun T ↦ ?_) (funext fun t ↦ ?_))
  · obtain ⟨C₁, hC₁⟩ := hgb T
    obtain ⟨C₂, hC₂⟩ := hhb T
    refine ⟨C₁ + C₂ * μ.renewalMeasure.real (Iic T), fun s hs ↦ ?_⟩
    exact (abs_sub _ _).trans (add_le_add (hC₁ s hs) (abs_renewalConv_renewalMeasure_le hC₂ s hs))
  · obtain ⟨C₁, hC₁⟩ := hgb t
    obtain ⟨C₂, hC₂⟩ := hhb t
    rw [renewalConv_sub (integrableOn_Iic_sub hg hC₁ measure_Iic_lt_top.ne)
      (integrableOn_Iic_sub (measurable_renewalConv hh _)
        (abs_renewalConv_renewalMeasure_le hC₂) measure_Iic_lt_top.ne),
      Pi.sub_apply, renewalConv_renewalMeasure_eq_add hh hC₂, congrFun hgeq t, Pi.add_apply]
    ring

end RenewalEquation

end TauCeti.Probability
