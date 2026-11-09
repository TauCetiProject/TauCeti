/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.StepApproximation
public import TauCeti.Probability.Renewal.Truncation
public import TauCeti.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Passing interval limits through monotone forcing

Convergence of interval masses implies convergence of convolution against monotone
forcing truncated to a bounded age interval. The forcing may have jumps and need not
have either sign. Uniform-mesh Darboux bounds preserve the half-open endpoint conventions
even when the integrating measure has atoms. The measure need only be finite on bounded
intervals; it need not be a renewal measure.

For a renewal measure, uniform tail truncation extends this to every nonnegative decreasing
Lebesgue-integrable forcing function. This is the analytic transfer in the key renewal
theorem. The interval limit is an explicit hypothesis: this file does not establish
Blackwell's theorem, nor infer a nonlattice renewal limit from the local bound alone.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, volume II,
  second edition (1971), Chapter XI, the monotone-forcing approximation argument.
-/

public section

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace MeasureTheory.Measure

open TauCeti.Probability

/-- Forward interval-mass limits also give the limits of reflected intervals of fixed age. -/
theorem tendsto_measureReal_Ioc_sub_of_tendsto_measureReal_Ioc
    (μ : Measure ℝ≥0) {r : ℝ}
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 => μ.real (Ioc t (t + d))) atTop
      (𝓝 (r * d))) (a b : ℝ≥0) (hab : a ≤ b) :
    Tendsto (fun t : ℝ≥0 => μ.real (Ioc (t - b) (t - a))) atTop
      (𝓝 (r * ((b : ℝ) - a))) := by
  have ht : Tendsto (fun t : ℝ≥0 => t - b) atTop atTop := by
    refine tendsto_atTop.2 fun c => ?_
    filter_upwards [eventually_ge_atTop (c + b)] with t hct
    exact le_tsub_of_add_le_right hct
  have he : (fun t : ℝ≥0 => μ.real (Ioc (t - b) (t - a))) =ᶠ[atTop]
      (fun t => μ.real (Ioc (t - b) (t - b + (b - a)))) := by
    filter_upwards [eventually_ge_atTop b] with t hbt
    rw [tsub_add_tsub_cancel hbt hab]
  simpa only [NNReal.coe_sub hab] using ((hlim (b - a)).comp ht).congr' he.symm

/-- If the forward interval masses `μ.real (Ioc t (t + d))` converge to `r * d` for every
`d`, convolution with a monotone forcing cut off at age `A` converges to
`r` times its integral on `0..A`. The age cutoff is excluded and age zero is included.
No continuity, positivity or global integrability of the forcing is required. -/
theorem tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc
    (μ : Measure ℝ≥0) [IsLocallyFiniteMeasure μ] {r : ℝ}
    (hlim : ∀ d : ℝ≥0, Tendsto (fun t : ℝ≥0 => μ.real (Ioc t (t + d))) atTop
      (𝓝 (r * d)))
    {h : ℝ≥0 → ℝ} (A : ℝ≥0) (hh : AntitoneOn h (Iic A)) :
    Tendsto (renewalConv ((Iio A).indicator h) μ) atTop
      (𝓝 (r * ∫ x in (0 : ℝ)..A, h x.toNNReal)) := by
  have hr : 0 ≤ r := by
    simpa only [NNReal.coe_one, mul_one] using
      ge_of_tendsto' (hlim 1) (fun _ => measureReal_nonneg)
  by_cases hA : A = 0
  · subst A
    have he : renewalConv ((Iio (0 : ℝ≥0)).indicator h) μ = fun _ => 0 := by
      funext t
      have hz : (Iio (0 : ℝ≥0)).indicator h = 0 := by ext s; simp
      rw [hz]
      exact renewalConv_zero_left μ t
    rw [he]
    simp
  -- Lower and upper sums share a vanishing, explicitly telescoping gap.
  let δ (n : ℕ) : ℝ≥0 := A / (n + 1)
  let p (n k : ℕ) : ℝ≥0 := δ n * k
  let L (n : ℕ) : ℝ := r * (δ n : ℝ) *
    ∑ k ∈ Finset.range (n + 1), h (p n (k + 1))
  let U (n : ℕ) : ℝ := r * (δ n : ℝ) *
    ∑ k ∈ Finset.range (n + 1), h (p n k)
  let I : ℝ := r * ∫ x in (0 : ℝ)..A, h x.toNNReal
  have hp (n : ℕ) : Monotone (p n) := fun k l hkl =>
    mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkl) bot_le
  have hp0 (n : ℕ) : p n 0 = 0 := by simp [p]
  have hpN (n : ℕ) : p n (n + 1) = A := by
    simp [p, δ, Nat.cast_add, Nat.cast_one]
  have hf : AntitoneOn (fun x : ℝ => h x.toNNReal) (Icc 0 (A : ℝ)) := by
    intro x hx y hy hxy
    exact hh (by simpa using Real.toNNReal_le_toNNReal hx.2)
      (by simpa using Real.toNNReal_le_toNNReal hy.2) (Real.toNNReal_mono hxy)
  have hd (n : ℕ) : (A : ℝ) / (n + 1) = δ n := by
    simp only [δ, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  have hsample (n k : ℕ) : h ((δ n : ℝ) * k).toNNReal = h (p n k) := by
    congr 1
    simp only [p, Real.toNNReal_mul (δ n).coe_nonneg, Real.toNNReal_coe,
      Real.toNNReal_natCast]
  obtain ⟨hbracket, herr⟩ : (∀ n, L n ≤ I ∧ I ≤ U n) ∧
      Tendsto (fun n => U n - L n) atTop (𝓝 0) := by
    have hm := hf.uniform_mesh_darboux_bounds A.coe_nonneg hr
    -- Expose only the mesh lets, then identify the real and nonnegative-real samples.
    dsimp only at hm
    simpa only [hd, hsample] using hm
  -- Each finite sum has a limit; the deterministic Darboux bounds hold for all t ≥ A.
  have hbounds (n : ℕ) :
      (∀ᶠ t : ℝ≥0 in atTop,
        (∑ k ∈ Finset.range (n + 1), h (p n (k + 1)) *
          μ.real (Ioc (t - p n (k + 1)) (t - p n k))) ≤
            renewalConv ((Iio A).indicator h) μ t) ∧
      (∀ᶠ t : ℝ≥0 in atTop, renewalConv ((Iio A).indicator h) μ t ≤
        ∑ k ∈ Finset.range (n + 1), h (p n k) *
          μ.real (Ioc (t - p n (k + 1)) (t - p n k))) := by
    constructor <;> filter_upwards [eventually_ge_atTop A] with t ht
    · simpa only [hpN] using sum_mul_measureReal_Ioc_le_renewalConv_of_antitoneOn
        (μ := μ) measure_Iic_lt_top.ne (p n) (hp n) (hp0 n) (n + 1)
        (by simpa only [hpN] using ht) (by simpa only [hpN] using hh)
    · simpa only [hpN] using renewalConv_le_sum_mul_measureReal_Ioc_of_antitoneOn
        (μ := μ) measure_Iic_lt_top.ne (p n) (hp n) (hp0 n) (n + 1)
        (by simpa only [hpN] using ht) (by simpa only [hpN] using hh)
  have hstep (n : ℕ) (c : ℕ → ℝ) :
      Tendsto (fun t : ℝ≥0 => ∑ k ∈ Finset.range (n + 1), c k *
        μ.real (Ioc (t - p n (k + 1)) (t - p n k))) atTop
        (𝓝 (r * (δ n : ℝ) * ∑ k ∈ Finset.range (n + 1), c k)) := by
    have he (k : ℕ) : (p n (k + 1) : ℝ) - p n k = δ n := by
      dsimp [p]
      push_cast
      ring
    convert tendsto_finsetSum (Finset.range (n + 1))
      (fun k _ => (μ.tendsto_measureReal_Ioc_sub_of_tendsto_measureReal_Ioc hlim
        (p n k) (p n (k + 1)) (hp n (Nat.le_succ k))).const_mul (c k)) using 1
    simp only [he, Finset.mul_sum, mul_comm, mul_left_comm]
  -- Choose a sufficiently fine mesh, then pass its finite-sum bounds to the time limit.
  apply tendsto_order.2
  constructor
  · intro a ha
    have hminus : Tendsto (fun n => I - (U n - L n)) atTop (𝓝 I) := by
      simpa using (tendsto_const_nhds (x := I)).sub herr
    obtain ⟨n, hn⟩ := (hminus.eventually_const_lt ha).exists
    have haL : a < L n := by linarith [(hbracket n).2]
    filter_upwards [(hstep n (fun k => h (p n (k + 1)))).eventually_const_lt haL,
      (hbounds n).1] with t ht hle
    exact ht.trans_le hle
  · intro b hb
    have hplus : Tendsto (fun n => I + (U n - L n)) atTop (𝓝 I) := by
      simpa using (tendsto_const_nhds (x := I)).add herr
    obtain ⟨n, hn⟩ := (hplus.eventually_lt_const hb).exists
    have hUb : U n < b := by linarith [(hbracket n).1]
    filter_upwards [(hstep n (fun k => h (p n k))).eventually_lt_const hUb,
      (hbounds n).2] with t ht hle
    exact hle.trans_lt ht

/-- The analytic implication from Blackwell interval limits to the key renewal limit.
The nonlattice hypothesis and the identification of `r` must be supplied by the interval-limit
theorem; neither is assumed implicitly. Zero increments and infinite increment mean are allowed. -/
theorem tendsto_renewalConv_of_tendsto_measureReal_Ioc
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (hμ : μ {0} < 1)
    {r : ℝ}
    (hlim : ∀ d : ℝ≥0,
      Tendsto (fun t : ℝ≥0 => μ.renewalMeasure.real (Ioc t (t + d))) atTop (𝓝 (r * d)))
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h μ.renewalMeasure) atTop
      (𝓝 (r * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  have := isLocallyFiniteMeasure_renewalMeasure μ hμ
  have hbound : ∀ x : ℝ≥0, |h x| ≤ h 0 := fun x => by
    rw [abs_of_nonneg (h₀ x)]
    exact hh bot_le
  have hintconv (t : ℝ≥0) : IntegrableOn (fun s => h (t - s)) (Iic t)
      μ.renewalMeasure :=
    integrableOn_Iic_sub hh.measurable (fun s _ => hbound s) measure_Iic_lt_top.ne
  have htrunc (N : ℕ) : renewalConv ((Iio (N : ℝ≥0)).indicator h) μ.renewalMeasure =
      renewalConv h μ.renewalMeasure -
        renewalConv ((Ici (N : ℝ≥0)).indicator h) μ.renewalMeasure := by
    funext t
    have hi : IntegrableOn (fun s => (Ici (N : ℝ≥0)).indicator h (t - s)) (Iic t)
        μ.renewalMeasure :=
      integrableOn_Iic_sub (hh.measurable.indicator measurableSet_Ici)
        (fun s _ => le_trans (by simpa only [Real.norm_eq_abs] using
          norm_indicator_le_norm_self (s := Ici (N : ℝ≥0)) h s)
            (hbound s)) measure_Iic_lt_top.ne
    simp only [Pi.sub_apply]
    rw [← renewalConv_sub (hintconv t) hi]
    congr 1
    ext s
    by_cases hs : s < N <;> simp [hs, not_lt.mp, Pi.sub_apply]
  -- Uniform tail control permits interchanging the cutoff and observation-time limits.
  have hunif : TendstoUniformly
      (fun N : ℕ => renewalConv ((Iio (N : ℝ≥0)).indicator h) μ.renewalMeasure)
      (renewalConv h μ.renewalMeasure) atTop := by
    have hu := Metric.tendstoUniformly_iff.1
      (μ.tendstoUniformly_renewalConv_indicator_Ici hμ hh h₀ hint)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [hu ε hε] with N hN t
    rw [htrunc]
    simpa [Real.dist_eq] using hN t
  apply hunif.tendsto_of_eventually_tendsto
    (Eventually.of_forall fun N =>
      μ.renewalMeasure.tendsto_renewalConv_indicator_Iio_of_tendsto_measureReal_Ioc hlim
        (N : ℝ≥0) (hh.antitoneOn _))
  exact (intervalIntegral_tendsto_integral_Ioi 0 hint
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul r

/-- Removing the artificial arrival at zero does not change the key renewal limit:
the term it contributes is the forcing itself, which vanishes at infinity. Genuine
zero-increment clusters remain in the integrating measure. -/
theorem tendsto_renewalConv_sub_dirac_of_tendsto_measureReal_Ioc
    (μ : Measure ℝ≥0) [IsProbabilityMeasure μ] (hμ : μ {0} < 1)
    {r : ℝ}
    (hlim : ∀ d : ℝ≥0,
      Tendsto (fun t : ℝ≥0 => μ.renewalMeasure.real (Ioc t (t + d))) atTop (𝓝 (r * d)))
    {h : ℝ≥0 → ℝ} (hh : Antitone h) (h₀ : ∀ x, 0 ≤ h x)
    (hint : IntegrableOn (fun x : ℝ => h x.toNNReal) (Ioi 0)) :
    Tendsto (renewalConv h (μ.renewalMeasure - dirac 0)) atTop
      (𝓝 (r * ∫ x in Ioi (0 : ℝ), h x.toNNReal)) := by
  have := isLocallyFiniteMeasure_renewalMeasure μ hμ
  have hf : AntitoneOn (fun x : ℝ => h x.toNNReal) (Ici 0) :=
    fun _ _ _ _ hxy => hh (Real.toNNReal_mono hxy)
  have hhlim : Tendsto h atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.toNNReal_coe, id_eq] using
      (hf.tendsto_zero_of_integrableOn_Ioi hint (fun x _ => h₀ x.toNNReal)).comp
        (NNReal.tendsto_coe_atTop.2 tendsto_id)
  have hmeasure : μ.renewalMeasure - dirac 0 = μ ∗ μ.renewalMeasure := by
    conv_lhs => rw [renewalMeasure_eq_dirac_add_conv, add_comm, Measure.add_sub_cancel]
  have he (t : ℝ≥0) : renewalConv h (μ.renewalMeasure - dirac 0) t =
      renewalConv h μ.renewalMeasure t - h t := by
    rw [hmeasure]
    have heq := renewalConv_renewalMeasure_eq_add_conv (μ := μ) hh.measurable
      (t := t) (C := h 0) (fun s _ => by
        rw [abs_of_nonneg (h₀ s)]
        exact hh bot_le)
    linarith
  rw [funext he]
  simpa only [sub_zero] using
    (μ.tendsto_renewalConv_of_tendsto_measureReal_Ioc hμ hlim hh h₀ hint).sub hhlim

end MeasureTheory.Measure
