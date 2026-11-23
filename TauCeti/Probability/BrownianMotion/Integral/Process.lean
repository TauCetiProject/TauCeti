/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Simple
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Tendsto
import TauCeti.Probability.BrownianMotion.Integral.Locality
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.BrownianMotion.Integral.Square
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Process.TimeIntegral

/-!
# The predictable L² Brownian integral process

For a filtration-relative Brownian motion `W` and an integrand `H` in
`TauCeti.BrownianIntegrable ℱ P H`, the finite-horizon terminal maps
`IsFilteredPreBrownianReal.l2Integral` assemble into a time-indexed stochastic integral process.

First, using `eLpNorm_l2Integral_toPredictableLp_sub_of_le` and
`norm_l2Integral_toPredictableLp_sub_sq_of_le` from
`TauCeti.Probability.BrownianMotion.Integral.Restriction`, the process
`t ↦ hW.l2Integral t (hH.toPredictableLp t)` is `L²`-continuous in time
(`continuous_l2Integral_toPredictableLp`).

Second, any adapted modification `I` of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` inherits the
elementary-approximation `L²` error identity (`eLpNorm_simpleGains_sub_of_ae_eq_l2Integral`,
`tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral`), uniform convergence in outer probability on
finite horizons when right-continuous (`tendsto_measure_exists_le_norm_simpleGains_sub_lt`), and is
a centered `L²` martingale satisfying the Itô isometry `integral_sq_of_ae_eq_l2Integral`, the
cross-isometry `integral_mul_of_ae_eq_l2Integral`, the set-integral and conditional increment
energy identities (`setIntegral_sq_sub_of_ae_eq_l2Integral`, `condExp_sq_sub_of_ae_eq_l2Integral`),
and the square-compensation martingale property `martingale_sq_sub_integral_of_ae_eq_l2Integral`.
Predictable rectangle restriction and optional stopping at raw stopping times are established in
`TauCeti.Probability.BrownianMotion.Integral.Locality` and
`TauCeti.Probability.BrownianMotion.Integral.Stopping.Integral`.

Finally, when `W` has almost surely continuous paths, `exists_continuous_l2Integral` selects a
strongly predictable, almost surely continuous martingale modification, unique up to
indistinguishability. Neither right continuity nor completeness of the filtration is assumed.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–C.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set TopologicalSpace
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The predictable `L²` Brownian integral process `t ↦ hW.l2Integral t (hH.toPredictableLp t)`
is continuous in `Lp ℝ 2 P`. -/
theorem continuous_l2Integral_toPredictableLp (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    letI := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
    Continuous fun t ↦ hW.l2Integral t (hH.toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  refine continuous_iff_continuousAt.mpr fun t₀ ↦ ?_
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  let f (t : ℝ≥0) : Lp ℝ 2 P := hW.l2Integral t (hH.toPredictableLp t)
  let μ := (timeMeasure (t₀ + 1)).prod P
  let F (t : ℝ≥0) (p : ℝ≥0 × Ω) : ℝ :=
    (Ioc (min t t₀) (max t t₀) ×ˢ Set.univ).indicator (fun q ↦ H q.1 q.2 ^ 2) p
  have hsm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) :=
    ((hH.isStronglyPredictable.mono ℱ.predictable_le_prod).pow 2)
  have ht₀_null : timeMeasure (t₀ + 1) {t₀} = 0 := by
    rw [timeMeasure_apply (t₀ + 1) (measurableSet_singleton t₀)]
    exact measure_mono_null (Set.image_mono Set.inter_subset_left) (by simp)
  have hne : ∀ᵐ p ∂μ, p.1 ≠ t₀ := by
    have htime : ∀ᵐ u ∂timeMeasure (t₀ + 1), u ≠ t₀ := by
      rw [ae_iff]
      convert ht₀_null using 2
      ext x
      simp
    exact (Measure.quasiMeasurePreserving_fst (μ := timeMeasure (t₀ + 1)) (ν := P)).ae htime
  have hF_lim : Tendsto (fun t ↦ ∫ p, F t p ∂μ) (𝓝 t₀) (𝓝 0) := by
    have hzero : ∫ _ : ℝ≥0 × Ω, (0 : ℝ) ∂μ = 0 := integral_zero _ _
    rw [← hzero]
    refine tendsto_integral_filter_of_dominated_convergence (fun p ↦ H p.1 p.2 ^ 2)
      (.of_forall fun t ↦
        (hsm.indicator (measurableSet_Ioc.prod MeasurableSet.univ)).aestronglyMeasurable)
      (.of_forall fun t ↦ .of_forall fun p ↦ ?_)
      (hH.memLp_timeMeasure (t₀ + 1)).integrable_sq
      (hne.mono fun ⟨u, ω⟩ hu ↦ ?_)
    · rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)]
      exact Set.indicator_le' (fun _ _ ↦ le_rfl) (fun _ _ ↦ sq_nonneg _) _
    · apply tendsto_const_nhds.congr'
      rcases lt_or_gt_of_ne hu with hlt | hgt
      · filter_upwards [eventually_gt_nhds hlt] with t ht
        have hnot : u ∉ Ioc (min t t₀) (max t t₀) := fun h ↦
          not_lt_of_ge h.1.le (lt_min ht hlt)
        simp [F, hnot]
      · filter_upwards [eventually_lt_nhds hgt] with t ht
        have hnot : u ∉ Ioc (min t t₀) (max t t₀) := fun h ↦
          not_lt_of_ge h.2 (max_lt ht hgt)
        simp [F, hnot]
  have hsq_lim : Tendsto (fun t ↦ ‖f t - f t₀‖ ^ 2) (𝓝 t₀) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hF_lim
      (.of_forall fun t ↦ sq_nonneg _) ?_
    filter_upwards [eventually_le_nhds (lt_add_one t₀)] with t ht1
    have hle_int {a b : ℝ≥0} (hb : b ≤ t₀ + 1) :
        ∫ p in Ioc a b ×ˢ Set.univ, H p.1 p.2 ^ 2 ∂(timeMeasure b).prod P ≤
          ∫ p, (Ioc a b ×ˢ Set.univ).indicator (fun q ↦ H q.1 q.2 ^ 2) p ∂μ := by
      rw [← integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
      exact integral_mono_measure (Measure.prod_mono (timeMeasure_mono hb) le_rfl)
        (.of_forall fun _ ↦ Set.indicator_nonneg (fun _ _ ↦ sq_nonneg _) _)
        ((hH.memLp_timeMeasure (t₀ + 1)).integrable_sq.indicator
          (measurableSet_Ioc.prod MeasurableSet.univ))
    by_cases ht : t ≤ t₀
    · rw [norm_sub_rev, hW.norm_l2Integral_toPredictableLp_sub_sq_of_le hH ht]
      simpa only [F, min_eq_left ht, max_eq_right ht] using
        hle_int (le_add_of_nonneg_right zero_le_one)
    · have ht' := (not_le.mp ht).le
      rw [hW.norm_l2Integral_toPredictableLp_sub_sq_of_le hH ht']
      simpa only [F, min_eq_right ht', max_eq_left ht'] using hle_int ht1
  have hsqrt : Tendsto (fun t ↦ √(‖f t - f t₀‖ ^ 2)) (𝓝 t₀) (𝓝 √0) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hsq_lim
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hsqrt

section Modification

variable {H K I J : ℝ≥0 → Ω → ℝ}

/-- Any strongly adapted modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` is a
martingale on the original raw filtration. -/
theorem martingale_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) : Martingale I ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P := MemLp.of_bound
    ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (Eventually.of_forall (hb m j hj))
  refine martingale_of_tendsto_eLpNorm_one (fun m ↦ hW.martingale.simpleGains_of_bdd
    (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
    hI_adapt fun t ↦ TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t))

/-- If `W` has almost surely continuous paths, `I` is a strongly adapted, almost surely
right-continuous modification of `t ↦ hW.l2Integral t (hH.toPredictableLp t)`, and square-integrable
elementary holdings converge in ambient time-product `L²` to `H` on `(0, T]`, then their Brownian
simple gains converge uniformly in outer probability to `I` on `[0, T]`. -/
theorem tendsto_measure_exists_le_norm_simpleGains_sub_lt
    {ι : Type*} {l : Filter ι} (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    {T : ℝ≥0}
    (hI_rc : ∀ᵐ ω ∂P, ∀ t < T, ContinuousWithinAt (fun u ↦ I u ω) (Ioi t) t)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    {τ : ι → ℕ → ℝ≥0} {n : ι → ℕ} {a : ι → ℕ → Ω → ℝ} (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k, ∀ i < n k, StronglyMeasurable[ℱ (τ k i)] (a k i))
    (ha₂ : ∀ k, ∀ i < n k, MemLp (a k i) 2 P)
    (hlim : Tendsto (fun k ↦ eLpNorm (fun p ↦ Finance.simpleHolding (τ k) (n k) (a k) p.1 p.2 -
      H p.1 p.2) 2 ((timeMeasure T).prod P)) l (𝓝 0))
    {ε : ℝ≥0} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ∃ t ≤ T, (ε : ℝ) < ‖Finance.simpleGains (τ k) (n k) (a k) W t ω -
      I t ω‖}) l (𝓝 0) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hM (k : ι) : Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P := by
    have hstep : ∀ m ≤ n k, Martingale (fun t ω ↦
        ∑ i ∈ range m, a k i ω * (W (min (τ k (i + 1)) t) ω - W (min (τ k i) t) ω)) ℱ P := by
      intro m hm
      induction m with
      | zero => simpa only [sum_range_zero, Pi.zero_def] using martingale_zero ℝ ℱ P
      | succ m ih =>
        have hlt : m < n k := hm
        have hle : τ k m ≤ τ k (m + 1) := hτ k (mem_Iic.mpr hlt.le) (mem_Iic.mpr hlt) m.le_succ
        convert (ih hlt.le).add (hW.martingale_mul_sub_min hle
          (ha k m hlt) ((ha₂ k m hlt).integrable one_le_two)) using 1
        ext t ω; simp only [Pi.add_apply, sum_range_succ]
    convert hstep (n k) le_rfl using 1
    ext t ω; rw [Finance.simpleGains_def]
  exact (hW.martingale_of_ae_eq_l2Integral hH hI_adapt hI).tendsto_measure_exists_le_norm_sub_lt
    hM hI_rc (fun k ↦ hcont.mono fun _ hω _ _ ↦
      (Finance.continuous_simpleGains hω).continuousWithinAt)
    (TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI T) hτ ha ha₂ hlim)) hε

/-- **Brownian square-compensation martingale.** For any `BrownianIntegrable` integrand `H` and
strongly adapted modification `I` of `l2Integral`, `I_t² - ∫_{(0, t]} H_s² ds` is a true
martingale on the original raw filtration. -/
theorem martingale_sq_sub_integral_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI_adapt : StronglyAdapted ℱ I)
    (hI : ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    Martingale (fun t ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) ℱ P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P := MemLp.of_bound
    ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (Eventually.of_forall (hb m j hj))
  let M (m : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
    Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 -
      ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t
  have hM (m : ℕ) : Martingale (M m) ℱ P := by
    convert hW.martingale_sq_simpleGains_sub (hτ m).monotoneOn (ha m) (ha₂ m) using 1
    ext t ω; dsimp only [M]
    rw [Finance.integral_sq_simpleHolding_timeMeasure (hτ m).monotoneOn t ω]
  have hcomp_adapt : StronglyAdapted ℱ (fun t ω ↦ ∫ s, H s ω ^ 2 ∂timeMeasure t) := by
    simpa only [sq] using (hH.isStronglyPredictable.mul
      hH.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
  refine martingale_of_tendsto_eLpNorm_one hM (fun t ↦ ((hI_adapt t).pow 2).sub (hcomp_adapt t))
    fun t ↦ ?_
  have hG_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) 1 P) atTop (𝓝 0) :=
    TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hW.memLp_of_ae_eq_l2Integral hH (hI t)).eLpNorm_ne_top
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI t) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t))
  have hA_lim : Tendsto (fun m ↦ eLpNorm
      (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
        ∫ s, H s ω ^ 2 ∂timeMeasure t) 1 P) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (TauCeti.tendsto_eLpNorm_one_sq_sub_sq (hH.memLp_timeMeasure t).eLpNorm_ne_top (herr t))
      (fun _ ↦ bot_le) fun m ↦ ?_
    have hS := BrownianIntegrable.simpleHolding (ha m) (ha₂ m)
    have hdiff_sm : StronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 ^ 2 - Function.uncurry H p ^ 2) :=
      ((hS.isStronglyPredictable.pow 2).sub (hH.isStronglyPredictable.pow 2)).mono
        ℱ.predictable_le_prod
    have hS_adapt : StronglyAdapted ℱ
        (fun t ω ↦ ∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) := by
      simpa only [sq] using (hS.isStronglyPredictable.mul
        hS.isStronglyPredictable).isStronglyProgressive.integral_timeMeasure.stronglyAdapted
    have hlhs_m : AEStronglyMeasurable
        (fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t) P :=
      (((hS_adapt t).sub (hcomp_adapt t)).mono (ℱ.le t)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_eNorm hlhs_m,
      eLpNorm_one_eq_lintegral_eNorm hdiff_sm.aestronglyMeasurable,
      lintegral_prod_symm _ hdiff_sm.eNorm.aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [hS.locallyBrownianIntegrable.ae_memLp,
      hH.locallyBrownianIntegrable.ae_memLp] with ω hSω hHω
    rw [← integral_sub
      (by simpa [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hSω t).integrable_sq)
      (by simpa [NNReal.comap_volume_restrict_Ioc, timeMeasure_def] using (hHω t).integrable_sq)]
    exact eNorm_integral_le_lintegral_eNorm _
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [zero_add] using hG_lim.add hA_lim) (fun _ ↦ bot_le) fun m ↦ ?_
  have htri : (M m t - fun ω ↦ I t ω ^ 2 - ∫ s, H s ω ^ 2 ∂timeMeasure t) =
      (fun ω ↦ Finance.simpleGains (τ m) (n m) (a m) W t ω ^ 2 - I t ω ^ 2) -
        fun ω ↦ (∫ s, Finance.simpleHolding (τ m) (n m) (a m) s ω ^ 2 ∂timeMeasure t) -
          ∫ s, H s ω ^ 2 ∂timeMeasure t := by ext ω; simp [M]; ring
  rw [htri]; exact eLpNorm_sub_le le_rfl

/-- For any process `I` agreeing almost surely at `s` and `t` (`s ≤ t`) with the predictable `L²`
integral of a `BrownianIntegrable` integrand `H`, the set integral of `(I t - I s)^2` over any
`ℱ s`-measurable event `A` equals the expected square energy of `H` over `(s, t] × A`.
No adaptedness assumption on `I` is needed. -/
theorem setIntegral_sq_sub_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hs : I s =ᵐ[P] hW.l2Integral s (hH.toPredictableLp s))
    (ht : I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t))
    {A : Set Ω} (hA : MeasurableSet[ℱ s] A) :
    ∫ ω in A, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p in Ioc s t ×ˢ A, H p.1 p.2 ^ 2 ∂(timeMeasure t).prod P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hrect := hW.coeFn_l2Integral_indicator_Ioc_prod_eq_indicator_sub hH hst le_rfl hA
  have hsq : (fun ω ↦ A.indicator (fun ω ↦ (I t ω - I s ω) ^ 2) ω) =ᵐ[P]
      fun ω ↦ hW.l2Integral t ((hH.indicator_Ioc_prod s t hA).toPredictableLp t) ω ^ 2 := by
    filter_upwards [hrect, hs, ht] with ω hω hωs hωt
    rw [hω]
    by_cases hωA : ω ∈ A
    · simp only [Set.indicator_of_mem hωA, hωs, hωt]
    · simp [hωA]
  have hint := hW.integral_sq_l2Integral_toPredictableLp (hH.indicator_Ioc_prod s t hA) t
  rw [← integral_indicator (ℱ.le s A hA), integral_congr_ae hsq, hint,
    ← integral_indicator ((measurableSet_Ioc (a := s) (b := t)).prod (ℱ.le s A hA))]
  refine integral_congr_ae (.of_forall fun ⟨u, ω⟩ ↦ ?_)
  by_cases hu : u ∈ Ioc s t <;> by_cases hω : ω ∈ A <;> simp [hu, hω]

/-- Conditional second moment of increments of a modification `I` of the predictable `L²` Brownian
integral: for `s ≤ t`, `E[(I t - I s)^2 | ℱ s] = E[∫_(s, t] H u ^ 2 du | ℱ s]` almost surely.
No adaptedness assumption on `I` is needed. -/
theorem condExp_sq_sub_of_ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H I : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hs : I s =ᵐ[P] hW.l2Integral s (hH.toPredictableLp s))
    (ht : I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t)) :
    P[fun ω ↦ (I t ω - I s ω) ^ 2 | ℱ s] =ᵐ[P]
      P[fun ω ↦ ∫ u in Ioc s t, H u ω ^ 2 ∂timeMeasure t | ℱ s] := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  have hI_mem : MemLp (fun ω ↦ I t ω - I s ω) 2 P :=
    (hW.memLp_of_ae_eq_l2Integral hH ht).sub (hW.memLp_of_ae_eq_l2Integral hH hs)
  have hH_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2) ((timeMeasure t).prod P) :=
    (hH.memLp_timeMeasure t).integrable_sq
  have hprod_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod P) :=
    hH_int.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  have hRHS_int : Integrable (fun ω ↦ ∫ u in Ioc s t, H u ω ^ 2 ∂timeMeasure t) P :=
    hprod_int.integral_prod_right
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s)
    hI_mem.integrable_sq (fun _ _ _ ↦ integrable_condExp.integrableOn)
    (fun A hA _ ↦ ?_) stronglyMeasurable_condExp.aestronglyMeasurable).symm
  have hA_int : Integrable (fun p : ℝ≥0 × Ω ↦ H p.1 p.2 ^ 2)
      (((timeMeasure t).restrict (Ioc s t)).prod (P.restrict A)) :=
    hprod_int.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  rw [setIntegral_condExp (ℱ.le s) hRHS_int hA,
    hW.setIntegral_sq_sub_of_ae_eq_l2Integral hH hst hs ht hA,
    ← Measure.prod_restrict (Ioc s t) A, integral_prod_symm _ hA_int]

end Modification

/-- **Continuous martingale modification of the predictable `L²` Brownian integral.**
When `W` has almost surely continuous paths, any `BrownianIntegrable` integrand `H` admits a
strongly predictable, almost surely continuous martingale `I` on the original raw filtration
that represents `hW.l2Integral t (hH.toPredictableLp t)` at every time `t`. -/
theorem exists_continuous_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    {H : ℝ≥0 → Ω → ℝ} (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t, I t =ᵐ[P] hW.l2Integral t (hH.toPredictableLp t) := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P := MemLp.of_bound
    ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (Eventually.of_forall (hb m j hj))
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) t
      ((BrownianIntegrable.simpleHolding (ha m) (ha₂ m)).memLp_predictableMeasure t))
  have htend (t : ℝ≥0) : Tendsto (fun m ↦ (hmem m t).toLp (M m t)) atTop
      (𝓝 (hW.l2Integral t (hH.toPredictableLp t))) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    exact (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
      (fun _ ↦ hH) (fun _ ↦ .rfl) (fun m ↦ (hτ m).monotoneOn) ha ha₂ (herr t)).congr
      fun m ↦ eLpNorm_congr_ae (((hmem m t).coeFn_toLp).symm.sub .rfl)
  obtain ⟨I, hIm, hIp, hIlim, _, _, _, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp (p := 2)
      (fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
        ⟨C m, Eventually.of_forall fun ω ↦ by simpa only [Real.norm_eq_abs] using hb m j hj ω⟩)
      (fun m ↦ hcont.mono fun ω hω ↦ by
        simp only [Finance.simpleGains_def]
        exact continuous_finsetSum _ fun j _ ↦ continuous_const.mul
          ((hω.comp (continuous_const.min continuous_id)).sub
            (hω.comp (continuous_const.min continuous_id))))
      hmem (fun t ↦ (htend t).cauchySeq)
  refine ⟨I, hIp, hIm, hIpath.mono fun _ hω ↦ hω.1, fun t ↦ ?_⟩
  have heq_lp : (hIlim t).1.toLp (I t) = hW.l2Integral t (hH.toPredictableLp t) :=
    tendsto_nhds_unique
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun m ↦ hmem m t) _ (hIlim t).1).mpr (hIlim t).2)
      (htend t)
  exact (hIlim t).1.coeFn_toLp.symm.trans (heq_lp ▸ EventuallyEq.rfl)

end TauCeti.Probability.IsFilteredPreBrownianReal
