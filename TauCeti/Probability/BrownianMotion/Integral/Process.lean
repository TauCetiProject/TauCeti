/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2
public import TauCeti.Probability.BrownianMotion.Integral.Simple
public import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.Probability.BrownianMotion.Integral.Restriction
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Martingale.ContinuousLimit
import TauCeti.Probability.Process.ElementaryDensity

/-!
# The predictable L² Brownian integral process

For a filtration-relative Brownian motion `W` and an integrand `H` in
`TauCeti.BrownianIntegrable ℱ P H`, the finite-horizon terminal maps
`IsFilteredPreBrownianReal.l2Integral` assemble into a time-indexed stochastic integral process.

First, conditional expectation of a terminal Brownian integral at an earlier deterministic time
is the integral of the restricted integrand (`condExp_l2Integral`), so the terminal L² maps
determine a square-integrable martingale (`exists_martingale_l2Integral`), and
`t ↦ hW.l2Integral t (hH.toPredictableLp t)` is `L²`-continuous in time
(`continuous_l2Integral_toPredictableLp`).

Second, any adapted modification `I` of `t ↦ hW.l2Integral t (hH.toPredictableLp t)` is a
martingale (`martingale_of_ae_eq_l2Integral`) and, when right-continuous against an almost surely
continuous Brownian driver, receives uniform convergence in outer probability on finite horizons
from approximating elementary integrals (`tendsto_measure_exists_le_norm_simpleGains_sub_lt`).
Square compensation (`martingale_sq_sub_integral_of_ae_eq_l2Integral`), conditional increment
energy (`setIntegral_sq_sub_of_ae_eq_l2Integral`, `condExp_sq_sub_of_ae_eq_l2Integral`),
predictable rectangle restriction, and optional stopping at raw stopping times are established in
`TauCeti.Probability.BrownianMotion.Integral.Square`,
`TauCeti.Probability.BrownianMotion.Integral.ConditionalIsometry`,
`TauCeti.Probability.BrownianMotion.Integral.Locality`, and
`TauCeti.Probability.BrownianMotion.Integral.Stopping.Integral`.

Finally, when `W` has almost surely continuous paths, `exists_continuous_l2Integral` selects a
strongly predictable, almost surely continuous martingale modification (uniqueness up to
indistinguishability follows from `TauCeti.indist_of_ae_continuous`). Neither right continuity nor
completeness of the filtration is assumed.

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
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, ha₂, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
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
  have hM (k : ι) : Martingale (Finance.simpleGains (τ k) (n k) (a k) W) ℱ P :=
    hW.martingale_simpleGains_of_integrable (hτ k) (ha k) fun i hi ↦
      (ha₂ k i hi).integrable one_le_two
  exact (hW.martingale_of_ae_eq_l2Integral hH hI_adapt hI).tendsto_measure_exists_le_norm_sub_lt
    hM hI_rc (fun k ↦ hcont.mono fun _ hω _ _ ↦
      (Finance.continuous_simpleGains hω).continuousWithinAt)
    (TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm one_le_two
      (hW.tendsto_eLpNorm_simpleGains_sub_of_ae_eq_l2Integral
        (fun _ ↦ hH) (fun _ ↦ hI T) hτ ha ha₂ hlim)) hε

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
  obtain ⟨n, τ, a, C, _, hτ, ha, hb, ha₂, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  let M (m : ℕ) := Finance.simpleGains (τ m) (n m) (a m) W
  have hmem (m : ℕ) (t : ℝ≥0) : MemLp (M m t) 2 P :=
    (Lp.memLp _).ae_eq (hW.coeFn_l2Integral_simpleHolding (hτ m).monotoneOn (ha m) t
      ((TauCeti.brownianIntegrable_simpleHolding (ha m) (ha₂ m)).memLp_predictableMeasure t))
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
      (fun m ↦ hcont.mono fun _ hω ↦ Finance.continuous_simpleGains hω)
      hmem (fun t ↦ (htend t).cauchySeq)
  refine ⟨I, hIp, hIm, hIpath.mono fun _ hω ↦ hω.1, fun t ↦ ?_⟩
  have heq_lp : (hIlim t).1.toLp (I t) = hW.l2Integral t (hH.toPredictableLp t) :=
    tendsto_nhds_unique
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun m ↦ hmem m t) _ (hIlim t).1).mpr (hIlim t).2)
      (htend t)
  exact (hIlim t).1.coeFn_toLp.symm.trans (heq_lp ▸ EventuallyEq.rfl)

/-- Conditioning a terminal integral on an earlier date gives the integral of its restriction.
The restricted input may be any L² class agreeing with the original input on the shorter
horizon; no choice of representatives or usual conditions on the filtration is needed. -/
theorem condExp_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {S T : ℝ≥0} (hST : S ≤ T) (f : Lp ℝ 2 (ℱ.predictableMeasure P T))
    (g : Lp ℝ 2 (ℱ.predictableMeasure P S))
    (hfg : g =ᵐ[ℱ.predictableMeasure P S] f) :
    P[hW.l2Integral T f | ℱ S] =ᵐ[P] hW.l2Integral S g := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  -- Restriction and conditional expectation are continuous linear maps on L² classes.
  let R : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ]
      Lp ℝ 2 (ℱ.predictableMeasure P S) :=
    ℱ.predictableMeasureRestrictLp P ℝ hST
  let C : Lp ℝ 2 P →L[ℝ] Lp ℝ 2 P :=
    (lpMeas ℝ ℝ (ℱ S) 2 P).subtypeL.comp (condExpL2 ℝ ℝ (ℱ.le S))
  have hC (u : Lp ℝ 2 P) : C u =ᵐ[P] P[u | ℱ S] := by
    simpa only [C, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
      Lp.toLp_coeFn] using (Lp.memLp u).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le S)
  -- It suffices to compare these maps on the dense predictable rectangles.
  have hmaps : C.comp (hW.l2Integral T).toContinuousLinearMap =
      (hW.l2Integral S).toContinuousLinearMap.comp R := by
    apply ContinuousLinearMap.ext_indicatorConstLp_Ioc_prod_predictableMeasure T
    intro s t hst ht A hA
    let u := indicatorConstLp (μ := ℱ.predictableMeasure P T) 2
      (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) (1 : ℝ)
    have hRu : R u = indicatorConstLp (μ := ℱ.predictableMeasure P S) 2
        (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) 1 := by
      exact ℱ.predictableMeasureRestrictLp_indicatorConstLp P (𝕜 := ℝ) hST _ 1
    dsimp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    rw [hRu]
    apply Lp.ext
    refine (hC (hW.l2Integral T u)).trans ?_
    have hterminal := hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht hA 1
    have hshort := hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod S s t hA 1
    simp only [← Pi.sub_apply, ← Set.indicator_mul_left, one_mul] at hterminal hshort
    exact (condExp_congr_ae hterminal).trans
      ((hW.martingale.condExp_indicator_sub hst.le hA S).trans hshort.symm)
  have hg : R f = g :=
    Lp.ext ((ℱ.coeFn_predictableMeasureRestrictLp P (𝕜 := ℝ) hST f).trans hfg.symm)
  exact (hC (hW.l2Integral T f)).symm.trans
    (by simpa only [ContinuousLinearMap.comp_apply,
      LinearIsometry.coe_toContinuousLinearMap, hg] using
        Lp.ext_iff.mp (congrArg (fun J : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ]
          Lp ℝ 2 P ↦ J f) hmaps))

/-- A terminal L² Brownian integral is a.e. strongly measurable at its terminal date. -/
theorem aestronglyMeasurable_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (T : ℝ≥0) (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    AEStronglyMeasurable[ℱ T] (hW.l2Integral T f) P :=
  ⟨P[hW.l2Integral T f | ℱ T], stronglyMeasurable_condExp,
    (hW.condExp_l2Integral le_rfl f f .rfl).symm⟩

/-- Predictable L² inputs on every finite horizon determine a square-integrable martingale
on the raw filtration. The chosen values agree with the terminal integral classes at each
fixed time; this asserts neither path continuity nor indistinguishability of arbitrary
representatives of those classes. Literal predictability of `H` is unnecessary: membership
in predictable L² already supplies the required a.e. measurable classes. -/
theorem exists_martingale_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    {H : ℝ≥0 × Ω → ℝ} (hH : ∀ t, MemLp H 2 (ℱ.predictableMeasure P t)) :
    ∃ I : ℝ≥0 → Ω → ℝ, Martingale I ℱ P ∧
      (∀ t, I t =ᵐ[P] hW.l2Integral t ((hH t).toLp H)) ∧
      ∀ t, MemLp (I t) 2 P := by
  let := hW.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let J (t : ℝ≥0) := hW.l2Integral t ((hH t).toLp H)
  let I (t : ℝ≥0) := P[J t | ℱ t]
  have hI (t : ℝ≥0) : I t =ᵐ[P] J t :=
    hW.condExp_l2Integral le_rfl _ _ Filter.EventuallyEq.rfl
  have hrestrict {s t : ℝ≥0} (hst : s ≤ t) :
      (hH s).toLp H =ᵐ[ℱ.predictableMeasure P s] (hH t).toLp H :=
    (hH s).coeFn_toLp.trans (((hH t).coeFn_toLp.filter_mono
      (ae_mono (ℱ.predictableMeasure_mono P hst))).symm)
  refine ⟨I, ⟨fun _ ↦ stronglyMeasurable_condExp, fun s t hst ↦ ?_⟩, hI, ?_⟩
  · exact (condExp_congr_ae (hI t)).trans
      ((hW.condExp_l2Integral hst _ _ (hrestrict hst)).trans (hI s).symm)
  · exact fun t ↦ (Lp.memLp (J t)).ae_eq (hI t).symm

end TauCeti.Probability.IsFilteredPreBrownianReal
