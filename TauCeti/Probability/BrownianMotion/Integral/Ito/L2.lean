/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Ito.Basic
public import TauCeti.Probability.BrownianMotion.Integral.L2
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.Probability.BrownianMotion.Integral.Energy.Basic
import TauCeti.Probability.BrownianMotion.Integral.Simple
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import TauCeti.Probability.Finance.SimpleStrategy.Energy
import TauCeti.Probability.Martingale.ContinuousLimit

/-!
# The continuous Brownian Itô integral on the expected square-energy domain

For `H` in `TauCeti.BrownianIntegrable ℱ P H`, this module constructs a predictable continuous
martingale `I` with `TauCeti.Probability.IsItoIntegral ℱ P W H I` whenever `W` is a filtered
pre-Brownian motion with a.s. continuous paths, together with a single sequence of bounded
elementary gains converging in `L²(P)` and uniformly in probability on every `[0, T]` and a
subsequence converging a.s. uniformly on every `[0, T]`. It also shows that every continuous Itô
integral of `H` against any filtered pre-Brownian motion agrees with `hW.l2Integral T`, has zero
expectation, satisfies the fixed-horizon and `(s, t]`-increment Itô isometries, varies
continuously in `L²(P)`, and is a martingale when strongly adapted.

## Main results

* `TauCeti.BrownianIntegrable.exists_isItoIntegral_approx`,
  `TauCeti.BrownianIntegrable.exists_isItoIntegral`: predictable continuous martingale Itô
  integral for `BrownianIntegrable` integrands, with uniform-in-probability and a.s.-uniform
  elementary approximation.
* `TauCeti.Probability.IsItoIntegral.ae_eq_l2Integral`, `memLp`, `toLp_eq_l2Integral`:
  identification of `I T` with `hW.l2Integral T` in `L²(P)`.
* `TauCeti.Probability.IsItoIntegral.eLpNorm_eq`, `eLpNorm_sub_eq`, `eLpNorm_simpleGains_sub_eq`,
  `integral_eq_zero`, `integral_mul`, `integral_sq`, `integral_sub_sq`: zero expectation,
  fixed-horizon and increment Itô isometries, and elementary-strategy `L²` comparison.
* `TauCeti.Probability.IsItoIntegral.continuous_toLp`: `L²(P)` continuity in time.
* `TauCeti.Probability.IsItoIntegral.martingale`: strongly adapted `L²` Itô integrals are
  martingales.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology InnerProductSpace

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ}

private theorem exists_simpleHolding_tendsto_l2Integral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ)
      (_ : ∀ m, τ m 0 = 0)
      (_ : ∀ m, StrictMonoOn (τ m) (Iic (n m)))
      (_ : ∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j))
      (_ : ∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m)
      (_ : ∀ m, Martingale (Finance.simpleGains (τ m) (n m) (a m) W) ℱ P)
      (hmem : ∀ m T, MemLp (Finance.simpleGains (τ m) (n m) (a m) W T) 2 P),
      (∀ T, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      ∀ T, Tendsto (fun m ↦ (hmem m T).toLp (Finance.simpleGains (τ m) (n m) (a m) W T)) atTop
        (𝓝 (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)))) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, herr⟩ := hH.exists_seq_simpleHolding_tendsto_eLpNorm
  have ha₂ (m j : ℕ) (hj : j < n m) : MemLp (a m j) 2 P :=
    MemLp.of_bound ((ha m j hj).mono (ℱ.le _)).aestronglyMeasurable (C m) (.of_forall (hb m j hj))
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb,
    fun m ↦ hW.martingale.simpleGains_of_bdd (hτ m).monotoneOn (ha m) fun j hj ↦
      ⟨C m, .of_forall fun ω ↦ by simpa [Real.norm_eq_abs] using hb m j hj ω⟩,
    fun m T ↦ hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T, herr, fun T ↦ ?_⟩
  have hu : Tendsto (fun m ↦ (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T).toLp
      (Function.uncurry (Finance.simpleHolding (τ m) (n m) (a m)))) atTop
      (𝓝 ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))) := by
    rw [tendsto_iff_edist_tendsto_0]
    exact (herr T).congr fun m ↦ by
      rw [Lp.edist_toLp_toLp, ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod
        ((Finance.isStronglyPredictable_simpleHolding (ha m)).sub hH.isStronglyPredictable)]; rfl
  exact (((hW.l2Integral T).continuous.tendsto _).comp hu).congr fun m ↦
    hW.l2Integral_simpleHolding (hτ m).monotoneOn (ha m) T
      (Finance.memLp_simpleHolding_predictableMeasure (ha m) (ha₂ m) T)
      (hW.memLp_simpleGains (hτ m).monotoneOn (ha m) (ha₂ m) T)

/-- **Existence and uniform approximation of the continuous `L²` Brownian Itô integral**: every
`BrownianIntegrable` integrand against a filtered pre-Brownian motion `W` with a.s. continuous
paths admits a predictable continuous martingale Itô integral on the raw filtration, approximated
simultaneously on every finite horizon by one sequence of bounded simple strategies in `L²`,
uniformly in probability on `[0, T]`, and along a subsequence a.s. uniformly on `[0, T]`. -/
theorem BrownianIntegrable.exists_isItoIntegral_approx
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (I : ℝ≥0 → Ω → ℝ) (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      Probability.IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧ Martingale I ℱ P ∧
      (∀ m, τ m 0 = 0) ∧
      (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      (∀ T : ℝ≥0, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0)) ∧
      (∀ T : ℝ≥0, Tendsto (fun m ↦
        eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T - I T) 2 P) atTop (𝓝 0)) ∧
      (∀ (T : ℝ≥0) (ε : ℝ≥0), 0 < ε → Tendsto (fun m ↦
        P {ω | ∃ t ≤ T, (ε : ℝ) < ‖Finance.simpleGains (τ m) (n m) (a m) W t ω - I t ω‖})
          atTop (𝓝 0)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
        TendstoUniformlyOn (fun m t ↦ Finance.simpleGains (τ (φ m)) (n (φ m)) (a (φ m)) W t ω)
          (fun t ↦ I t ω) atTop (Iic T) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, hMm, hmem, herr, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  obtain ⟨I, hIm, hIp, hIlim, hIunif, φ, hφ, hIpath⟩ :=
    exists_continuous_martingale_of_cauchySeq_Lp hMm
      (fun _ ↦ hcont.mono fun _ hω ↦ by simp only [Finance.simpleGains_def]; fun_prop) hmem
      fun T ↦ (hlim T).cauchySeq
  have hIto : Probability.IsItoIntegral ℱ P W H I :=
    ⟨hH.isStronglyPredictable, hIpath.mono fun _ h ↦ h.1, fun t ↦
      ⟨n, τ, a, fun m ↦ (hτ m).monotoneOn, ha,
        fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
          (.of_forall fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
            hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
          (herr t) hε,
        tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) (hIlim t).2⟩⟩
  exact ⟨I, n, τ, a, C, hIto, hIp, hIm, hτ₀, hτ, ha, hb, herr, fun T ↦ (hIlim T).2, hIunif,
    φ, hφ, hIpath.mono fun _ h ↦ h.2⟩

/-- **Existence of the continuous `L²` Brownian Itô integral**: every `BrownianIntegrable`
integrand against a filtered pre-Brownian motion `W` with a.s. continuous paths admits a
predictable continuous martingale Itô integral on the raw filtration. -/
theorem BrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : BrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, Probability.IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Martingale I ℱ P := by
  obtain ⟨I, _, _, _, _, hI, hIp, hIm, -⟩ := hH.exists_isItoIntegral_approx hW hcont
  exact ⟨I, hI, hIp, hIm⟩

namespace Probability.IsItoIntegral

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand agrees `P`-a.s. at horizon `T`
with `hW.l2Integral T`, without assuming path continuity of `W`. -/
theorem ae_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    I T =ᵐ[P] hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  obtain ⟨n, τ, a, -, -, hτ, ha, -, -, hmem, herr, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  have hl2 : Tendsto (fun m ↦ eLpNorm (Finance.simpleGains (τ m) (n m) (a m) W T -
      (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) : Ω → ℝ)) 2 P)
      atTop (𝓝 0) := (tendsto_iff_edist_tendsto_0.mp (hlim T)).congr fun m ↦ by
    rw [Lp.edist_def]; exact eLpNorm_congr_ae (((hmem m T).coeFn_toLp).sub .rfl)
  exact hI.ae_eq_of_approx hW (fun m ↦ (hτ m).monotoneOn) ha
    (fun _ hε ↦ MeasureTheory.tendsto_measure_lintegral_enorm_sq_of_tendsto_eLpNorm
      (.of_forall fun m ↦ (((Finance.isStronglyPredictable_simpleHolding (ha m)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).aestronglyMeasurable)
      (herr T) hε)
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num) hl2)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand belongs to `L²(P)` at each
finite horizon, without assuming path continuity of `W`. -/
theorem memLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    MemLp (I T) 2 P :=
  (Lp.memLp (hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)))).ae_eq
    (hI.ae_eq_l2Integral hW hH T).symm

/-- At every horizon `T`, the `L²(P)` class of `I T` equals `hW.l2Integral T` applied to `H`,
without assuming path continuity of `W`. -/
theorem toLp_eq_l2Integral (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    (hI.memLp hW hH T).toLp (I T) =
      hW.l2Integral T ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H)) :=
  Lp.ext ((hI.memLp hW hH T).coeFn_toLp.trans (hI.ae_eq_l2Integral hW hH T))

/-- **`L²`-seminorm Itô isometry**: `eLpNorm (I T) 2 P` equals the `L²((timeMeasure T).prod P)`
seminorm of `H` at every horizon `T`, without assuming path continuity of `W`. -/
theorem eLpNorm_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    eLpNorm (I T) 2 P =
      eLpNorm (Function.uncurry H) 2 ((timeMeasure T).prod P) := by
  have hnorm : ‖(hI.memLp hW hH T).toLp (I T)‖ =
      ‖(hH.memLp_predictableMeasure T).toLp (Function.uncurry H)‖ := by
    rw [hI.toLp_eq_l2Integral hW hH T, (hW.l2Integral T).norm_map]
  simp only [Lp.norm_toLp, ℱ.predictableMeasure_def,
    eLpNorm_trim ℱ.predictable_le_prod hH.isStronglyPredictable] at hnorm
  exact (ENNReal.toReal_eq_toReal_iff' (hI.memLp hW hH T).eLpNorm_lt_top.ne
    (hH.memLp_timeMeasure T).eLpNorm_lt_top.ne).mp hnorm

private theorem brownianIntegrable_indicator_Ioi (hH : BrownianIntegrable ℱ P H) (s : ℝ≥0) :
    BrownianIntegrable ℱ P (fun u ω ↦ (Ioi s).indicator (H · ω) u) := by
  have heq : (fun u ω ↦ (Ioi s).indicator (H · ω) u) =
      fun u ω ↦ ((Ioi s ×ˢ (univ : Set Ω)).indicator (Function.uncurry H)) (u, ω) := by
    ext u ω
    by_cases hu : s < u <;> simp [hu]
  rw [heq]
  exact hH.indicator (measurableSet_predictable_Ioi_prod (i := s) MeasurableSet.univ)

/-- **`(s, t]`-increment `L²`-seminorm Itô isometry**: for `s ≤ t`, `eLpNorm (I t - I s) 2 P` equals
the `L²((timeMeasure t).prod P)` seminorm of `H · 1_{(s, t]}`, without path continuity of `W`. -/
theorem eLpNorm_sub_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t) :
    eLpNorm (I t - I s) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioc s t).indicator (H · p.2) p.1) 2
        ((timeMeasure t).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hsub : eLpNorm (I t - I s) 2 P =
      eLpNorm (fun p : ℝ≥0 × Ω ↦ (Ioi s).indicator (H · p.2) p.1) 2 ((timeMeasure t).prod P) := by
    simpa only [Pi.sub_def, Function.uncurry_def, min_eq_left hst] using
      (hI.indicator_Ioi hW s).eLpNorm_eq hW (brownianIntegrable_indicator_Ioi hH s) t
  refine hsub.trans (eLpNorm_congr_ae ?_)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure t)
    (ν := P)).ae (ae_mem_Ioc_timeMeasure t)] with p hp
  by_cases hps : s < p.1 <;> simp [hps, hp.2]

/-- The `L²(P)` distance between the elementary gains of a left-measurable `L²` simple strategy on
a nondecreasing grid and an Itô integral of `K` equals the `L²((timeMeasure T).prod P)` distance
between their integrands, without assuming path continuity of `W`. -/
theorem eLpNorm_simpleGains_sub_eq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hK : BrownianIntegrable ℱ P K) (hI : IsItoIntegral ℱ P W K I)
    {n : ℕ} {γ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ} (hγ : MonotoneOn γ (Iic n))
    (ha : ∀ j < n, StronglyMeasurable[ℱ (γ j)] (a j))
    (ha₂ : ∀ j < n, MemLp (a j) 2 P) (T : ℝ≥0) :
    eLpNorm (Finance.simpleGains γ n a W T - I T) 2 P =
      eLpNorm (fun p ↦ Finance.simpleHolding γ n a p.1 p.2 - K p.1 p.2) 2
        ((timeMeasure T).prod P) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  rw [← Lp.edist_toLp_toLp _ _ (hW.memLp_simpleGains hγ ha ha₂ T) (hI.memLp hW hK T),
    ← hW.l2Integral_simpleHolding hγ ha T
      (Finance.memLp_simpleHolding_predictableMeasure ha ha₂ T)
      (hW.memLp_simpleGains hγ ha ha₂ T),
    hI.toLp_eq_l2Integral hW hK T, (hW.l2Integral T).isometry.edist_eq, Lp.edist_toLp_toLp,
    ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod
      ((Finance.isStronglyPredictable_simpleHolding ha).sub hK.isStronglyPredictable)]
  rfl

/-- **`L²(P)` time continuity**: the `L²(P)` class `t ↦ (hI.memLp hW hH t).toLp (I t)` of a
continuous Itô integral of a `BrownianIntegrable` integrand varies continuously in `t`, without
assuming path continuity of `W`. -/
theorem continuous_toLp (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) :
    Continuous fun t : ℝ≥0 ↦ (hI.memLp hW hH t).toLp (I t) := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  refine continuous_iff_continuousAt.2 fun t₀ ↦ tendsto_iff_edist_tendsto_0.2 ?_
  have hne_fst : ∀ᵐ t ∂timeMeasure (t₀ + 1), t ≠ t₀ := by
    simp only [ae_iff, ne_eq, not_not, ofPred_eq_eq_singleton,
      timeMeasure_apply _ (measurableSet_singleton t₀)]
    by_cases h0 : t₀ ∈ Ioc 0 (t₀ + 1) <;> simp [h0]
  have hne : ∀ᵐ p ∂(timeMeasure (t₀ + 1)).prod P, p.1 ≠ t₀ :=
    (Measure.quasiMeasurePreserving_fst (μ := timeMeasure (t₀ + 1)) (ν := P)).ae hne_fst
  have hlim : Tendsto (fun t ↦ eLpNorm
      (fun p : ℝ≥0 × Ω ↦ (uIoc t₀ t).indicator (H · p.2) p.1 - 0) 2
        ((timeMeasure (t₀ + 1)).prod P)) (𝓝 t₀) (𝓝 0) := by
    refine tendsto_eLpNorm_sub_of_ae_tendsto (C := 1) (by norm_num)
      (.of_forall fun t ↦ (hH.memLp_timeMeasure (t₀ + 1)).aestronglyMeasurable.indicator
        ((measurableSet_uIoc (a := t₀) (b := t)).prod MeasurableSet.univ) |>.congr
          (.of_forall fun p ↦ by
            by_cases hp : p.1 ∈ uIoc t₀ t <;> simp [Function.uncurry_def, hp]))
      (hH.memLp_timeMeasure (t₀ + 1))
      (.of_forall fun t ↦ .of_forall fun p ↦ by
        simpa only [Pi.zero_apply, sub_zero, ENNReal.coe_one, one_mul, Function.uncurry_def] using
          eNorm_indicator_le_eNorm_self (H · p.2) p.1)
      (hne.mono fun p hp ↦ tendsto_const_nhds.congr' <| by
        rcases lt_or_gt_of_ne hp with hlt | hgt
        · filter_upwards [eventually_gt_nhds hlt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hlt.not_gt, ht.not_gt])]
        · filter_upwards [eventually_lt_nhds hgt] with t ht
          rw [Set.indicator_of_notMem (by simp [Set.mem_uIoc, hgt.not_ge, ht.not_ge])])
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ zero_le)
    (Eventually.mono (Iio_mem_nhds (lt_add_one t₀)) fun t (ht : t < t₀ + 1) ↦ ?_)
  rw [Lp.edist_toLp_toLp]
  simp only [sub_zero]
  rcases le_total t₀ t with hle | hle
  · rw [hI.eLpNorm_sub_eq hW hH hle, uIoc_of_le hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono ht.le) le_rfl)
  · rw [← eLpNorm_neg, neg_sub, hI.eLpNorm_sub_eq hW hH hle, uIoc_of_ge hle]
    exact eLpNorm_mono_measure _ (Measure.prod_mono (timeMeasure_mono le_self_add) le_rfl)

/-- Every continuous Itô integral of a `BrownianIntegrable` integrand has expectation zero at every
horizon, without assuming path continuity of `W` or adaptation of `I`. -/
theorem integral_eq_zero (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ∂P = 0 :=
  (integral_congr_ae (hI.ae_eq_l2Integral hW hH T)).trans (hW.integral_l2Integral T _)

/-- **Polarized Itô isometry**: `E[I T · J T] = E[∫_{(0, T]} H K]` for `BrownianIntegrable`
integrands `H` and `K`, without assuming path continuity of `W`. -/
theorem integral_mul (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hK : BrownianIntegrable ℱ P K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) (T : ℝ≥0) :
    ∫ ω, I T ω * J T ω ∂P = ∫ p, H p.1 p.2 * K p.1 p.2 ∂(timeMeasure T).prod P := by
  have hmap := (hW.l2Integral T).inner_map_map
    ((hK.memLp_predictableMeasure T).toLp (Function.uncurry K))
    ((hH.memLp_predictableMeasure T).toLp (Function.uncurry H))
  rw [← hJ.toLp_eq_l2Integral hW hK T, ← hI.toLp_eq_l2Integral hW hH T,
    L2.inner_def, L2.inner_def] at hmap
  simp only [RCLike.inner_apply, conj_trivial] at hmap
  rw [← integral_congr_ae (((hI.memLp hW hH T).coeFn_toLp.and (hJ.memLp hW hK T).coeFn_toLp).mono
      fun _ ⟨h1, h2⟩ ↦ congrArg₂ (· * ·) h1 h2), hmap,
    integral_congr_ae (((hH.memLp_predictableMeasure T).coeFn_toLp.and
      (hK.memLp_predictableMeasure T).coeFn_toLp).mono fun _ ⟨h1, h2⟩ ↦ congrArg₂ (· * ·) h1 h2)]
  exact ℱ.integral_predictableMeasure P (hH.isStronglyPredictable.mul hK.isStronglyPredictable) T

/-- **Bochner-integral Itô isometry**: `E[(I T)²] = E[∫_{(0, T]} H²]` for `BrownianIntegrable`
`H`, without assuming path continuity of `W`. -/
theorem integral_sq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) (T : ℝ≥0) :
    ∫ ω, I T ω ^ 2 ∂P = ∫ p, H p.1 p.2 ^ 2 ∂(timeMeasure T).prod P := by
  simpa only [sq] using hI.integral_mul hW hH hH hI T

/-- **`(s, t]`-increment Bochner-integral Itô isometry**: for `s ≤ t`,
`E[(I t - I s)²] = E[∫_{(s, t]} H²]`, without assuming path continuity of `W`. -/
theorem integral_sub_sq (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I) {s t : ℝ≥0} (hst : s ≤ t) :
    ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p, (Ioc s t).indicator (H · p.2) p.1 ^ 2 ∂(timeMeasure t).prod P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have heq : ∫ ω, (I t ω - I s ω) ^ 2 ∂P =
      ∫ p, (Ioi s).indicator (H · p.2) p.1 ^ 2 ∂(timeMeasure t).prod P := by
    simpa only [min_eq_left hst] using
      (hI.indicator_Ioi hW s).integral_sq hW (brownianIntegrable_indicator_Ioi hH s) t
  refine heq.trans (integral_congr_ae ?_)
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := timeMeasure t)
    (ν := P)).ae (ae_mem_Ioc_timeMeasure t)] with p hp
  by_cases hps : s < p.1 <;> simp [hps, hp.2]

/-- Every strongly adapted continuous Itô integral of a `BrownianIntegrable` integrand is a true
martingale on the raw filtration, without assuming path continuity of `W`. -/
theorem martingale (hW : IsFilteredPreBrownianReal ℱ W P)
    (hH : BrownianIntegrable ℱ P H) (hI : IsItoIntegral ℱ P W H I)
    (hI_adap : StronglyAdapted ℱ I) :
    Martingale I ℱ P := by
  let := (hW.hasLaw_eval 0).isProbabilityMeasure
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  obtain ⟨_, _, _, -, -, -, -, -, hMm, hmem, -, hlim⟩ :=
    exists_simpleHolding_tendsto_l2Integral hW hH
  obtain ⟨Z, hZm, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hMm hmem fun T ↦ (hlim T).cauchySeq
  refine hZm.congr hI_adap fun T ↦ ?_
  have heq : (hZlim T).1.toLp (Z T) = (hI.memLp hW hH T).toLp (I T) :=
    (tendsto_nhds_unique (tendsto_iff_edist_tendsto_0.mpr <| by
      simpa only [Lp.edist_toLp_toLp] using (hZlim T).2) (hlim T)).trans
      (hI.toLp_eq_l2Integral hW hH T).symm
  exact ((heq ▸ (hZlim T).1.coeFn_toLp).symm).trans (hI.memLp hW hH T).coeFn_toLp

end Probability.IsItoIntegral

end TauCeti
