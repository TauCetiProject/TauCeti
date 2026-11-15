/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Energy.Bound
public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Energy
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Process.ContinuousAE

/-!
# The continuous time-indexed Brownian Itô integral: specification, algebra, and uniqueness

`TauCeti.IsItoIntegral ℱ P W H I` specifies when a real-valued process `I` is a continuous
time-indexed Itô stochastic integral of a predictable integrand `H` against `W` under `P`:
`H` is predictable for `ℱ`, `I` has `P`-almost-surely continuous sample paths, and at every
horizon `t` there exist bounded, left-measurable simple strategies whose holdings converge to `H`
in pathwise square energy on `(0, t]` in probability while their elementary gains against `W` at
`t` converge to `I t` in probability.

This relational specification uses `TauCeti.Finance.simpleHolding` and
`TauCeti.Finance.simpleGains` directly on a raw filtration without completeness, right continuity,
or moment assumptions on `H`. Pathwise square energy is measured by the `ℝ≥0∞`-valued lower
Lebesgue integral against `TauCeti.Probability.timeMeasure t`, so infinite-energy paths are never
conflated with zero energy; in particular every integrand admitting an `IsItoIntegral` belongs to
`TauCeti.LocallyBrownianIntegrable ℱ P`.

## Main definitions and results

* `TauCeti.IsItoIntegral`: relational specification of a continuous Brownian Itô integral process.
* `TauCeti.IsItoIntegral.mono_filtration`, `locallyBrownianIntegrable`: filtration enlargement and
  automatic membership of the integrand in `TauCeti.LocallyBrownianIntegrable ℱ P`.
* `TauCeti.IsItoIntegral.simpleHolding`, `indicator_Ioc`, `const_sub_initial`, `const`: elementary
  holdings, predictable interval indicators, and `ℱ 0`-measurable time-constant integrands have
  explicit continuous Itô integrals on finite measures when `W` has almost-surely continuous paths,
  with no height-bound or moment assumptions.
* `TauCeti.IsItoIntegral.add`, `sub`, `neg`, `bdd_mul`, `const_mul`, `smul`: linearity and bounded
  `ℱ 0`-measurable random multipliers.
* `TauCeti.IsItoIntegral.tendstoInMeasure_simpleGains`, `ae_eq_of_approx`, `indist`: convergence
  in measure of approximating elementary gains and uniqueness up to `P`-indistinguishability for
  any filtered pre-Brownian integrator, requiring no path-continuity assumption on `W`.
* `TauCeti.IsItoIntegral.indicator_Ioi_bdd_mul`, `indicator_Ioi`: post-`u` restriction and bounded
  `ℱ u`-measurable random multipliers against a filtered pre-Brownian integrator.
* `TauCeti.IsItoIntegral.congr_integrand`, `indist_of_ae_eq`: invariance and indistinguishability
  under `(dt × P)`-almost-everywhere integrand equality on each finite horizon.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open Finset hiding Iic mem_Iic
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W B H K I J : ℝ≥0 → Ω → ℝ}

/-- `IsItoIntegral ℱ P W H I` means that `I` is a continuous time-indexed Brownian Itô integral
of the predictable integrand `H` against `W` under `P`: `H` is literally predictable for `ℱ`,
`I` has `P`-almost-surely continuous paths, and at each horizon `t` there exist bounded,
left-measurable simple strategies whose holdings converge to `H` in pathwise square energy on
`(0, t]` in probability while their elementary gains against `W` at `t` converge to `I t` in
probability. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- The integral process has `P`-almost-surely continuous sample paths. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At every horizon `t`, bounded left-measurable simple strategies approximate `H` in pathwise
  square energy in probability on `(0, t]` while their elementary gains approximate `I t` in
  probability. -/
  exists_seq_approx : ∀ t : ℝ≥0,
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
      (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
      (∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i)) ∧
      (∀ k i, i < n k → ∃ C : ℝ, ∀ ω, ‖a k i ω‖ ≤ C) ∧
      (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
      TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t)

/-- Unfolding characterization of `IsItoIntegral`. -/
theorem isItoIntegral_iff :
    IsItoIntegral ℱ P W H I ↔
      IsStronglyPredictable ℱ H ∧
      (∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)) ∧
      ∀ t : ℝ≥0, ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
        (∀ k, MonotoneOn (τ k) (Iic (n k))) ∧
        (∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i)) ∧
        (∀ k i, i < n k → ∃ C : ℝ, ∀ ω, ‖a k i ω‖ ≤ C) ∧
        (∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
          ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
            ∂Probability.timeMeasure t}) atTop (𝓝 0)) ∧
        TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t) :=
  ⟨fun h ↦ ⟨h.1, h.2, h.3⟩, fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

namespace IsItoIntegral

/-! ### Congruence, filtration enlargement, initial value, and pathwise domain -/

/-- Replacing an Itô integral by an indistinguishable process preserves `IsItoIntegral`. -/
theorem of_indist (hI : IsItoIntegral ℱ P W H I) (hIJ : I ≡ᵐ[P] J) :
    IsItoIntegral ℱ P W H J where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hIJ] with ω hω heq
    exact hω.congr fun t ↦ heq t
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, ha, hb, henergy, hgains.congr_right (hIJ.ae_eq_eval t)⟩

/-- Replacing the integrator by a modification preserves `IsItoIntegral`. -/
theorem congr_integrator (hI : IsItoIntegral ℱ P W H I) (hWB : ∀ s, W s =ᵐ[P] B s) :
    IsItoIntegral ℱ P B H I where
  isStronglyPredictable := hI.isStronglyPredictable
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, hb, henergy, hgains.congr_left fun k ↦ ?_⟩
    have hall : ∀ᵐ ω ∂P, ∀ j ≤ n k, W (min (τ k j) t) ω = B (min (τ k j) t) ω :=
      (ae_ball_iff (finite_Iic (n k)).countable).2 fun j _ ↦ hWB (min (τ k j) t)
    filter_upwards [hall] with ω hω
    exact Finance.simpleGains_congr_price ω hω

/-- Replacing the integrand by a predictable process agreeing `(dt × P)`-almost everywhere on
every finite horizon preserves `IsItoIntegral`. -/
theorem congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P]
      Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    have hswap : (fun p : Ω × ℝ≥0 ↦ H p.2 p.1) =ᵐ[P.prod (Probability.timeMeasure t)]
        fun p : Ω × ℝ≥0 ↦ K p.2 p.1 :=
      (Measure.measurePreserving_swap (μ := P)
        (ν := Probability.timeMeasure t)).quasiMeasurePreserving.ae_eq_comp (hHK t)
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] fun s ↦ K s ω :=
      Measure.ae_ae_of_ae_prod hswap
    refine ⟨n, τ, a, hτ, ha, hb, fun ε hε ↦ (henergy ε hε).congr fun k ↦ ?_, hgains⟩
    refine measure_congr ?_
    filter_upwards [hsec] with ω hω
    have hlin : (∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t) =
        ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - K s ω‖ₑ ^ 2
          ∂Probability.timeMeasure t := by
      refine lintegral_congr_ae ?_
      filter_upwards [hω] with s hs
      rw [hs]
    simp only [hlin]

/-- Enlarging the filtration preserves `IsItoIntegral`. -/
theorem mono_filtration {𝒢 : Filtration ℝ≥0 mΩ} (hI : IsItoIntegral ℱ P W H I) (hle : ℱ ≤ 𝒢) :
    IsItoIntegral 𝒢 P W H I where
  isStronglyPredictable := hI.isStronglyPredictable.mono (Filtration.predictable_mono hle)
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    exact ⟨n, τ, a, hτ, fun k i hi ↦ (ha k i hi).mono (hle (τ k i)), hb, henergy, hgains⟩

/-- Every Itô integral vanishes almost surely at time `0`. -/
theorem eval_zero_ae_eq_zero (hI : IsItoIntegral ℱ P W H I) : I 0 =ᵐ[P] 0 := by
  obtain ⟨n, τ, a, hτ, -, -, -, hgains⟩ := hI.exists_seq_approx 0
  have hzero (k : ℕ) : Finance.simpleGains (τ k) (n k) (a k) W 0 = 0 := by
    ext ω
    exact Finance.simpleGains_of_le (hτ k) bot_le W ω
  simp_rw [hzero] at hgains
  exact tendstoInMeasure_ae_unique hgains tendstoInMeasure_const

/-- Every integrand admitting an `IsItoIntegral` has finite pathwise square energy on every finite
horizon almost surely (`LocallyBrownianIntegrable ℱ P H`), with no finiteness assumption on `P` or
Brownian assumption on `W`. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun N ↦ ?_⟩
  obtain ⟨n, τ, a, -, ha, -, henergy, -⟩ := hI.exists_seq_approx N
  let E (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure N
  have hpos (j : ℕ) : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ j :=
    ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top) j
  choose φ hφ using fun j ↦ ((henergy 1 zero_lt_one).eventually (gt_mem_nhds (hpos j))).exists
  have h2 : (∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j) ≠ ∞ := by
    rw [ENNReal.tsum_geometric_two]
    exact ENNReal.ofNat_ne_top
  have hsum : (∑' j : ℕ, P {ω | 1 ≤ E (φ j) ω}) ≠ ∞ :=
    ne_top_of_le_ne_top h2 (tsum_le_tsum fun j ↦ (hφ j).le)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨j, hj⟩ := hω.exists
  rw [not_le] at hj
  rw [← NNReal.coe_natCast N, NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω) 2
      (Probability.timeMeasure N) := by
    refine MemLp.of_bound
      (((Finance.isStronglyPredictable_simpleHolding (ha (φ j))).mono ℱ.predictable_le_prod)
        |>.measurable.comp (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
      (∑ i ∈ range (n (φ j)), ‖a (φ j) i ω‖) (.of_forall fun s ↦ ?_)
    rw [Finance.simpleHolding_def]
    exact (norm_sum_le _ _).trans (sum_le_sum fun i _ ↦ norm_indicator_le_norm_self _ _)
  have hdiff : MemLp (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω - H s ω) 2
      (Probability.timeMeasure N) := by
    have hm : AEStronglyMeasurable
        (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω - H s ω)
        (Probability.timeMeasure N) :=
      ((((Finance.isStronglyPredictable_simpleHolding (ha (φ j))).sub hI.isStronglyPredictable)
        |>.mono ℱ.predictable_le_prod).measurable.comp
          (measurable_id.prodMk measurable_const)).aestronglyMeasurable
    rw [memLp_iff, eLpNorm_eq_lintegral_rpow_eNorm_toReal (by norm_num) (by norm_num) hm]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (hj.trans_le le_top).ne
  exact (hL.sub hdiff).ae_eq (.of_forall fun _ ↦ sub_sub_cancel _ _)

/-! ### Elementary and constant integrands -/

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp]
theorem zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := Eventually.of_forall fun _ ↦ continuous_const
  exists_seq_approx t := by
    refine ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ _ _ _ ↦ le_rfl,
      fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim, fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim,
      fun ε hε ↦ ?_, ?_⟩
    · simp [Finance.simpleHolding_def, hε.not_ge]
    · have hg : (fun _ : ℕ ↦ Finance.simpleGains (fun _ ↦ 0) 0 (fun _ ↦ 0) W t) =
          fun _ : ℕ ↦ (0 : Ω → ℝ) := by
        ext
        simp [Finance.simpleGains_def]
      rw [hg]
      exact tendstoInMeasure_const

/-- A uniformly bounded left-measurable simple holding has its elementary gains as an Itô integral
on any measure `P` whenever `W` has `P`-almost-surely continuous paths. -/
theorem simpleHolding_of_bdd {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, ∃ C : ℝ, ∀ ω, ‖a i ω‖ ≤ C) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := by
    filter_upwards [hcont] with ω hω
    simp only [Finance.simpleGains_def]
    fun_prop
  exists_seq_approx _ := by
    refine ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha, fun _ ↦ hb,
      fun ε hε ↦ ?_, tendstoInMeasure_const⟩
    simp [sub_self, hε.not_ge]

/-- On a finite measure `P`, every left-measurable simple holding has its elementary gains as a
continuous Itô integral whenever `W` has `P`-almost-surely continuous paths, with no boundedness
or moment hypothesis on the heights. -/
theorem simpleHolding [IsFiniteMeasure P] {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := hcont.mono fun ω hω ↦ by simp only [Finance.simpleGains_def]; fun_prop
  exists_seq_approx t := by
    let A (k : ℕ) : Set Ω := ⋃ i ∈ range n, {ω | (k : ℝ) < ‖a i ω‖}
    let a' (k i : ℕ) : Ω → ℝ := {ω | ‖a i ω‖ ≤ (k : ℝ)}.indicator (a i)
    have hAm (k : ℕ) : MeasurableSet (A k) :=
      (range n).measurableSet_biUnion fun i hi ↦
        ((ha i (Finset.mem_range.mp hi)).mono (ℱ.le _)).norm.measurable measurableSet_Ioi
    have hAlim : Tendsto (fun k ↦ P (A k)) atTop (𝓝 0) := by
      have hmem : ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ω ∈ A k ↔ ω ∈ (∅ : Set Ω) := by
        refine .of_forall fun ω ↦ ?_
        obtain ⟨K, hK⟩ := exists_nat_ge (∑ i ∈ range n, ‖a i ω‖)
        filter_upwards [eventually_ge_atTop K] with k hk
        simp only [A, Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
        exact fun i hi ↦ (single_le_sum (fun j _ ↦ norm_nonneg (a j ω))
          (Finset.mem_range.mpr hi)).trans (hK.trans (Nat.cast_le.mpr hk))
      simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
        atTop MeasurableSet.empty hAm hmem
    have ha' (k i : ℕ) (hi : i < n) : StronglyMeasurable[ℱ (τ i)] (a' k i) :=
      (ha i hi).indicator (measurableSet_le (ha i hi).norm.measurable measurable_const)
    have hb' (k i : ℕ) (_ : i < n) : ∃ C : ℝ, ∀ ω, ‖a' k i ω‖ ≤ C := ⟨k, fun ω ↦ by
      dsimp only [a']; by_cases h : ω ∈ {ω | ‖a i ω‖ ≤ (k : ℝ)}
      · rw [indicator_of_mem h]; exact Set.mem_ofPred_eq.mp h
      · rw [indicator_of_notMem h, norm_zero]; exact Nat.cast_nonneg k⟩
    have heq_of_notMem {k : ℕ} {ω : Ω} (hω : ω ∉ A k) {i : ℕ} (hi : i ∈ range n) :
        a' k i ω = a i ω := indicator_of_mem (s := {ω' | ‖a i ω'‖ ≤ (k : ℝ)})
      (Set.mem_ofPred_eq.mpr (le_of_not_gt fun hlt ↦
        hω (Set.mem_biUnion hi (Set.mem_ofPred_eq.mpr hlt)))) _
    refine ⟨fun _ ↦ n, fun _ ↦ τ, a', fun _ ↦ hτ, ha', hb', fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAlim
        (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ ?_
      by_contra hnot
      have hhold (s : ℝ≥0) :
          Finance.simpleHolding τ n (a' k) s ω = Finance.simpleHolding τ n a s ω := by
        simp only [Finance.simpleHolding_def]; exact sum_congr rfl fun _ hi ↦ by
          rw [heq_of_notMem hnot hi]
      simp [hhold, hε.not_ge] at hω
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAlim
        (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ ?_
      by_contra hnot
      have hgain : Finance.simpleGains τ n (a' k) W t ω = Finance.simpleGains τ n a W t ω := by
        simp only [Finance.simpleGains_def]; exact sum_congr rfl fun _ hi ↦ by
          rw [heq_of_notMem hnot hi]
      simp [hgain, hε.not_ge] at hω

/-- On a finite measure `P`, an `ℱ u`-measurable random variable `ξ` held on `(u, v]` (with
`u ≤ v`) has clipped increment gains `ξ * (W (v ⊓ t) - W (u ⊓ t))` as its continuous Itô integral
whenever `W` has `P`-almost-surely continuous paths. -/
theorem indicator_Ioc [IsFiniteMeasure P] {u v : ℝ≥0} {ξ : Ω → ℝ} (huv : u ≤ v)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hξ : StronglyMeasurable[ℱ u] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ ξ ω) t)
      (fun t ω ↦ ξ ω * (W (min v t) ω - W (min u t) ω)) := by
  let τ : ℕ → ℝ≥0 := fun i ↦ if i = 0 then u else v
  have hτ : MonotoneOn τ (Iic 1) := by
    intro i _ j _ hij
    dsimp [τ]
    split_ifs with hi0 hj0 hj0'
    · exact le_rfl
    · exact huv
    · omega
    · exact le_rfl
  have h := simpleHolding (ℱ := ℱ) (P := P) (n := 1) (τ := τ) (a := fun _ ↦ ξ) hcont hτ
    (fun i hi ↦ by obtain rfl : i = 0 := (by omega); exact hξ)
  have h1 : Finance.simpleHolding τ 1 (fun _ ↦ ξ) =
      fun t ω ↦ (Ioc u v).indicator (fun _ ↦ ξ ω) t := by
    ext t ω
    simp [Finance.simpleHolding_def, τ]
  have h2 : Finance.simpleGains τ 1 (fun _ ↦ ξ) W =
      fun t ω ↦ ξ ω * (W (min v t) ω - W (min u t) ω) := by
    ext t ω
    simp [Finance.simpleGains_def, τ]
  rwa [h1, h2] at h

/-- On a finite measure `P`, a time-constant `ℱ 0`-measurable random variable `ξ` has
`t ↦ ξ * (W t - W 0)` as a continuous Itô integral whenever `W` has `P`-almost-surely continuous
paths, with no moment assumption on `ξ` and without assuming `W 0 = 0`. -/
theorem const_sub_initial [IsFiniteMeasure P] {ξ : Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * (W t ω - W 0 ω)) where
  isStronglyPredictable :=
    ((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable
  ae_continuous := by
    filter_upwards [hcont] with ω hω
    fun_prop
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ :=
      (indicator_Ioc (P := P) (zero_le : (0 : ℝ≥0) ≤ t) hcont hξ).exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, hb, fun ε hε ↦ (henergy ε hε).congr fun k ↦ ?_, ?_⟩
    · congr 1
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [lintegral_congr_ae ((Probability.ae_mem_Ioc_timeMeasure t).mono fun s hs ↦ by
        rw [indicator_of_mem hs])]
    · simpa only [min_self, min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)] using hgains

/-- On a finite measure `P`, when `W` has `P`-almost-surely continuous paths and `W 0 = 0` almost
surely, a time-constant `ℱ 0`-measurable random variable `ξ` has `t ↦ ξ * W t` as a continuous
Itô integral. -/
theorem const [IsFiniteMeasure P] {ξ : Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hW₀ : W 0 =ᵐ[P] 0) (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * W t ω) := by
  refine (const_sub_initial hcont hξ).of_indist ?_
  filter_upwards [hW₀] with ω hω t
  simp [hω]

/-! ### Linearity and bounded initial multipliers -/

private theorem tendsto_measure_lintegral_bdd_mul_le
    {f g : ℕ → ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {M : ℝ≥0} (hM0 : (M : ℝ≥0∞) ≠ 0)
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hle : ∀ k s ω, ‖f k s ω‖ₑ ^ 2 ≤ (M : ℝ≥0∞) ^ 2 * ‖g k s ω‖ₑ ^ 2)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  refine MeasureTheory.tendsto_measure_ge_of_ne_top (fun ε hε _ ↦ ?_) hε
  have hM2_pos : (0 : ℝ≥0∞) < (M : ℝ≥0∞) ^ 2 := by
    rw [sq]
    exact ENNReal.mul_pos hM0 hM0
  have hM2_top : (M : ℝ≥0∞) ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (henergy (ε / (M : ℝ≥0∞) ^ 2) (ENNReal.div_pos hε.ne' hM2_top))
    (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ ?_
  rw [Set.mem_ofPred_eq,
    ENNReal.div_le_iff_le_mul (Or.inl hM2_pos.ne') (Or.inl hM2_top), mul_comm]
  refine hω.trans ?_
  rw [← lintegral_const_mul' _ _ hM2_top]
  exact lintegral_mono fun s ↦ hle k s ω

/-- Multiplying an integrand by a bounded `ℱ 0`-measurable random variable `ξ` multiplies its Itô
integral by `ξ`, on any measure `P` and for any integrator `W`. -/
theorem bdd_mul (hI : IsItoIntegral ℱ P W H I) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ ξ ω * H t ω) (fun t ω ↦ ξ ω * I t ω) := by
  obtain ⟨Cξ, hCξ⟩ := hb
  let M : ℝ≥0 := ⟨max Cξ 0, le_max_right Cξ 0⟩
  have hξM (ω : Ω) : ‖ξ ω‖ₑ ≤ M := by
    rw [eNorm_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    exact (hCξ ω).trans (le_max_left Cξ 0)
  rcases eq_or_ne (M : ℝ≥0∞) 0 with hM0 | hM0
  · have hzero (ω : Ω) : ξ ω = 0 := by simpa using (hξM ω).trans_eq hM0
    have hH0 : (fun t ω ↦ ξ ω * H t ω) = 0 := by ext t ω; simp [hzero]
    have hI0 : (fun t ω ↦ ξ ω * I t ω) = 0 := by ext t ω; simp [hzero]
    rw [hH0, hI0]; exact zero
  refine ⟨(((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable).mul
    hI.isStronglyPredictable, hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω,
    fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hba, henergy, hgains⟩ := hI.exists_seq_approx t
  let a' (k i : ℕ) (ω : Ω) : ℝ := ξ ω * a k i ω
  refine ⟨n, τ, a', hτ, fun k i hi ↦ (hξ.mono (ℱ.mono bot_le)).mul (ha k i hi),
    fun k i hi ↦ ?_, fun ε hε ↦ ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hba k i hi
    refine ⟨max Cξ 0 * max C 0, fun ω ↦ ?_⟩
    simpa only [a', norm_mul] using mul_le_mul ((hCξ ω).trans (le_max_left Cξ 0))
      ((hC ω).trans (le_max_left C 0)) (norm_nonneg _) (le_max_right Cξ 0)
  · refine tendsto_measure_lintegral_bdd_mul_le hM0 henergy (fun k s ω ↦ ?_) hε
    have hhold : Finance.simpleHolding (τ k) (n k) (a' k) s ω =
        ξ ω * Finance.simpleHolding (τ k) (n k) (a k) s ω := by
      simp only [Finance.simpleHolding_def, a', mul_sum]
      exact sum_congr rfl fun i _ ↦ by by_cases hs : s ∈ Ioc (τ k i) (τ k (i + 1)) <;> simp [hs]
    rw [hhold, ← mul_sub, eNorm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left' (hξM ω) 2) zero_le
  · refine (hgains.bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ ?_) .rfl
    simp [Finance.simpleGains_def, a', smul_eq_mul, mul_sum, mul_assoc]

/-- Scaling an integrand by a constant scales its Itô integral. -/
theorem const_mul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (fun t ω ↦ c * H t ω) (fun t ω ↦ c * I t ω) :=
  hI.bdd_mul stronglyMeasurable_const ⟨‖c‖, fun _ ↦ le_rfl⟩

/-- Scalar-multiplication form of `IsItoIntegral.const_mul`. -/
theorem smul (hI : IsItoIntegral ℱ P W H I) (c : ℝ) :
    IsItoIntegral ℱ P W (c • H) (c • I) :=
  hI.const_mul c

/-- Negating an integrand negates its Itô integral. -/
theorem neg (hI : IsItoIntegral ℱ P W H I) :
    IsItoIntegral ℱ P W (-H) (-I) := by
  simpa [neg_one_smul] using hI.smul (-1 : ℝ)

/-- Adding two integrands adds their Itô integrals. -/
theorem add (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H + K) (I + J) where
  isStronglyPredictable := hI.isStronglyPredictable.add hJ.isStronglyPredictable
  ae_continuous := by
    filter_upwards [hI.ae_continuous, hJ.ae_continuous] with ω hIω hJω
    exact hIω.add hJω
  exists_seq_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hb₁, he₁, hg₁⟩ := hI.exists_seq_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hb₂, he₂, hg₂⟩ := hJ.exists_seq_approx t
    choose n τ b _ hτ hbm hbb hhold hgains using fun k ↦
      Finance.exists_simpleHolding_simpleGains_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    refine ⟨n, τ, b, fun k ↦ (hτ k).monotoneOn, hbm, fun k j hj ↦ ?_, fun ε hε ↦ ?_, ?_⟩
    · choose C₁ hC₁ using fun (i : Fin (n₁ k)) ↦ hb₁ k i.1 i.2
      choose C₂ hC₂ using fun (i : Fin (n₂ k)) ↦ hb₂ k i.1 i.2
      refine ⟨(∑ i : Fin (n₁ k), C₁ i) + ∑ i : Fin (n₂ k), C₂ i, fun ω ↦
        (hbb k j hj ω).trans (add_le_add ?_ ?_)⟩
      · rw [← Fin.sum_univ_eq_sum_range]
        exact sum_le_sum fun i _ ↦ hC₁ i ω
      · rw [← Fin.sum_univ_eq_sum_range]
        exact sum_le_sum fun i _ ↦ hC₂ i ω
    · simp_rw [hhold, Pi.add_apply, add_sub_add_comm]
      exact MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
        (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
            (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
        he₁ he₂ hε
    · exact (hg₁.add hg₂).congr (fun k ↦ .of_forall fun ω ↦ (hgains k W t ω).symm) .rfl

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-! ### Gains convergence, uniqueness, and post-`u` multipliers -/

/-- At any fixed horizon `t`, if a sequence of left-measurable simple strategies approximates `H`
in pathwise square energy in probability on `(0, t]`, then its elementary gains against a filtered
pre-Brownian motion `W` converge in probability to `I t`. Neither boundedness of the approximating
heights nor path continuity of `W` is required. -/
theorem tendstoInMeasure_simpleGains (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop (I t) := by
  obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, -, he₁, hg₁⟩ := hI.exists_seq_approx t
  choose m σ b _ hσ hbm _ hhold hgains_sub using fun k ↦
    Finance.exists_simpleHolding_simpleGains_sub ℱ (hτ k) (hτ₁ k) (ha k) (ha₁ k)
  have he_neg : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖H s ω - Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
    simpa only [eNorm_sub_rev] using he₁
  have he_sub : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := fun ε hε ↦ by
    have h := MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
      (f := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
      (g := fun k s ω ↦ H s ω - Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω)
      (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
        hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
          (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
      henergy he_neg hε
    simpa only [sub_add_sub_cancel, ← hhold] using h
  have hdiff := (hW.tendstoInMeasure_simpleGains_zero_of_lintegral
    (fun k ↦ (hσ k).monotoneOn) hbm he_sub).congr_left fun k ↦ .of_forall (hgains_sub k W t)
  exact (hdiff.add hg₁).congr (fun k ↦ .of_forall fun _ ↦ sub_add_cancel _ _)
    (.of_forall fun _ ↦ zero_add _)

/-- At any fixed horizon `t`, if a sequence of left-measurable simple strategies approximates `H`
in pathwise square energy in probability on `(0, t]` and its elementary gains against a filtered
pre-Brownian motion `W` converge in probability to `Y`, then `I t =ᵐ[P] Y`. Neither boundedness of
the approximating heights, path continuity of `W`, nor a full continuous process extending `Y` is
required. -/
theorem ae_eq_of_approx (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {t : ℝ≥0} {Y : Ω → ℝ}
    {n : ℕ → ℕ} {τ : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hτ : ∀ k, MonotoneOn (τ k) (Iic (n k)))
    (ha : ∀ k i, i < n k → StronglyMeasurable[ℱ (τ k i)] (a k i))
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hgains : TendstoInMeasure P (fun k ↦ Finance.simpleGains (τ k) (n k) (a k) W t) atTop Y) :
    I t =ᵐ[P] Y :=
  tendstoInMeasure_ae_unique (hI.tendstoInMeasure_simpleGains hW hτ ha henergy) hgains

/-- Two Itô integrals of the same integrand against a filtered pre-Brownian motion agree almost
surely at each horizon, without assuming path continuity of `W`. -/
theorem ae_eq_eval (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) (t : ℝ≥0) :
    I t =ᵐ[P] J t := by
  obtain ⟨n, τ, a, hτ, ha, -, he, hg⟩ := hJ.exists_seq_approx t
  exact hI.ae_eq_of_approx hW hτ ha he hg

/-- **Uniqueness of the continuous Brownian Itô integral**: any two continuous Itô integrals of the
same predictable integrand against a filtered pre-Brownian motion are `P`-indistinguishable. No
moment bound on `H` and no path-continuity hypothesis on `W` are required. -/
theorem indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J :=
  ProbabilityTheory.indist_of_ae_continuous hI.ae_continuous hJ.ae_continuous (hI.ae_eq_eval hW hJ)

/-- Any Itô integral of the zero integrand against a filtered pre-Brownian motion vanishes almost
surely at each horizon, without assuming path continuity of `W`. -/
theorem ae_eq_zero_of_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) (t : ℝ≥0) : I t =ᵐ[P] 0 :=
  hI.ae_eq_eval hW zero t

/-- Any Itô integral of the zero integrand against a filtered pre-Brownian motion is
indistinguishable from `0`. -/
theorem indist_zero_of_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) : I ≡ᵐ[P] 0 :=
  hI.indist hW zero

/-- **Integrand congruence for continuous Brownian Itô integrals**: if two predictable integrands
agree `(dt × P)`-almost everywhere on every finite horizon, then any continuous Itô integrals of
them against a filtered pre-Brownian motion are `P`-indistinguishable. -/
theorem indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P]
      Function.uncurry K)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    I ≡ᵐ[P] J := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  exact (hI.congr_integrand hJ.isStronglyPredictable hHK).indist hW hJ

private theorem isStronglyPredictable_indicator_Ioi_mul
    (hH : IsStronglyPredictable ℱ H) {u : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ u] ξ) :
    IsStronglyPredictable ℱ (fun t ω ↦ (Ioi u).indicator (fun s ↦ ξ ω * H s ω) t) := by
  classical
  have hξ_pred : IsStronglyPredictable ℱ (fun t ω ↦ (Ioi u).indicator (fun _ ↦ ξ ω) t) := by
    refine Measurable.stronglyMeasurable fun A hA ↦ ?_
    have hset : (Function.uncurry fun t ω ↦ (Ioi u).indicator (fun _ ↦ ξ ω) t) ⁻¹' A =
        if (0 : ℝ) ∈ A then (Ioi u ×ˢ (univ : Set Ω))ᶜ ∪ Ioi u ×ˢ (ξ ⁻¹' A)
        else Ioi u ×ˢ (ξ ⁻¹' A) := by
      ext ⟨s, ω⟩
      by_cases hs : u < s <;> by_cases h0 : (0 : ℝ) ∈ A <;> simp [Function.uncurry, hs, h0]
    rw [hset]
    split_ifs
    · exact (measurableSet_predictable_Ioi_prod MeasurableSet.univ).compl.union
        (measurableSet_predictable_Ioi_prod (hξ.measurable hA))
    · exact measurableSet_predictable_Ioi_prod (hξ.measurable hA)
  have heq : (fun t ω ↦ (Ioi u).indicator (fun s ↦ ξ ω * H s ω) t) =
      fun t ω ↦ (Ioi u).indicator (fun _ ↦ ξ ω) t * H t ω := by
    ext t ω
    by_cases ht : u < t <;> simp [ht]
  exact heq ▸ hξ_pred.mul hH

/-- Multiplying an integrand after time `u` by a bounded `ℱ u`-measurable random variable `ξ`
yields a continuous Itô integral against a filtered pre-Brownian motion `W` given by the post-`u`
increment `t ↦ ξ * (I t - I (min u t))`, without assuming path continuity of `W`. -/
theorem indicator_Ioi_bdd_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {u : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ u] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (fun s ↦ ξ ω * H s ω) t)
      (fun t ω ↦ ξ ω * (I t ω - I (min u t) ω)) := by
  obtain ⟨Cξ, hCξ⟩ := hb
  let M : ℝ≥0 := ⟨max Cξ 0, le_max_right Cξ 0⟩
  have hξM (ω : Ω) : ‖ξ ω‖ₑ ≤ M := by
    rw [eNorm_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]
    exact (hCξ ω).trans (le_max_left Cξ 0)
  rcases eq_or_ne (M : ℝ≥0∞) 0 with hM0 | hM0
  · have hzero (ω : Ω) : ξ ω = 0 := by simpa using (hξM ω).trans_eq hM0
    have hH0 : (fun t ω ↦ (Ioi u).indicator (fun s ↦ ξ ω * H s ω) t) = 0 := by
      ext t ω; simp [hzero]
    have hI0 : (fun t ω ↦ ξ ω * (I t ω - I (min u t) ω)) = 0 := by ext t ω; simp [hzero]
    rw [hH0, hI0]; exact zero
  refine ⟨isStronglyPredictable_indicator_Ioi_mul hI.isStronglyPredictable hξ,
    hI.ae_continuous.mono fun ω hω ↦ by fun_prop, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hba, henergy, hgains⟩ := hI.exists_seq_approx t
  have he_min (ε : ℝ≥0∞) (hε : 0 < ε) : Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure (min u t)}) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (henergy ε hε)
      (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ by
        simp only [Set.mem_ofPred_eq] at hω ⊢
        refine hω.trans ?_
        rw [← Probability.timeMeasure_restrict t u]
        exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hgains_min := hI.tendstoInMeasure_simpleGains hW hτ ha he_min
  let τ' (k i : ℕ) : ℝ≥0 := max (τ k i) u
  let a' (k i : ℕ) (ω : Ω) : ℝ := ξ ω * a k i ω
  refine ⟨n, τ', a', fun k _ hi _ hj hij ↦ max_le_max_right u (hτ k hi hj hij),
    fun k i hi ↦ ((hξ.mono (ℱ.mono (le_max_right _ _))).mul
      ((ha k i hi).mono (ℱ.mono (le_max_left _ _)))),
    fun k i hi ↦ ?_, fun ε hε ↦ ?_, ?_⟩
  · obtain ⟨C, hC⟩ := hba k i hi
    refine ⟨max Cξ 0 * max C 0, fun ω ↦ ?_⟩
    simpa only [a', norm_mul] using mul_le_mul ((hCξ ω).trans (le_max_left Cξ 0))
      ((hC ω).trans (le_max_left C 0)) (norm_nonneg _) (le_max_right Cξ 0)
  · refine tendsto_measure_lintegral_bdd_mul_le hM0 henergy (fun k s ω ↦ ?_) hε
    rw [Finance.simpleHolding_max_eq u ξ s ω]
    by_cases hs : u < s
    · simp only [Set.mem_Ioi.mpr hs, indicator_of_mem, ← mul_sub, eNorm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left' (hξM ω) 2) zero_le
    · simp [Set.mem_Ioi, hs]
  · refine ((hgains.sub hgains_min).bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ ?_) .rfl
    simpa only [smul_eq_mul, Pi.sub_apply] using
      (Finance.simpleGains_max_eq (hτ k) u ξ W t ω).symm

/-- Restricting an integrand to `(u, ∞)` yields a continuous Itô integral against a filtered
pre-Brownian motion `W` given by the post-`u` increment `t ↦ I t - I (min u t)`, without assuming
path continuity of `W`. -/
theorem indicator_Ioi (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (u : ℝ≥0) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (H · ω) t)
      (fun t ω ↦ I t ω - I (min u t) ω) := by
  simpa only [one_mul] using
    hI.indicator_Ioi_bdd_mul hW (u := u) (ξ := fun _ ↦ 1) stronglyMeasurable_const
      ⟨1, fun _ ↦ by norm_num⟩

end IsItoIntegral

end TauCeti
