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
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Finance.SimpleStrategy.Stopping
import TauCeti.Probability.Process.ContinuousAE

/-!
# The continuous time-indexed Brownian Itô integral: specification, algebra, and uniqueness

`TauCeti.IsItoIntegral ℱ P W H I` specifies when `I` is a continuous time-indexed Itô stochastic
integral of a predictable integrand `H` against `W` under `P` on a raw filtration: `H` is
predictable for `ℱ`, `I` has `P`-a.s. continuous paths, and at every horizon `t` bounded
left-measurable simple strategies approximate `H` in pathwise square energy on `(0, t]` in
probability while their gains against `W` at `t` converge to `I t` in probability.

## Main definitions and results

* `TauCeti.IsItoIntegral`: relational specification of a continuous Brownian Itô integral process.
* `TauCeti.IsItoIntegral.mono_filtration`, `locallyBrownianIntegrable`: filtration enlargement and
  automatic membership in `TauCeti.LocallyBrownianIntegrable ℱ P`.
* `TauCeti.IsItoIntegral.simpleHolding`, `indicator_Ioc`, `const_sub_initial`, `const`: elementary
  holdings, interval indicators, and `ℱ 0`-measurable constants when `W` is a.s. continuous.
* `TauCeti.IsItoIntegral.add`, `sub`, `neg`, `bdd_mul`, `const_mul`, `smul`: linearity and bounded
  `ℱ 0`-measurable multipliers.
* `TauCeti.IsItoIntegral.tendstoInMeasure_simpleGains`, `ae_eq_of_approx`, `indist`: gains
  convergence in measure and uniqueness up to `P`-indistinguishability against pre-Brownian `W`.
* `TauCeti.IsItoIntegral.indicator_Ioi_bdd_mul`, `indicator_Ioi`: post-`u` restriction and bounded
  `ℱ u`-measurable multipliers.
* `TauCeti.IsItoIntegral.congr_integrand`, `indist_of_ae_eq`: `(dt × P)`-a.e. integrand congruence.

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

/-- `IsItoIntegral ℱ P W H I` means `I` is a continuous Brownian Itô integral of the predictable
integrand `H` against `W` under `P`: `H` is predictable for `ℱ`, `I` is `P`-a.s. continuous, and at
each horizon `t` bounded left-measurable simple strategies approximate `H` in pathwise square
energy on `(0, t]` in probability while their gains converge to `I t` in probability. -/
structure IsItoIntegral (ℱ : Filtration ℝ≥0 mΩ) (P : Measure Ω)
    (W H I : ℝ≥0 → Ω → ℝ) : Prop where
  /-- The integrand is predictable for the declared filtration. -/
  isStronglyPredictable : IsStronglyPredictable ℱ H
  /-- The integral process has `P`-almost-surely continuous sample paths. -/
  ae_continuous : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω)
  /-- At each horizon `t`, bounded left-measurable simple strategies approximate `H` in pathwise
  square energy on `(0, t]` and `I t` via their elementary gains in probability. -/
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
  ae_continuous := hI.ae_continuous.mp <| hIJ.mono fun _ heq hω ↦ hω.congr fun t ↦ heq t
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
    exact ((ae_ball_iff (finite_Iic (n k)).countable).2 fun j _ ↦ hWB (min (τ k j) t)).mono
      Finance.simpleGains_congr_price

/-- Replacing the integrand by a predictable process agreeing `(dt × P)`-a.e. on each finite
horizon preserves `IsItoIntegral`. -/
theorem congr_integrand [SFinite P] (hI : IsItoIntegral ℱ P W H I)
    (hK : IsStronglyPredictable ℱ K)
    (hHK : ∀ t : ℝ≥0, Function.uncurry H =ᵐ[(Probability.timeMeasure t).prod P]
      Function.uncurry K) :
    IsItoIntegral ℱ P W K I where
  isStronglyPredictable := hK
  ae_continuous := hI.ae_continuous
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ := hI.exists_seq_approx t
    have hsec : ∀ᵐ ω ∂P, (fun s ↦ H s ω) =ᵐ[Probability.timeMeasure t] fun s ↦ K s ω :=
      Measure.ae_ae_of_ae_prod <| (Measure.measurePreserving_swap (μ := P)
        (ν := Probability.timeMeasure t)).quasiMeasurePreserving.ae_eq_comp (hHK t)
    refine ⟨n, τ, a, hτ, ha, hb, fun ε hε ↦ (henergy ε hε).congr fun k ↦ measure_congr ?_, hgains⟩
    filter_upwards [hsec] with ω hω
    rw [lintegral_congr_ae (hω.mono fun s hs ↦
      congrArg (‖Finance.simpleHolding (τ k) (n k) (a k) s ω - ·‖ₑ ^ 2) hs)]

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
  exact tendstoInMeasure_ae_unique
    (hgains.congr_left fun k ↦ .of_forall fun ω ↦ Finance.simpleGains_of_le (hτ k) bot_le W ω)
    tendstoInMeasure_const

/-- Every integrand admitting an `IsItoIntegral` belongs to `LocallyBrownianIntegrable ℱ P`,
with no finiteness assumption on `P` or Brownian assumption on `W`. -/
theorem locallyBrownianIntegrable (hI : IsItoIntegral ℱ P W H I) :
    LocallyBrownianIntegrable ℱ P H := by
  refine locallyBrownianIntegrable_iff_nat.2 ⟨hI.isStronglyPredictable, fun N ↦ ?_⟩
  obtain ⟨n, τ, a, -, ha, -, henergy, -⟩ := hI.exists_seq_approx N
  let E (k : ℕ) (ω : Ω) : ℝ≥0∞ :=
    ∫⁻ s, ‖Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω‖ₑ ^ 2 ∂Probability.timeMeasure N
  choose φ hφ using fun j : ℕ ↦ ((henergy 1 zero_lt_one).eventually (gt_mem_nhds
    (ENNReal.pow_pos (ENNReal.inv_pos.mpr ENNReal.ofNat_ne_top : (0 : ℝ≥0∞) < 2⁻¹) j))).exists
  have hsum : (∑' j : ℕ, P {ω | 1 ≤ E (φ j) ω}) ≠ ∞ :=
    ne_top_of_le_ne_top (by rw [ENNReal.tsum_geometric_two]; exact ENNReal.ofNat_ne_top)
      (tsum_le_tsum fun j ↦ (hφ j).le)
  filter_upwards [ae_eventually_notMem hsum] with ω hω
  obtain ⟨j, hj⟩ := hω.exists
  rw [← NNReal.coe_natCast N, NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
  have hpred := Finance.isStronglyPredictable_simpleHolding (ha (φ j))
  have hL : MemLp (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω) 2
      (Probability.timeMeasure N) :=
    MemLp.of_bound ((hpred.mono ℱ.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable)
      (∑ i ∈ range (n (φ j)), ‖a (φ j) i ω‖) (.of_forall fun s ↦ by
        rw [Finance.simpleHolding_def]
        exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_indicator_le_norm_self _ _))
  have hdiff : MemLp (fun s ↦ Finance.simpleHolding (τ (φ j)) (n (φ j)) (a (φ j)) s ω - H s ω) 2
      (Probability.timeMeasure N) :=
    (((hpred.sub hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
      (measurable_id.prodMk measurable_const) |>.aestronglyMeasurable
      |>.memLp_two_iff_lintegral_enorm_sq_lt_top).mpr (lt_trans (not_le.mp hj) ENNReal.one_lt_top)
  exact (hL.sub hdiff).ae_eq (.of_forall fun _ ↦ sub_sub_cancel _ _)

/-! ### Elementary and constant integrands -/

/-- The zero process is an Itô integral of the zero integrand. -/
@[simp]
theorem zero : IsItoIntegral ℱ P W 0 0 where
  isStronglyPredictable := stronglyMeasurable_const
  ae_continuous := .of_forall fun _ ↦ continuous_const
  exists_seq_approx t :=
    ⟨fun _ ↦ 0, fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ _ _ _ _ ↦ le_rfl,
      fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim, fun _ _ hi ↦ (Nat.not_lt_zero _ hi).elim,
      fun _ hε ↦ by simp [Finance.simpleHolding_def, hε.not_ge],
      tendstoInMeasure_const.congr_left fun _ ↦ .of_forall fun _ ↦ by
        simp [Finance.simpleGains_def]⟩

/-- A uniformly bounded left-measurable simple holding has its elementary gains as an Itô integral
on any measure `P` whenever `W` has `P`-almost-surely continuous paths. -/
theorem simpleHolding_of_bdd {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i))
    (hb : ∀ i < n, ∃ C : ℝ, ∀ ω, ‖a i ω‖ ≤ C) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := hcont.mono fun _ hω ↦ by simp only [Finance.simpleGains_def]; fun_prop
  exists_seq_approx _ :=
    ⟨fun _ ↦ n, fun _ ↦ τ, fun _ ↦ a, fun _ ↦ hτ, fun _ ↦ ha, fun _ ↦ hb,
      fun _ hε ↦ by simp [sub_self, hε.not_ge], tendstoInMeasure_const⟩

/-- On a finite measure `P`, every left-measurable simple holding has its elementary gains as an Itô
integral whenever `W` has `P`-a.s. continuous paths, with no boundedness or moment assumptions. -/
theorem simpleHolding [IsFiniteMeasure P] {n : ℕ} {τ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hτ : MonotoneOn τ (Iic n))
    (ha : ∀ i < n, StronglyMeasurable[ℱ (τ i)] (a i)) :
    IsItoIntegral ℱ P W (Finance.simpleHolding τ n a) (Finance.simpleGains τ n a W) where
  isStronglyPredictable := Finance.isStronglyPredictable_simpleHolding ha
  ae_continuous := hcont.mono fun _ hω ↦ by simp only [Finance.simpleGains_def]; fun_prop
  exists_seq_approx t := by
    let A (k : ℕ) : Set Ω := ⋃ i ∈ range n, {ω | (k : ℝ) < ‖a i ω‖}
    let a' (k i : ℕ) : Ω → ℝ := {ω | ‖a i ω‖ ≤ (k : ℝ)}.indicator (a i)
    have hAlim : Tendsto (fun k ↦ P (A k)) atTop (𝓝 0) := by
      simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure (As := A)
        atTop MeasurableSet.empty (fun k ↦ (range n).measurableSet_biUnion fun i hi ↦
          ((ha i (Finset.mem_range.mp hi)).mono (ℱ.le _)).norm.measurable measurableSet_Ioi)
        (.of_forall fun ω ↦ by
          obtain ⟨K, hK⟩ := exists_nat_ge (∑ i ∈ range n, ‖a i ω‖)
          filter_upwards [eventually_ge_atTop K] with k hk
          simp only [A, Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false, not_exists, not_lt]
          exact fun i hi ↦ (single_le_sum (fun j _ ↦ norm_nonneg (a j ω))
            (Finset.mem_range.mpr hi)).trans (hK.trans (Nat.cast_le.mpr hk)))
    have hzero {S : ℕ → Set Ω} (hS : ∀ k, S k ⊆ A k) : Tendsto (fun k ↦ P (S k)) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hAlim (fun _ ↦ zero_le)
        fun k ↦ measure_mono (hS k)
    have heq {k : ℕ} {ω : Ω} (hω : ω ∉ A k) {i : ℕ} (hi : i ∈ range n) : a' k i ω = a i ω :=
      indicator_of_mem (s := {ω' | ‖a i ω'‖ ≤ (k : ℝ)}) (Set.mem_ofPred_eq.mpr
        (le_of_not_gt fun hlt ↦ hω (Set.mem_biUnion hi (Set.mem_ofPred_eq.mpr hlt)))) _
    refine ⟨fun _ ↦ n, fun _ ↦ τ, a', fun _ ↦ hτ,
      fun k i hi ↦ (ha i hi).indicator
        (measurableSet_le (ha i hi).norm.measurable measurable_const),
      fun k i _ ↦ ⟨k, fun ω ↦ by
        simp only [a', Set.indicator_apply]; split_ifs with h
        · exact h
        · simp⟩,
      fun _ hε ↦ hzero fun k ω hω ↦ by_contra fun hnot ↦ ?_,
      fun _ hε ↦ hzero fun k ω hω ↦ by_contra fun hnot ↦ ?_⟩
    · have hhold (s : ℝ≥0) : Finance.simpleHolding τ n (a' k) s ω =
          Finance.simpleHolding τ n a s ω := by
        simp only [Finance.simpleHolding_def]; exact sum_congr rfl fun _ hi ↦ by rw [heq hnot hi]
      simp [hhold, hε.not_ge] at hω
    · have hgain : Finance.simpleGains τ n (a' k) W t ω = Finance.simpleGains τ n a W t ω := by
        simp only [Finance.simpleGains_def]; exact sum_congr rfl fun _ hi ↦ by rw [heq hnot hi]
      simp [hgain, hε.not_ge] at hω

/-- On a finite measure `P`, an `ℱ u`-measurable `ξ` held on `(u, v]` (`u ≤ v`) has clipped
increment gains `ξ * (W (v ⊓ t) - W (u ⊓ t))` as its Itô integral when `W` is `P`-a.s. continuous.
-/
theorem indicator_Ioc [IsFiniteMeasure P] {u v : ℝ≥0} {ξ : Ω → ℝ} (huv : u ≤ v)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hξ : StronglyMeasurable[ℱ u] ξ) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioc u v).indicator (fun _ ↦ ξ ω) t)
      (fun t ω ↦ ξ ω * (W (min v t) ω - W (min u t) ω)) := by
  let τ : ℕ → ℝ≥0 := fun i ↦ if i = 0 then u else v
  have hτ : MonotoneOn τ (Iic 1) := fun i _ j _ hij ↦ by
    dsimp [τ]; split_ifs <;> first | exact le_rfl | exact huv | omega
  convert simpleHolding (ℱ := ℱ) (P := P) (n := 1) (τ := τ) (a := fun _ ↦ ξ) hcont hτ
    (fun i hi ↦ by obtain rfl : i = 0 := (by omega); exact hξ) using 1 <;>
    (ext t ω; simp [Finance.simpleHolding_def, Finance.simpleGains_def, τ])

/-- On a finite measure `P`, a time-constant `ℱ 0`-measurable `ξ` has `t ↦ ξ * (W t - W 0)` as an
Itô integral when `W` is `P`-a.s. continuous, with no moment assumption on `ξ` or `W 0 = 0`. -/
theorem const_sub_initial [IsFiniteMeasure P] {ξ : Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω)) (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * (W t ω - W 0 ω)) where
  isStronglyPredictable :=
    ((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable
  ae_continuous := hcont.mono fun _ hω ↦ by fun_prop
  exists_seq_approx t := by
    obtain ⟨n, τ, a, hτ, ha, hb, henergy, hgains⟩ :=
      (indicator_Ioc (P := P) (zero_le : (0 : ℝ≥0) ≤ t) hcont hξ).exists_seq_approx t
    refine ⟨n, τ, a, hτ, ha, hb, fun ε hε ↦ (henergy ε hε).congr fun k ↦ by
      congr 1; ext ω; simp only [Set.mem_ofPred_eq]
      rw [lintegral_congr_ae ((Probability.ae_mem_Ioc_timeMeasure t).mono fun _ hs ↦ by
        rw [indicator_of_mem hs])],
      by simpa only [min_self, min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)] using hgains⟩

/-- On a finite measure `P`, when `W` is `P`-a.s. continuous with `W 0 =ᵐ[P] 0`, a time-constant
`ℱ 0`-measurable `ξ` has `t ↦ ξ * W t` as a continuous Itô integral. -/
theorem const [IsFiniteMeasure P] {ξ : Ω → ℝ}
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hW₀ : W 0 =ᵐ[P] 0) (hξ : StronglyMeasurable[ℱ 0] ξ) :
    IsItoIntegral ℱ P W (fun _ ω ↦ ξ ω) (fun t ω ↦ ξ ω * W t ω) :=
  (const_sub_initial hcont hξ).of_indist (hW₀.mono fun _ hω _ ↦ by simp [hω])

/-! ### Linearity and bounded initial multipliers -/

private theorem tendsto_measure_lintegral_bdd_mul_le
    {f g : ℕ → ℝ≥0 → Ω → ℝ} {t : ℝ≥0} {ξ : Ω → ℝ} {C : ℝ} (hC : ∀ ω, ‖ξ ω‖ ≤ C)
    (henergy : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖g k s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0))
    (hle : ∀ k s ω, ‖f k s ω‖ₑ ≤ ‖ξ ω‖ₑ * ‖g k s ω‖ₑ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ P {ω | ε ≤ ∫⁻ s, ‖f k s ω‖ₑ ^ 2 ∂Probability.timeMeasure t}) atTop (𝓝 0) := by
  let M : ℝ≥0 := ⟨max C 1, by positivity⟩
  have hM0 : (M : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (NNReal.coe_pos.mp (lt_of_lt_of_le zero_lt_one (le_max_right _ _))).ne'
  have hξM (ω : Ω) : ‖ξ ω‖ₑ ≤ M := by
    rw [eNorm_le_coe, ← NNReal.coe_le_coe, coe_nnNorm]; exact (hC ω).trans (le_max_left _ _)
  refine MeasureTheory.tendsto_measure_ge_of_ne_top (fun ε hε _ ↦ ?_) hε
  have hM2_pos : (0 : ℝ≥0∞) < (M : ℝ≥0∞) ^ 2 := sq (M : ℝ≥0∞) ▸ ENNReal.mul_pos hM0 hM0
  have hM2_top : (M : ℝ≥0∞) ^ 2 ≠ ∞ := ENNReal.pow_ne_top ENNReal.coe_ne_top
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (henergy (ε / (M : ℝ≥0∞) ^ 2) (ENNReal.div_pos hε.ne' hM2_top))
    (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ ?_
  rw [Set.mem_ofPred_eq, ENNReal.div_le_iff_le_mul (Or.inl hM2_pos.ne') (Or.inl hM2_top), mul_comm]
  exact hω.trans <| (lintegral_mono fun s ↦ ((pow_le_pow_left' (hle k s ω) 2).trans_eq
    (mul_pow _ _ 2)).trans (mul_le_mul_of_nonneg_right (pow_le_pow_left' (hξM ω) 2)
      zero_le)).trans_eq (lintegral_const_mul' _ _ hM2_top)

private theorem exists_bdd_mul {ξ a : Ω → ℝ} {Cξ : ℝ} (hCξ : ∀ ω, ‖ξ ω‖ ≤ Cξ)
    (ha : ∃ C : ℝ, ∀ ω, ‖a ω‖ ≤ C) : ∃ C : ℝ, ∀ ω, ‖ξ ω * a ω‖ ≤ C := by
  obtain ⟨C, hC⟩ := ha
  exact ⟨max Cξ 1 * max C 0, fun ω ↦ by
    simpa only [norm_mul] using mul_le_mul ((hCξ ω).trans (le_max_left _ _))
      ((hC ω).trans (le_max_left _ _)) (norm_nonneg _) (by positivity)⟩

/-- Multiplying an integrand by a bounded `ℱ 0`-measurable random variable `ξ` multiplies its Itô
integral by `ξ`, on any measure `P` and for any integrator `W`. -/
theorem bdd_mul (hI : IsItoIntegral ℱ P W H I) {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ 0] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ ξ ω * H t ω) (fun t ω ↦ ξ ω * I t ω) := by
  obtain ⟨Cξ, hCξ⟩ := hb
  refine ⟨(((locallyBrownianIntegrable_const_iff (P := P)).2 hξ).isStronglyPredictable).mul
    hI.isStronglyPredictable, hI.ae_continuous.mono fun _ hω ↦ continuous_const.mul hω,
    fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hba, henergy, hgains⟩ := hI.exists_seq_approx t
  refine ⟨n, τ, fun k i ω ↦ ξ ω * a k i ω, hτ,
    fun k i hi ↦ (hξ.mono (ℱ.mono bot_le)).mul (ha k i hi),
    fun k i hi ↦ exists_bdd_mul hCξ (hba k i hi),
    fun _ hε ↦ tendsto_measure_lintegral_bdd_mul_le hCξ henergy (fun k s ω ↦ ?_) hε,
    (hgains.bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ by
      simp [Finance.simpleGains_def, smul_eq_mul, mul_sum, mul_assoc]) .rfl⟩
  have hhold : Finance.simpleHolding (τ k) (n k) (fun i ω ↦ ξ ω * a k i ω) s ω =
      ξ ω * Finance.simpleHolding (τ k) (n k) (a k) s ω := by
    simp only [Finance.simpleHolding_def, mul_sum]
    exact sum_congr rfl fun i _ ↦ by by_cases hs : s ∈ Ioc (τ k i) (τ k (i + 1)) <;> simp [hs]
  rw [hhold, ← mul_sub, eNorm_mul]

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
  ae_continuous := hI.ae_continuous.mp <| hJ.ae_continuous.mono fun _ hJω hIω ↦ hIω.add hJω
  exists_seq_approx t := by
    obtain ⟨n₁, τ₁, a₁, hτ₁, ha₁, hb₁, he₁, hg₁⟩ := hI.exists_seq_approx t
    obtain ⟨n₂, τ₂, a₂, hτ₂, ha₂, hb₂, he₂, hg₂⟩ := hJ.exists_seq_approx t
    choose n τ b _ hτ hbm hbb hhold hgains using fun k ↦
      Finance.exists_simpleHolding_simpleGains_add ℱ (hτ₁ k) (hτ₂ k) (ha₁ k) (ha₂ k)
    refine ⟨n, τ, b, fun k ↦ (hτ k).monotoneOn, hbm, fun k j hj ↦ ?_, fun ε hε ↦ ?_,
      (hg₁.add hg₂).congr (fun k ↦ .of_forall fun ω ↦ (hgains k W t ω).symm) .rfl⟩
    · choose C₁ hC₁ using fun (i : Fin (n₁ k)) ↦ hb₁ k i.1 i.2
      choose C₂ hC₂ using fun (i : Fin (n₂ k)) ↦ hb₂ k i.1 i.2
      refine ⟨(∑ i : Fin (n₁ k), C₁ i) + ∑ i : Fin (n₂ k), C₂ i, fun ω ↦
        (hbb k j hj ω).trans (add_le_add ?_ ?_)⟩ <;>
        (rw [← Fin.sum_univ_eq_sum_range]; exact sum_le_sum fun i _ ↦ by solve_by_elim)
    · simp_rw [hhold, Pi.add_apply, add_sub_add_comm]
      exact MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
        (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (ha₁ k)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
            (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
        he₁ he₂ hε

/-- Subtracting two integrands subtracts their Itô integrals. -/
theorem sub (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J) :
    IsItoIntegral ℱ P W (H - K) (I - J) := by
  simpa only [sub_eq_add_neg] using hI.add hJ.neg

/-! ### Gains convergence, uniqueness, and post-`u` multipliers -/

/-- If left-measurable simple strategies approximate `H` in pathwise square energy in probability
on `(0, t]`, their elementary gains against a filtered pre-Brownian motion `W` converge in
probability to `I t`, without height bounds or path continuity of `W`. -/
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
  have he_sub : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun k ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (σ k) (m k) (b k) s ω‖ₑ ^ 2
        ∂Probability.timeMeasure t}) atTop (𝓝 0) := fun ε hε ↦ by
    simpa only [sub_add_sub_cancel, ← hhold] using
      MeasureTheory.tendsto_measure_lintegral_enorm_add_sq
        (f := fun k s ω ↦ Finance.simpleHolding (τ k) (n k) (a k) s ω - H s ω)
        (g := fun k s ω ↦ H s ω - Finance.simpleHolding (τ₁ k) (n₁ k) (a₁ k) s ω)
        (.of_forall fun k ω ↦ ((((Finance.isStronglyPredictable_simpleHolding (ha k)).sub
          hI.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.comp
            (measurable_id.prodMk measurable_const) |>.eNorm.pow_const 2).aemeasurable)
        henergy (by simpa only [eNorm_sub_rev] using he₁) hε
  have hdiff := (hW.tendstoInMeasure_simpleGains_zero_of_lintegral
    (fun k ↦ (hσ k).monotoneOn) hbm he_sub).congr_left fun k ↦ .of_forall (hgains_sub k W t)
  exact (hdiff.add hg₁).congr (fun _ ↦ .of_forall fun _ ↦ sub_add_cancel _ _)
    (.of_forall fun _ ↦ zero_add _)

/-- If left-measurable simple strategies approximate `H` in pathwise square energy in probability
on `(0, t]` and their gains against a filtered pre-Brownian motion `W` converge in probability to
`Y`, then `I t =ᵐ[P] Y`. -/
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

/-- Two Itô integrals of the same integrand against a filtered pre-Brownian motion agree a.s. at
each horizon, without assuming path continuity of `W`. -/
theorem ae_eq_eval (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) (t : ℝ≥0) :
    I t =ᵐ[P] J t := by
  obtain ⟨n, τ, a, hτ, ha, -, he, hg⟩ := hJ.exists_seq_approx t
  exact hI.ae_eq_of_approx hW hτ ha he hg

/-- **Uniqueness of the continuous Brownian Itô integral**: any two continuous Itô integrals of the
same integrand against a filtered pre-Brownian motion are `P`-indistinguishable. -/
theorem indist (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W H J) :
    I ≡ᵐ[P] J :=
  ProbabilityTheory.indist_of_ae_continuous hI.ae_continuous hJ.ae_continuous (hI.ae_eq_eval hW hJ)

/-- Any Itô integral of `0` against a filtered pre-Brownian motion vanishes a.s. at each horizon. -/
theorem ae_eq_zero_of_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) (t : ℝ≥0) : I t =ᵐ[P] 0 :=
  hI.ae_eq_eval hW zero t

/-- Any Itô integral of `0` against a filtered pre-Brownian motion is indistinguishable from `0`. -/
theorem indist_zero_of_zero (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W 0 I) : I ≡ᵐ[P] 0 :=
  hI.indist hW zero

/-- **Integrand congruence**: predictable integrands agreeing `(dt × P)`-a.e. on every finite
horizon have `P`-indistinguishable continuous Itô integrals against `W`. -/
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
  have hξ_pred : IsStronglyPredictable ℱ (fun t ω ↦ (Ioi u).indicator (fun _ ↦ ξ ω) t) :=
    Measurable.stronglyMeasurable fun A hA ↦ by
      have hset : (Function.uncurry fun t ω ↦ (Ioi u).indicator (fun _ ↦ ξ ω) t) ⁻¹' A =
          if (0 : ℝ) ∈ A then (Ioi u ×ˢ univ)ᶜ ∪ Ioi u ×ˢ (ξ ⁻¹' A) else Ioi u ×ˢ (ξ ⁻¹' A) := by
        ext ⟨s, ω⟩; by_cases hs : u < s <;> by_cases h0 : (0 : ℝ) ∈ A <;> simp [hs, h0]
      rw [hset]; have hξA := measurableSet_predictable_Ioi_prod (hξ.measurable hA)
      split_ifs
      · exact (measurableSet_predictable_Ioi_prod .univ).compl.union hξA
      · exact hξA
  convert hξ_pred.mul hH using 1; ext t ω; by_cases ht : u < t <;> simp [ht]

/-- Multiplying an integrand after time `u` by a bounded `ℱ u`-measurable `ξ` yields the post-`u`
Itô integral `t ↦ ξ * (I t - I (min u t))`, without assuming path continuity of `W`. -/
theorem indicator_Ioi_bdd_mul (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {u : ℝ≥0} {ξ : Ω → ℝ}
    (hξ : StronglyMeasurable[ℱ u] ξ) (hb : ∃ C : ℝ, ∀ ω, ‖ξ ω‖ ≤ C) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (fun s ↦ ξ ω * H s ω) t)
      (fun t ω ↦ ξ ω * (I t ω - I (min u t) ω)) := by
  obtain ⟨Cξ, hCξ⟩ := hb
  refine ⟨isStronglyPredictable_indicator_Ioi_mul hI.isStronglyPredictable hξ,
    hI.ae_continuous.mono fun _ hω ↦ by fun_prop, fun t ↦ ?_⟩
  obtain ⟨n, τ, a, hτ, ha, hba, henergy, hgains⟩ := hI.exists_seq_approx t
  have hgains_min := hI.tendstoInMeasure_simpleGains (t := min u t) hW hτ ha fun ε hε ↦
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (henergy ε hε)
      (fun _ ↦ zero_le) fun k ↦ measure_mono fun ω hω ↦ by
        simp only [Set.mem_ofPred_eq] at hω ⊢
        refine hω.trans ?_
        rw [← Probability.timeMeasure_restrict t u]
        exact lintegral_mono' Measure.restrict_le_self le_rfl
  refine ⟨n, fun k i ↦ max (τ k i) u, fun k i ω ↦ ξ ω * a k i ω,
    fun k _ hi _ hj hij ↦ max_le_max_right u (hτ k hi hj hij),
    fun k i hi ↦ (hξ.mono (ℱ.mono (le_max_right _ _))).mul
      ((ha k i hi).mono (ℱ.mono (le_max_left _ _))),
    fun k i hi ↦ exists_bdd_mul hCξ (hba k i hi),
    fun _ hε ↦ tendsto_measure_lintegral_bdd_mul_le hCξ henergy (fun k s ω ↦ by
      rw [Finance.simpleHolding_max_eq u ξ s ω]
      by_cases hs : u < s
      · simp [Set.mem_Ioi.mpr hs, ← mul_sub, eNorm_mul]
      · simp [Set.mem_Ioi, hs]) hε,
    ((hgains.sub hgains_min).bdd_smul hCξ).congr (fun k ↦ .of_forall fun ω ↦ by
      simpa only [smul_eq_mul, Pi.sub_apply] using (Finance.simpleGains_max_eq u ξ W t ω).symm)
      .rfl⟩

/-- Restricting an integrand to `(u, ∞)` yields the post-`u` Itô integral
`t ↦ I t - I (min u t)`, without assuming path continuity of `W`. -/
theorem indicator_Ioi (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (u : ℝ≥0) :
    IsItoIntegral ℱ P W (fun t ω ↦ (Ioi u).indicator (H · ω) t)
      (fun t ω ↦ I t ω - I (min u t) ω) := by
  simpa only [one_mul] using hI.indicator_Ioi_bdd_mul hW (u := u) (ξ := fun _ ↦ 1)
    stronglyMeasurable_const ⟨1, fun _ ↦ by norm_num⟩

end IsItoIntegral

end TauCeti
