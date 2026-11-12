/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Integrable
public import TauCeti.Probability.Finance.SimpleStrategy.Refinement
public import TauCeti.Probability.Process.ElementaryDensity
public import TauCeti.Probability.Process.Predictable.Measure
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Approximation by bounded finite-grid holdings

Every predictable square-integrable real process can be approximated in square-energy norm
by a simple holding on one strictly increasing deterministic grid. The heights are bounded
and measurable at the left endpoints, not the right endpoints. This turns density of
predictable rectangle indicators in the native L² space into actual elementary integrands
on which increment sums can be evaluated, as needed for completion of stochastic integrals.

The first theorem allows any measure on the predictable sigma-algebra finite on bounded
predictable rectangles, with no mass at time zero. The second gives the finite-horizon
Lebesgue-time × sample-measure form.
Finally, one sequence of finite-grid holdings approximates a Brownian-integrable process
on every finite horizon.
No Brownian motion, usual filtration conditions or path regularity is assumed. The grids
start at zero; their last date need not equal the observation horizon. Approximation is
in energy norm, not pointwise or uniform in time.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)

private theorem exists_simpleHolding_ae_eq_of_mem_span
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    (hfin : ∀ s t A, MeasurableSet[ℱ s] A → μ (Ioc s t ×ˢ A) ≠ ∞)
    {g : Lp ℝ 2 μ}
    (hg : g ∈ Submodule.span ℝ {v : Lp ℝ 2 μ | ∃ (s t : ℝ≥0) (A : Set Ω)
      (hA : MeasurableSet[ℱ s] A),
      v = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (hfin s t A hA) 1}) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (C : ℝ),
      τ 0 = 0 ∧ StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) ∧
      (fun p ↦ simpleHolding τ n a p.1 p.2) =ᵐ[μ] g := by
  classical
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  obtain ⟨k, c, v, hv⟩ := Submodule.mem_span_set'.mp hg
  -- Represent the L² linear combination by one common deterministic grid.
  have hrect (i : Fin k) := (v i).property
  choose l u A hA heq using hrect
  let b (i : Fin k) : Ω → ℝ := fun ω ↦ c i * (A i).indicator (fun _ ↦ 1) ω
  have hb (i : Fin k) : StronglyMeasurable[ℱ (l i)] (b i) :=
    (stronglyMeasurable_const.indicator (hA i)).const_mul (c i)
  obtain ⟨n, τ, a, hτ₀, hτ, ha, hhold⟩ :=
    exists_simpleHolding_eq_sum_indicator_Ioc ℱ Finset.univ l u b (fun i _ ↦ hb i)
  have hbound (t : ℝ≥0) (ω : Ω) : ‖simpleHolding τ n a t ω‖ ≤ ∑ i, ‖c i‖ := by
    rw [hhold]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
    by_cases ht : t ∈ Ioc (l i) (u i) <;> by_cases hω : ω ∈ A i <;>
      simp [b, ht, hω]
  refine ⟨n, τ, a, ∑ i, ‖c i‖, hτ₀, hτ, ha, ?_, ?_⟩
  · intro j hj ω
    have hmem : τ (j + 1) ∈ Ioc (τ j) (τ (j + 1)) :=
      ⟨hτ hj.le (Nat.succ_le_of_lt hj) (Nat.lt_succ_self j), le_rfl⟩
    simpa only [simpleHolding_of_mem_Ioc hτ.monotoneOn hj hmem] using
      hbound (τ (j + 1)) ω
  -- Compare representatives only almost everywhere; L² coercions are not pointwise sums.
  · have hcoe := Lp.coeFn_finsetSum (s := Finset.univ) (fun i : Fin k ↦ c i • (v i).val)
    have hterms : ∀ i : Fin k, (c i • (v i).val : Lp ℝ 2 μ) =ᵐ[μ]
        fun p ↦ (Ioc (l i) (u i)).indicator (fun _ ↦ b i p.2) p.1 := by
      intro i
      rw [heq i]
      filter_upwards [Lp.coeFn_smul (c i)
        (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod (l i) (u i) (hA i))
          (hfin (l i) (u i) (A i) (hA i)) (1 : ℝ)),
        indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
          (hs := measurableSet_predictable_Ioc_prod (l i) (u i) (hA i))
          (hμs := hfin (l i) (u i) (A i) (hA i)) (c := (1 : ℝ))] with p hp hq
      rw [hp]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hq]
      by_cases ht : p.1 ∈ Ioc (l i) (u i) <;> by_cases hω : p.2 ∈ A i <;>
        simp [b, ht, hω]
    have hsum := hcoe.trans (eventuallyEq_sum fun i _ ↦ hterms i)
    rw [hv] at hsum
    filter_upwards [hsum] with p hp
    exact (hhold p.1 p.2).trans (by simpa only [Finset.sum_apply] using hp.symm)

/-- Predictable L² functions admit arbitrarily accurate energy-norm approximation by
one finite-grid holding with bounded left-measurable heights. The predictable measure
need only be finite on bounded predictable rectangles, with a null initial-time slice. -/
theorem exists_simpleHolding_eLpNorm_sub_lt
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    (hfin : ∀ s t A, MeasurableSet[ℱ s] A → μ (Ioc s t ×ˢ A) ≠ ∞)
    (hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    {H : ℝ≥0 → Ω → ℝ} (hH₂ : MemLp (Function.uncurry H) 2 μ) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (C : ℝ),
      τ 0 = 0 ∧ StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) ∧
      eLpNorm (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2 μ < ε := by
  classical
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let R : Set (Lp ℝ 2 μ) := {v | ∃ (s t : ℝ≥0) (A : Set Ω)
    (hA : MeasurableSet[ℱ s] A),
    v = indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
      (hfin s t A hA) 1}
  have hdense : (Submodule.span ℝ R).topologicalClosure = ⊤ :=
    ℱ.topologicalClosure_span_indicatorConstLp_Ioc_prod_eq_top μ hfin hzero
  have hmem : hH₂.toLp (Function.uncurry H) ∈ closure (Submodule.span ℝ R : Set (Lp ℝ 2 μ)) := by
    rw [← Submodule.topologicalClosure_coe, hdense]
    trivial
  obtain ⟨g, hg, hdist⟩ := EMetric.mem_closure_iff.mp hmem ε hε
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hbound, heq⟩ :=
    exists_simpleHolding_ae_eq_of_mem_span ℱ μ hfin hg
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hbound, ?_⟩
  have hnorm : eLpNorm (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2 μ =
      edist g (hH₂.toLp (Function.uncurry H)) := by
    rw [Lp.edist_def]
    exact eLpNorm_congr_ae (heq.sub hH₂.coeFn_toLp.symm)
  rw [hnorm, edist_comm]
  exact hdist

/-- On each finite horizon, a predictable integrand with finite expected square energy
can be approximated by bounded finite-grid holdings in ambient time-product L² norm.
The measure on the sample space need only be finite. -/
theorem exists_simpleHolding_eLpNorm_sub_lt_timeMeasure
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    (hH₂ : MemLp (Function.uncurry H) 2 ((Probability.timeMeasure T).prod P))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ) (C : ℝ),
      τ 0 = 0 ∧ StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ C) ∧
      eLpNorm (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P) < ε := by
  have hH₂' := (ℱ.memLp_predictableMeasure_iff P hH T 2).mpr hH₂
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hb, herr⟩ :=
    exists_simpleHolding_eLpNorm_sub_lt ℱ (ℱ.predictableMeasure P T)
      (fun _ _ _ _ ↦ measure_ne_top _ _)
      (ℱ.predictableMeasure_singleton_zero_prod P T MeasurableSet.univ) hH₂' hε
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_⟩
  have hp := isStronglyPredictable_simpleHolding (ℱ := ℱ) ha
  have hs : StronglyMeasurable[ℱ.predictable]
      (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) := by
    simpa only [Pi.sub_def, Function.uncurry_def] using hp.sub hH
  rwa [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hs] at herr

end MeasureTheory.Filtration

namespace TauCeti.BrownianIntegrable

/-- One sequence of bounded, left-measurable finite-grid holdings approximates an
expected-square-integrable predictable process in L² on every finite horizon. The same
sequence works for all horizons; no compatibility or nesting of its grids is required. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}
    (hH : BrownianIntegrable ℱ P H) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ m, τ m 0 = 0) ∧ (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      ∀ T : ℝ≥0, Tendsto (fun m ↦ eLpNorm
        (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  have hex (m : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P m
    hH.isStronglyPredictable
    (by simpa only [NNReal.comap_volume_restrict_Ioc, Probability.timeMeasure_def]
        using hH.memLp m)
    (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top m))
  choose n τ a C hτ₀ hτ ha hb herr using hex
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, fun T ↦ ?_⟩
  have hbound : ∀ᶠ m : ℕ in atTop, eLpNorm
      (fun p ↦ Finance.simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
        ((Probability.timeMeasure T).prod P) ≤ (m : ℝ≥0∞)⁻¹ := by
    obtain ⟨N, hN⟩ := exists_nat_ge T
    filter_upwards [eventually_ge_atTop N] with m hm
    have hTm : T ≤ (m : ℝ≥0) := hN.trans (by exact_mod_cast hm)
    have hmeasure : (Probability.timeMeasure T).prod P ≤
        (Probability.timeMeasure m).prod P := by
      apply Measure.prod_mono _ le_rfl
      rw [Probability.timeMeasure_def, Probability.timeMeasure_def]
      exact Measure.restrict_mono_set _ (Ioc_subset_Ioc_right hTm)
    exact (eLpNorm_mono_measure _ hmeasure).trans (herr m).le
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (Eventually.of_forall fun _ ↦ bot_le) hbound

end TauCeti.BrownianIntegrable
