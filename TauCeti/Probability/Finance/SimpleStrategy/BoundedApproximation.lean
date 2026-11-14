/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Approximation
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Bound-preserving predictable grid approximation

A predictable square-integrable process bounded almost everywhere by `K` admits finite-grid
approximations whose left-endpoint-measurable heights are all bounded by the same `K`.
The heights satisfy this bound everywhere, even if the original bound holds only almost
everywhere. For `K ≥ 0` the holding processes are therefore bounded by `K` at every time.
A negative bound forces the zero measure and is handled by an empty grid.
The grid may depend on the approximation accuracy.

This strengthens energy density by controlling the heights uniformly across approximations.
For exponential Brownian likelihoods this is essential: their second-moment estimate depends
exponentially on the squared height bound, so a separate bound for each approximant does not
supply uniform integrability. No Brownian motion or usual filtration conditions are needed
for the approximation itself.

The construction clips the heights of the existing finite-grid energy approximations using
`Set.projIcc`. Its native nonexpansiveness ensures that clipping cannot increase the error
against a target already lying in the interval. No stochastic integral or density measure is
constructed here.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §§3.2 and 3.5.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti.Finance
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Filtration

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)

/-- Finite-grid L² density preserving a prescribed almost-everywhere bound on the target.
The heights satisfy the bound everywhere and are measurable at the left endpoints.
The measure need only be finite on predictable rectangles and have no mass at time zero. -/
theorem exists_simpleHolding_eLpNorm_sub_lt_of_bound
    (μ : @Measure (ℝ≥0 × Ω) ℱ.predictable)
    (hfin : ∀ s t A, MeasurableSet[ℱ s] A → μ (Ioc s t ×ˢ A) ≠ ∞)
    (hzero : μ ({0} ×ˢ (univ : Set Ω)) = 0)
    {H : ℝ≥0 → Ω → ℝ} (hH₂ : MemLp (Function.uncurry H) 2 μ)
    {K : ℝ} (hbound : ∀ᵐ p ∂μ, ‖H p.1 p.2‖ ≤ K)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ),
      τ 0 = 0 ∧ StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ K) ∧
      eLpNorm (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2 μ < ε := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  by_cases hK : 0 ≤ K
  swap
  · -- A negative bound can occur only for the zero measure; use the empty grid.
    have hμ : μ = 0 := by
      by_contra hn
      have : NeZero μ := ⟨hn⟩
      obtain ⟨p, hp⟩ := hbound.exists
      exact hK ((norm_nonneg _).trans hp)
    refine ⟨0, fun _ ↦ 0, 0, rfl, ?_, by simp, by simp, ?_⟩
    · intro i hi j hj hij
      simp only [mem_Iic, nonpos_iff_eq_zero] at hi hj
      omega
    · simpa [hμ] using hε
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, -, herr⟩ :=
    ℱ.exists_simpleHolding_eLpNorm_sub_lt μ hfin hzero hH₂ hε
  let clip (x : ℝ) : ℝ := Set.projIcc (-K) K (neg_le_self hK) x
  have hclip : Continuous clip := continuous_subtype_val.comp continuous_projIcc
  have hclip₀ : clip 0 = 0 := by simp [clip, Set.projIcc, hK, neg_nonpos.mpr hK]
  refine ⟨n, τ, fun j ω ↦ clip (a j ω), hτ₀, hτ,
    fun j hj ↦ hclip.comp_stronglyMeasurable (ha j hj), ?_, ?_⟩
  · intro j _ ω
    exact Real.norm_eq_abs _ ▸ abs_le.mpr (Set.projIcc _ _ _ _).property
  · have hm : AEStronglyMeasurable (fun p ↦
        simpleHolding τ n (fun j ω ↦ clip (a j ω)) p.1 p.2 - H p.1 p.2) μ :=
      (isStronglyPredictable_simpleHolding (ℱ := ℱ)
        (fun j hj ↦ hclip.comp_stronglyMeasurable (ha j hj))).aestronglyMeasurable.sub
          hH₂.aestronglyMeasurable
    refine (eLpNorm_mono_ae hm ?_).trans_lt herr
    filter_upwards [hbound] with p hp
    rw [simpleHolding_comp hclip₀ hτ.monotoneOn]
    have hp' : H p.1 p.2 ∈ Icc (-K) K := abs_le.mp (by simpa using hp)
    have hdist := (LipschitzWith.projIcc (neg_le_self hK)).dist_le_mul
      (simpleHolding τ n a p.1 p.2) (H p.1 p.2)
    simpa only [Set.projIcc_of_mem _ hp', Subtype.dist_eq, Real.dist_eq, NNReal.coe_one,
      one_mul, Real.norm_eq_abs, clip] using hdist

/-- Finite-horizon time-product form of bound-preserving grid approximation.
In particular a bounded predictable Brownian drift has elementary approximations with a
common height bound, rather than a bound growing with the accuracy. -/
theorem exists_simpleHolding_eLpNorm_sub_lt_timeMeasure_of_bound
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    {K : ℝ} (hbound : ∀ᵐ p ∂(TauCeti.Probability.timeMeasure T).prod P, ‖H p.1 p.2‖ ≤ K)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (τ : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ),
      τ 0 = 0 ∧ StrictMonoOn τ (Iic n) ∧
      (∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j)) ∧
      (∀ j < n, ∀ ω, ‖a j ω‖ ≤ K) ∧
      eLpNorm (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) 2
        ((TauCeti.Probability.timeMeasure T).prod P) < ε := by
  let ν := (TauCeti.Probability.timeMeasure T).prod P
  have hm : AEStronglyMeasurable (Function.uncurry H) ν :=
    (hH.mono ℱ.predictable_le_prod).aestronglyMeasurable
  have hH₂ : MemLp (Function.uncurry H) 2 ν := (memLp_const K).mono' hm hbound
  have hb : ∀ᵐ p ∂ℱ.predictableMeasure P T, ‖H p.1 p.2‖ ≤ K := by
    have hs : MeasurableSet[ℱ.predictable] {p : ℝ≥0 × Ω | ¬ ‖H p.1 p.2‖ ≤ K} :=
      (measurableSet_le hH.norm.measurable measurable_const).compl
    rw [ℱ.predictableMeasure_def, ae_iff, trim_measurableSet_eq ℱ.predictable_le_prod hs]
    exact hbound
  obtain ⟨n, τ, a, hτ₀, hτ, ha, hbound', herr⟩ :=
    ℱ.exists_simpleHolding_eLpNorm_sub_lt_of_bound (ℱ.predictableMeasure P T)
      (fun _ _ _ _ ↦ measure_ne_top _ _)
      (ℱ.predictableMeasure_singleton_zero_prod P T MeasurableSet.univ)
      ((ℱ.memLp_predictableMeasure_iff P hH T 2).mpr hH₂) hb hε
  refine ⟨n, τ, a, hτ₀, hτ, ha, hbound', ?_⟩
  have hs : StronglyMeasurable[ℱ.predictable]
      (fun p ↦ simpleHolding τ n a p.1 p.2 - H p.1 p.2) :=
    (isStronglyPredictable_simpleHolding (ℱ := ℱ) ha).sub hH
  rwa [ℱ.predictableMeasure_def, eLpNorm_trim ℱ.predictable_le_prod hs] at herr

/-- A bounded predictable process has a sequence of finite-grid energy approximations on a
fixed finite horizon with the same bound on every height of every approximant. No moment
hypothesis on the process is needed beyond its deterministic bound. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_of_bound
    (P : Measure Ω) [IsFiniteMeasure P] (T : ℝ≥0)
    {H : ℝ≥0 → Ω → ℝ} (hH : IsStronglyPredictable ℱ H)
    {K : ℝ} (hbound : ∀ᵐ p ∂(TauCeti.Probability.timeMeasure T).prod P, ‖H p.1 p.2‖ ≤ K) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ),
      (∀ m, τ m 0 = 0) ∧ (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ K) ∧
      Tendsto (fun m ↦ eLpNorm
        (fun p ↦ simpleHolding (τ m) (n m) (a m) p.1 p.2 - H p.1 p.2) 2
          ((TauCeti.Probability.timeMeasure T).prod P)) atTop (𝓝 0) := by
  have hex (m : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure_of_bound P T hH
    hbound (ε := (m : ℝ≥0∞)⁻¹) (ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top m))
  choose n τ a hτ₀ hτ ha hb herr using hex
  refine ⟨n, τ, a, hτ₀, hτ, ha, hb, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ ↦ bot_le) (fun m ↦ (herr m).le)

end MeasureTheory.Filtration
