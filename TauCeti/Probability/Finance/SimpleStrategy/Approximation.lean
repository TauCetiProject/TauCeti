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
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.Truncation
import TauCeti.MeasureTheory.Integral.Lebesgue.Subsequence

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
One sequence of finite-grid holdings approximates a Brownian-integrable process
on every finite horizon. On a fixed finite horizon, a predictable real process with only
almost surely finite pathwise square energy also admits bounded finite-grid approximations
whose square errors converge to zero almost surely. No expected-energy bound is required
for this pathwise result; its sequence and exceptional sample set may depend on the horizon.
The errors use nonnegative lower integrals, so infinite energies are not replaced by
default-valued Bochner integrals. Neither nesting nor a common height bound is asserted.

The pathwise construction uses value truncations, the expected-energy density theorem
`MeasureTheory.Filtration.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure`, and summably
small expected approximation errors. Value truncation requires no stopping times.
No Brownian motion, usual filtration conditions or path regularity is assumed. The grids
start at zero; their last date need not equal the observation horizon. Approximation is
in energy, not pointwise or uniform in time. These are integrand approximation theorems,
not constructions of stochastic integrals.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2 (in particular §3.2.D for pathwise-energy approximation).
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

namespace MeasureTheory.IsStronglyPredictable

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} [IsFiniteMeasure P] {H : ℝ≥0 → Ω → ℝ}

/-- A predictable process with finite pathwise square energy on a finite horizon has bounded
finite-grid approximations converging in square energy on almost every sample path.
The original process need not have a finite expected square energy. -/
theorem exists_seq_simpleHolding_ae_tendsto_lintegral_eNorm_sub_sq
    (hH : IsStronglyPredictable ℱ H) (T : ℝ≥0)
    (hH₂ : ∀ᵐ ω ∂P, MemLp (fun t ↦ H t ω) 2 (TauCeti.Probability.timeMeasure T)) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ m, τ m 0 = 0) ∧ (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      ∀ᵐ ω ∂P, Tendsto (fun m ↦ ∫⁻ t,
        ‖simpleHolding (τ m) (n m) (a m) t ω - H t ω‖ₑ ^ 2
          ∂TauCeti.Probability.timeMeasure T) atTop (𝓝 0) := by
  classical
  let ν := TauCeti.Probability.timeMeasure T
  let K (m : ℕ) (t : ℝ≥0) (ω : Ω) := if ‖H t ω‖ ≤ m then H t ω else 0
  have hK (m : ℕ) : IsStronglyPredictable ℱ (K m) :=
    hH.ite (measurableSet_le hH.norm.measurable measurable_const) stronglyMeasurable_const
  have hKbound (m : ℕ) (t : ℝ≥0) (ω : Ω) : ‖K m t ω‖ ≤ m := by
    simp only [K]
    split_ifs with h <;> simp_all
  have hK₂ (m : ℕ) : MemLp (Function.uncurry (K m)) 2 (ν.prod P) := by
    refine (memLp_const (m : ℝ)).mono'
      ((hK m).mono ℱ.predictable_le_prod).aestronglyMeasurable ?_
    exact Eventually.of_forall fun p ↦ hKbound m p.1 p.2
  -- Approximate each bounded truncation with a summable sequence of expected errors.
  have hex (m : ℕ) := ℱ.exists_simpleHolding_eLpNorm_sub_lt_timeMeasure P T (hK m) (hK₂ m)
    (ε := ((1 / 2 : ℝ≥0) ^ m : ℝ≥0∞)) (by positivity)
  choose n τ a C hτ₀ hτ ha hb herr using hex
  let L (m : ℕ) := simpleHolding (τ m) (n m) (a m)
  let E (m : ℕ) (ω : Ω) := ∫⁻ t, ‖L m t ω - K m t ω‖ₑ ^ 2 ∂ν
  have hpred (m : ℕ) : IsStronglyPredictable ℱ (fun t ω ↦ L m t ω - K m t ω) :=
    (isStronglyPredictable_simpleHolding (ha m)).sub (hK m)
  have hmeas (m : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ ‖L m p.1 p.2 - K m p.1 p.2‖ₑ ^ 2) :=
    ((hpred m).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
  have hE (m : ℕ) : Measurable (E m) := (hmeas m).lintegral_prod_left'
  have hmean (m : ℕ) : ∫⁻ ω, E m ω ∂P ≤ (((1 / 2 : ℝ≥0) ^ 2) ^ m : ℝ≥0∞) := by
    rw [← lintegral_lintegral_swap (hmeas m).aemeasurable]
    rw [← lintegral_prod _ (hmeas m).aemeasurable]
    have hpow := eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
      ((hpred m).mono ℱ.predictable_le_prod).aestronglyMeasurable (μ := ν.prod P)
    simp only [NNReal.coe_ofNat, ENNReal.rpow_two, Function.uncurry_def,
      ENNReal.coe_ofNat] at hpow
    rw [← hpow]
    simpa only [← ENNReal.coe_pow, ← pow_mul, Nat.mul_comm] using
      pow_le_pow_left' (herr m).le 2
  have hsum : (∑' m, (((1 / 2 : ℝ≥0) ^ 2) ^ m : ℝ≥0∞)) ≠ ∞ :=
    ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_geometric (by norm_num))
  have hELim : ∀ᵐ ω ∂P, Tendsto (fun m ↦ E m ω) atTop (𝓝 0) :=
    ae_tendsto_zero_of_tsum_lintegral_ne_top (fun m ↦ (hE m).aemeasurable)
      (ne_top_of_le_ne_top hsum (tsum_le_tsum hmean))
  -- On each finite-energy path the value-truncation error vanishes by dominated convergence.
  have htrunc : ∀ᵐ ω ∂P, Tendsto
      (fun m ↦ ∫⁻ t, ‖K m t ω - H t ω‖ₑ ^ 2 ∂ν) atTop (𝓝 0) := by
    filter_upwards [hH₂] with ω hω
    simpa only [Function.comp_def, K, ENNReal.toReal_ofNat, ENNReal.rpow_two] using
      (hω.tendsto_lintegral_eNorm_ite_sub_rpow (by norm_num) (by norm_num)).comp
        tendsto_natCast_atTop_atTop
  -- The square error is at most twice each of the two square errors.
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hb, ?_⟩
  filter_upwards [hELim, htrunc] with ω hEω hKω
  have hbound (m : ℕ) : (∫⁻ t, ‖L m t ω - H t ω‖ₑ ^ 2 ∂ν) ≤
      2 * E m ω + 2 * ∫⁻ t, ‖K m t ω - H t ω‖ₑ ^ 2 ∂ν := by
    calc
      _ ≤ ∫⁻ t, 2 * ‖L m t ω - K m t ω‖ₑ ^ 2 +
          2 * ‖K m t ω - H t ω‖ₑ ^ 2 ∂ν := by
        apply lintegral_mono
        intro t
        -- Transport the existing squared triangle inequality to the nonnegative energy.
        have h := ENNReal.ofReal_le_ofReal
          (norm_sub_sq_le_two_mul (L m t ω) (H t ω) (K m t ω))
        simp only [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
          ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, ENNReal.ofReal_ofNat] at h
        simpa only [eNorm_sub_rev, mul_add] using h
      _ = _ := by
        have hmω : Measurable (fun t ↦ ‖L m t ω - K m t ω‖ₑ ^ 2) :=
          (hmeas m).comp (measurable_id.prodMk (measurable_const (a := ω)))
        rw [lintegral_add_left (hmω.const_mul 2),
          lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]
  have hlim := (ENNReal.Tendsto.const_mul (a := 2) hEω (Or.inr (by norm_num))).add
    (ENNReal.Tendsto.const_mul (a := 2) hKω (Or.inr (by norm_num)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa only [mul_zero, zero_add] using hlim)
    (Eventually.of_forall fun _ ↦ bot_le) (Eventually.of_forall hbound)

end MeasureTheory.IsStronglyPredictable

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
