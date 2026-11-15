/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Refinement
public import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Finance.SimpleStrategy.Associativity

/-!
# Stopping simple trading strategies at dyadic ceiling times

On a fixed finite horizon `T`, the unit strategy on `dyadicGrid d T` that holds one unit on step `k`
when `dyadicGrid d T k < dyadicCeilTime d (τ ω)` realizes the random interval indicator
`1_{[0, dyadicCeilTime d (τ ω)]}` on `(0, T]` (`simpleHolding_dyadicGrid_ite_lt`), and its gains at
every time `s ≤ T` against any process `X` equal `stoppedProcess X (dyadicCeilTime d ∘ τ) s - X 0`
(`simpleGains_dyadicGrid_ite_lt`).

Combining this cutoff strategy with simple-strategy associativity and common-grid refinement shows
that stopping a left-measurable finite-grid strategy at `dyadicCeilTime d ∘ τ` is represented on
`[0, T]`, universally across all price processes `W`, by a single strictly increasing
deterministic-grid left-measurable simple strategy starting at `0` with heights bounded by the sum
of the original absolute heights
(`exists_simpleHolding_simpleGains_stoppedProcess_dyadicCeilTime`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Springer, 2005, Chapter II, §2.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory Set
open Finset hiding Iic mem_Iic
open scoped NNReal

namespace TauCeti.Finance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-- On `(0, T]`, holding one unit on step `k` of `dyadicGrid d T` whenever
`dyadicGrid d T k < dyadicCeilTime d (τ ω)` equals the indicator of
`[0, dyadicCeilTime d (τ ω)]`. -/
theorem simpleHolding_dyadicGrid_ite_lt (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    {s : ℝ≥0} (hs : s ∈ Ioc 0 T) (ω : Ω) :
    simpleHolding (dyadicGrid d T) (dyadicCount d T)
      (fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
      s ω = if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then 1 else 0 := by
  have hs_mem : s ∈ Ioc (dyadicGrid d T 0) (dyadicGrid d T (dyadicCount d T)) := by
    simpa only [dyadicGrid_zero, dyadicGrid_count] using hs
  obtain ⟨k, hk, hsk⟩ := exists_lt_mem_Ioc_of_mem_Ioc hs_mem
  rw [simpleHolding_of_mem_Ioc ((dyadicGrid_mono d T).monotoneOn _) hk hsk]
  by_cases hlt : (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω)
  · rw [ite_eq_left hlt,
      ite_eq_left ((coe_le_dyadicCeilTime_iff_of_mem_Ioc d T (τ ω) hk hsk).2 hlt)]
  · have hnle : ¬ ((s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω)) :=
      fun h ↦ hlt ((coe_le_dyadicCeilTime_iff_of_mem_Ioc d T (τ ω) hk hsk).1 h)
    rw [ite_eq_right hlt, ite_eq_right hnle]

/-- At every time `s ≤ T`, the elementary gains of the unit cutoff strategy on `dyadicGrid d T`
against any process `X` equal the stopped increment
`stoppedProcess X (dyadicCeilTime d ∘ τ) s - X 0`. -/
theorem simpleGains_dyadicGrid_ite_lt (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    {s : ℝ≥0} (hs : s ≤ T) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    simpleGains (dyadicGrid d T) (dyadicCount d T)
      (fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
      X s ω =
      stoppedProcess X (fun ω ↦ dyadicCeilTime d (τ ω)) s ω - X 0 ω := by
  let K := dyadicStopIndex d T (τ ω)
  rw [simpleGains_def]
  have hfilter : (range (dyadicCount d T)).filter (· < K) = range K := by
    ext k
    have hK := dyadicStopIndex_le d T (τ ω)
    simp only [Finset.mem_filter, Finset.mem_range, K]
    omega
  have hcongr :
      (∑ k ∈ range (dyadicCount d T),
        (if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then (1 : ℝ) else 0) *
          (X (min (dyadicGrid d T (k + 1)) s) ω - X (min (dyadicGrid d T k) s) ω)) =
      ∑ k ∈ range K, (X (min (dyadicGrid d T (k + 1)) s) ω - X (min (dyadicGrid d T k) s) ω) := by
    rw [← hfilter, sum_filter]
    refine sum_congr rfl fun k hk ↦ ?_
    have hiff := dyadicGrid_lt_dyadicCeilTime_iff d T (τ ω) (Finset.mem_range.1 hk)
    by_cases hk' : k < K
    · rw [ite_eq_left (hiff.2 hk'), one_mul, ite_eq_left hk']
    · rw [ite_eq_right (mt hiff.1 hk'), zero_mul, ite_eq_right hk']
  have hminK : min (dyadicGrid d T K) s =
      (min (s : WithTop ℝ≥0) (dyadicCeilTime d (τ ω))).untopA := by
    rw [dyadicGrid_dyadicStopIndex]
    cases hσ : dyadicCeilTime d (τ ω) with
    | top =>
      rw [min_eq_left le_top, min_eq_left le_top, WithTop.untopA, WithTop.untopD_coe,
        WithTop.untopD_coe, min_eq_right hs]
    | coe u =>
      rw [← WithTop.coe_min, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe,
        WithTop.untopD_coe, min_right_comm, min_eq_right hs, min_comm]
  rw [hcongr, sum_range_sub (fun k ↦ X (min (dyadicGrid d T k) s) ω), dyadicGrid_zero,
    min_eq_left (zero_le : 0 ≤ s), hminK, stoppedProcess]

/-- Stopping a left-measurable simple strategy at the dyadic ceiling `dyadicCeilTime d ∘ τ` of a raw
stopping time `τ` is represented throughout `[0, T]` — both for its holdings and for its elementary
gains against every price process `W` — by a single strictly increasing deterministic-grid
left-measurable simple strategy starting at `0` whose heights are bounded pointwise by the sum of
the original absolute heights. -/
theorem exists_simpleHolding_simpleGains_stoppedProcess_dyadicCeilTime {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (d : ℕ) (T : ℝ≥0)
    {n : ℕ} {g : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (g j)] (a j)) :
    ∃ (N : ℕ) (r : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      r 0 = 0 ∧ StrictMonoOn r (Iic N) ∧
      (∀ i < N, StronglyMeasurable[ℱ (r i)] (b i)) ∧
      (∀ i < N, ∀ ω, ‖b i ω‖ ≤ ∑ j ∈ range n, ‖a j ω‖) ∧
      (∀ s ≤ T, ∀ ω, simpleHolding r N b s ω =
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then simpleHolding g n a s ω else 0) ∧
      ∀ (W : ℝ≥0 → Ω → ℝ), ∀ s ≤ T, ∀ ω, simpleGains r N b W s ω =
        stoppedProcess (simpleGains g n a W) (fun ω ↦ dyadicCeilTime d (τ ω)) s ω := by
  let q := dyadicGrid d T
  let σ (ω : Ω) := dyadicCeilTime d (τ ω)
  have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime d
  let u (k : ℕ) (ω : Ω) : ℝ := if (q k : WithTop ℝ≥0) < σ ω then 1 else 0
  let s_idx : Finset (ℕ × ℕ) := range (dyadicCount d T) ×ˢ range n
  let l (p : ℕ × ℕ) : ℝ≥0 := max (g p.2) (q p.1)
  let hi (p : ℕ × ℕ) : ℝ≥0 := min (g (p.2 + 1)) (q (p.1 + 1))
  let c (p : ℕ × ℕ) (ω : Ω) : ℝ := u p.1 ω * a p.2 ω
  have hc : ∀ p ∈ s_idx, StronglyMeasurable[ℱ (l p)] (c p) := fun p hp ↦ by
    have hj : p.2 < n := Finset.mem_range.1 (Finset.mem_product.1 hp).2
    have hmeasA : MeasurableSet[ℱ (l p)] {ω | (q p.1 : WithTop ℝ≥0) < σ ω} :=
      ℱ.mono (le_max_right _ _) _ (hσ.measurableSet_gt (q p.1))
    have hu : StronglyMeasurable[ℱ (l p)] (u p.1) :=
      StronglyMeasurable.ite hmeasA stronglyMeasurable_const stronglyMeasurable_const
    exact hu.mul ((ha p.2 hj).mono (ℱ.mono (le_max_left _ _)))
  obtain ⟨N, r, b, hr0, hr, hb, -, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ s_idx l hi c hc
  refine ⟨N, r, b, hr0, hr, hb, fun i hi_lt ω ↦ ?_, fun s hs ω ↦ ?_, fun W s hs ω ↦ ?_⟩
  · have hmem : r (i + 1) ∈ Ioc (r i) (r (i + 1)) :=
      ⟨hr hi_lt.le hi_lt (Nat.lt_succ_self i), le_rfl⟩
    have hbi : b i ω = simpleHolding q (dyadicCount d T) u (r (i + 1)) ω *
        simpleHolding g n a (r (i + 1)) ω := by
      rw [← simpleHolding_of_mem_Ioc (a := b) hr.monotoneOn hi_lt hmem ω, hhold, sum_product,
        ← simpleHolding_mul_eq_sum]
    have hu_le : ‖simpleHolding q (dyadicCount d T) u (r (i + 1)) ω‖ ≤ 1 := by
      by_cases hq : r (i + 1) ∈ Ioc (q 0) (q (dyadicCount d T))
      · obtain ⟨k, hk, hkq⟩ := exists_lt_mem_Ioc_of_mem_Ioc hq
        rw [simpleHolding_of_mem_Ioc ((dyadicGrid_mono d T).monotoneOn _) hk hkq]
        dsimp only [u]
        split_ifs <;> simp
      · rw [simpleHolding_of_notMem_Ioc ((dyadicGrid_mono d T).monotoneOn _) hq, norm_zero]
        exact zero_le_one
    have ha_le : ‖simpleHolding g n a (r (i + 1)) ω‖ ≤ ∑ j ∈ range n, ‖a j ω‖ := by
      rw [simpleHolding_def]
      exact (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ norm_indicator_le_norm_self _ _)
    rw [hbi, norm_mul]
    exact (mul_le_mul hu_le ha_le (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · rcases eq_or_lt_of_le (zero_le : 0 ≤ s) with rfl | hs0
    · have hzero {m : ℕ} {f : ℕ → ℝ≥0} {v : ℕ → Ω → ℝ} : simpleHolding f m v 0 ω = 0 := by
        rw [simpleHolding_def]
        exact sum_eq_zero fun j _ ↦
          Set.indicator_of_notMem (fun (h : 0 ∈ Set.Ioc _ _) ↦ not_lt_zero h.1) _
      simp [hzero]
    · rw [hhold, sum_product, ← simpleHolding_mul_eq_sum,
        simpleHolding_dyadicGrid_ite_lt d T τ ⟨hs0, hs⟩]
      split_ifs <;> simp
  · rw [hgains, sum_product,
      ← simpleGains_simpleGains_eq_sum hg ((dyadicGrid_mono d T).monotoneOn _),
      simpleGains_dyadicGrid_ite_lt d T τ hs, simpleGains_of_le hg zero_le, sub_zero]

end TauCeti.Finance
