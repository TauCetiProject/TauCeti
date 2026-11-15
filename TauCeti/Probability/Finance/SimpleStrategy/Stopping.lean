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
`1_{[0, dyadicCeilTime d (τ ω)]}` on `(0, T]` (`simpleHolding_dyadicGrid_ite_lt`), and its gains
against any process `X` equal `stoppedProcess X (dyadicCeilTime d ∘ τ) T - X 0`
(`simpleGains_dyadicGrid_ite_lt`).

Combining this cutoff strategy with simple-strategy associativity and common-grid refinement shows
that stopping the elementary gains of any left-measurable finite-grid strategy at
`dyadicCeilTime d ∘ τ` is represented on `[0, T]` by another left-measurable deterministic-grid
simple strategy (`exists_simpleHolding_stopped_dyadicCeilTime`).

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
  · rw [ite_eq_left hlt, ite_eq_left ((mem_Ioc_dyadicGrid_le_iff d T (τ ω) hk hsk).2 hlt)]
  · have hnle : ¬ ((s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω)) :=
      fun h ↦ hlt ((mem_Ioc_dyadicGrid_le_iff d T (τ ω) hk hsk).1 h)
    rw [ite_eq_right hlt, ite_eq_right hnle]

/-- At horizon `T`, the elementary gains of the unit cutoff strategy on `dyadicGrid d T` against any
process `X` equal the stopped increment `stoppedProcess X (dyadicCeilTime d ∘ τ) T - X 0`. -/
theorem simpleGains_dyadicGrid_ite_lt (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    simpleGains (dyadicGrid d T) (dyadicCount d T)
      (fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
      X T ω =
      stoppedProcess X (fun ω ↦ dyadicCeilTime d (τ ω)) T ω - X 0 ω := by
  let K := dyadicStopIndex d T (τ ω)
  have hsum := simpleGains_apply_eq_sum (X := X) (ω := ω)
    (a := fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
    ((dyadicGrid_mono d T).monotoneOn _) (le_rfl : dyadicCount d T ≤ dyadicCount d T)
  rw [dyadicGrid_count d T] at hsum
  rw [hsum]
  have hfilter : (range (dyadicCount d T)).filter (· < K) = range K := by
    ext k
    have hK := dyadicStopIndex_le d T (τ ω)
    simp only [Finset.mem_filter, Finset.mem_range, K]
    omega
  have hcongr :
      (∑ k ∈ range (dyadicCount d T),
        (if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then (1 : ℝ) else 0) *
          (X (dyadicGrid d T (k + 1)) ω - X (dyadicGrid d T k) ω)) =
      ∑ k ∈ range K, (X (dyadicGrid d T (k + 1)) ω - X (dyadicGrid d T k) ω) := by
    rw [← hfilter, sum_filter]
    refine sum_congr rfl fun k hk ↦ ?_
    have hiff := dyadicGrid_lt_dyadicCeilTime_iff d T (τ ω) (Finset.mem_range.1 hk)
    by_cases hk' : k < K
    · rw [ite_eq_left (hiff.2 hk'), one_mul, ite_eq_left hk']
    · rw [ite_eq_right (mt hiff.1 hk'), zero_mul, ite_eq_right hk']
  rw [hcongr, sum_range_sub (fun k ↦ X (dyadicGrid d T k) ω), dyadicGrid_zero,
    dyadicGrid_dyadicStopIndex, stoppedProcess]

/-- Stopping a left-measurable simple strategy at the dyadic ceiling `dyadicCeilTime d ∘ τ` of a raw
stopping time `τ` is represented on `[0, T]` by a single deterministic-grid left-measurable simple
strategy. -/
theorem exists_simpleHolding_stopped_dyadicCeilTime {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (d : ℕ) (T : ℝ≥0)
    {n : ℕ} {g : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (g j)] (a j))
    (W : ℝ≥0 → Ω → ℝ) :
    ∃ (N : ℕ) (r : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn r (Iic N) ∧
      (∀ i < N, StronglyMeasurable[ℱ (r i)] (b i)) ∧
      (∀ s ∈ Ioc 0 T, ∀ ω, simpleHolding r N b s ω =
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then simpleHolding g n a s ω else 0) ∧
      ∀ ω, simpleGains r N b W T ω =
        stoppedProcess (simpleGains g n a W) (fun ω ↦ dyadicCeilTime d (τ ω)) T ω := by
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
    have hu : StronglyMeasurable[ℱ (l p)] (u p.1) := by
      have heq : u p.1 = {ω | (q p.1 : WithTop ℝ≥0) < σ ω}.indicator 1 := funext fun ω ↦ by
        by_cases h : (q p.1 : WithTop ℝ≥0) < σ ω
        · rw [Set.indicator_of_mem h, Pi.one_apply]; exact ite_eq_left h
        · rw [Set.indicator_of_notMem h]; exact ite_eq_right h
      exact heq ▸ stronglyMeasurable_const.indicator hmeasA
    exact hu.mul ((ha p.2 hj).mono (ℱ.mono (le_max_left _ _)))
  obtain ⟨N, r, b, -, hr, hb, -, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ s_idx l hi c hc
  refine ⟨N, r, b, hr.monotoneOn, hb, fun s hs ω ↦ ?_, fun ω ↦ ?_⟩
  · rw [hhold, sum_product, ← simpleHolding_mul_eq_sum, simpleHolding_dyadicGrid_ite_lt d T τ hs]
    split_ifs <;> simp
  · rw [hgains, sum_product,
      ← simpleGains_simpleGains_eq_sum hg ((dyadicGrid_mono d T).monotoneOn _),
      simpleGains_dyadicGrid_ite_lt, simpleGains_of_le hg zero_le, sub_zero]

end TauCeti.Finance
