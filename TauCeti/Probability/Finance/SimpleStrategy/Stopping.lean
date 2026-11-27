/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Finance.SimpleStrategy.Refinement

/-!
# Dyadic stopping of simple trading strategies

Stopping a bounded simple holding at an upward dyadic stopping time `dyadicCeilTime k ∘ τ` on any
finite horizon `[0, T]` is realized exactly by another bounded simple holding. For a single
elementary interval `(s, t]`, projecting the dyadic grid of mesh `2⁻ᵏ` onto `[s, min t T]`
(`TauCeti.dyadicProjIcc`) ensures that no rounded stopping time lies strictly inside any
subinterval, so the elementary gains telescope exactly
(`exists_simpleHolding_simpleGains_dyadicCeilTime_Ioc`). Refining these per-interval stopped grids
any finite-grid simple holding (`exists_simpleHolding_simpleGains_dyadicCeilTime`).

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.B–D.
-/

public section

noncomputable section

open MeasureTheory Set Finset
open scoped NNReal

namespace TauCeti.Finance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}

/-- On a single interval `(s, t]` with bounded `ℱ s`-measurable height `ξ`, stopping the
elementary integral at the dyadic stopping time `dyadicCeilTime k ∘ τ` at horizon `T` is realized
exactly by a bounded simple holding equal to `1_{[0, σ]} · 1_{(s, t]} ξ` on `[0, T]`. -/
theorem exists_simpleHolding_simpleGains_dyadicCeilTime_Ioc
    {s t : ℝ≥0} (hst : s ≤ t) {ξ : Ω → ℝ} (hξ : StronglyMeasurable[ℱ s] ξ)
    {C : ℝ} (hC : ∀ ω, ‖ξ ω‖ ≤ C) {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime ℱ τ)
    (k : ℕ) (T : ℝ≥0) :
    ∃ (N : ℕ) (p : ℕ → ℝ≥0) (ζ : ℕ → Ω → ℝ) (C' : ℝ),
      MonotoneOn p (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (p j)] (ζ j)) ∧
      (∀ j < N, ∀ ω, ‖ζ j ω‖ ≤ C') ∧
      (∀ u ≤ T, ∀ ω, simpleHolding p N ζ u ω =
        if (u : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then
          (Ioc s t).indicator (fun _ ↦ ξ ω) u else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), simpleGains p N ζ X T ω =
        stoppedProcess (fun u ω ↦ ξ ω * (X (min t u) ω - X (min s u) ω))
          (fun ω ↦ dyadicCeilTime k (τ ω)) T ω := by
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (τ ω)
  by_cases hsT : s ≤ T
  · -- Case `s ≤ T`: subdivide `[s, min t T]` by `dyadicProjIcc` so `σ` never splits a subinterval.
    let b : ℝ≥0 := min t T
    have hsb : s ≤ b := le_min hst hsT
    let N : ℕ := ⌊b * (2 : ℝ≥0) ^ k⌋₊ + 1
    let p : ℕ → ℝ≥0 := dyadicProjIcc s b hsb k
    have hp_mono : Monotone p := monotone_dyadicProjIcc hsb k
    have hp0 : p 0 = s := dyadicProjIcc_zero hsb k
    have hp_end : p N = b := dyadicProjIcc_end hsb k
    let ζ : ℕ → Ω → ℝ := fun j ω ↦ if (p j : WithTop ℝ≥0) < σ ω then ξ ω else 0
    have hζ_meas (j : ℕ) (_ : j < N) : StronglyMeasurable[ℱ (p j)] (ζ j) :=
      (hξ.mono (ℱ.mono (le_dyadicProjIcc hsb k j))).ite
        (by convert ((hτ.dyadicCeilTime k).measurableSet_le (p j)).compl using 1
            ext ω; simp only [σ, Set.mem_ofPred_eq, Set.mem_compl_iff, not_le])
        stronglyMeasurable_zero
    refine ⟨N, p, ζ, max C 0, hp_mono.monotoneOn _, hζ_meas, fun _ _ ω ↦ by
        dsimp only [ζ]; split_ifs <;> first | exact (hC ω).trans (le_max_left _ _) | simp,
      fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
    · -- Holding identity on `[0, T]`: inside `(s, b]` use the unique active subinterval.
      by_cases hu : u ∈ Ioc s b
      · obtain ⟨j₀, hj₀, hju⟩ :=
          exists_lt_mem_Ioc_of_mem_Ioc (τ := p) (n := N) (by simpa only [hp0, hp_end] using hu)
        rw [simpleHolding_of_mem_Ioc (hp_mono.monotoneOn _) hj₀ hju,
          indicator_of_mem (s := Ioc s t) ⟨hu.1, hu.2.trans (min_le_left t T)⟩]
        have hiff : (p j₀ : WithTop ℝ≥0) < σ ω ↔ (u : WithTop ℝ≥0) ≤ σ ω :=
          ⟨fun h ↦ (WithTop.coe_le_coe.mpr hju.2).trans (dyadicProjIcc_le_dyadicCeilTime hsb h),
            lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hju.1)⟩
        simp only [ζ, hiff, σ]
      · rw [simpleHolding_of_notMem_Ioc (hp_mono.monotoneOn _)
            (by simpa only [hp0, hp_end] using hu),
          indicator_of_notMem (fun h : u ∈ Ioc s t ↦ hu ⟨h.1, le_min h.2 huT⟩), ite_self]
    · -- Gain identity at `T`: telescope over the projected dyadic grid.
      rw [simpleGains_def]
      exact sum_dyadicProjIcc_telescope hst hsT k (τ ω) (ξ ω) (X · ω)
  · -- Case `T < s`: the interval `(s, t]` lies past the horizon `T`, so the zero strategy works.
    have hTs : T < s := lt_of_not_ge hsT
    refine ⟨0, fun _ ↦ 0, fun _ _ ↦ 0, 0,
      fun _ _ _ _ _ ↦ le_rfl,
      fun _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
      fun u huT ω ↦ by simp only [simpleHolding_def, Finset.range_zero, sum_empty,
        indicator_of_notMem (fun h : u ∈ Ioc s t ↦ not_lt_of_ge (huT.trans hTs.le) h.1), ite_self],
      fun X ω ↦ ?_⟩
    have hls : (min (T : WithTop ℝ≥0) (σ ω)).untopA ≤ s :=
      (WithTop.untopA_le (min_le_left _ _)).trans hTs.le
    rw [simpleGains_def, Finset.range_zero, sum_empty, stoppedProcess,
      min_eq_right (hls.trans hst), min_eq_right hls, sub_self, mul_zero]

/-- Stopping any bounded simple holding at the dyadic stopping time `dyadicCeilTime k ∘ σ₀` at
horizon `T` is realized exactly by another bounded simple holding. -/
theorem exists_simpleHolding_simpleGains_dyadicCeilTime
    {τ : ℕ → ℝ≥0} {n : ℕ} {a : ℕ → Ω → ℝ} {C : ℝ}
    (hτ : MonotoneOn τ (Set.Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (τ j)] (a j))
    (hb : ∀ j < n, ∀ ω, ‖a j ω‖ ≤ C)
    {σ₀ : Ω → WithTop ℝ≥0} (hσ₀ : IsStoppingTime ℱ σ₀) (k : ℕ) (T : ℝ≥0) :
    ∃ (N : ℕ) (p : ℕ → ℝ≥0) (ζ : ℕ → Ω → ℝ) (C' : ℝ),
      MonotoneOn p (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (p j)] (ζ j)) ∧
      (∀ j < N, ∀ ω, ‖ζ j ω‖ ≤ C') ∧
      (∀ u ≤ T, ∀ ω, simpleHolding p N ζ u ω =
        if (u : WithTop ℝ≥0) ≤ dyadicCeilTime k (σ₀ ω) then
          simpleHolding τ n a u ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), simpleGains p N ζ X T ω =
        stoppedProcess (simpleGains τ n a X) (fun ω ↦ dyadicCeilTime k (σ₀ ω)) T ω := by
  let σ : Ω → WithTop ℝ≥0 := fun ω ↦ dyadicCeilTime k (σ₀ ω)
  -- Step 1: realize the stopped strategy on each elementary interval `i < n` (0 for `i ≥ n`).
  have hsingle (i : ℕ) : ∃ (N : ℕ) (p : ℕ → ℝ≥0) (ζ : ℕ → Ω → ℝ) (C' : ℝ),
      MonotoneOn p (Set.Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (p j)] (ζ j)) ∧
      (∀ j < N, ∀ ω, ‖ζ j ω‖ ≤ C') ∧
      (i < n → ∀ u ≤ T, ∀ ω, simpleHolding p N ζ u ω =
        if (u : WithTop ℝ≥0) ≤ σ ω then
          (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ a i ω) u else 0) ∧
      (i < n → ∀ (X : ℝ≥0 → Ω → ℝ) (ω : Ω), simpleGains p N ζ X T ω =
        stoppedProcess (fun u ω ↦ a i ω * (X (min (τ (i + 1)) u) ω - X (min (τ i) u) ω))
          σ T ω) := by
    by_cases hi : i < n
    · obtain ⟨N, p, ζ, C', hp, hζ, hC', hhold, hgain⟩ :=
        exists_simpleHolding_simpleGains_dyadicCeilTime_Ioc
          (hτ hi.le hi (Nat.le_succ i)) (ha i hi) (hb i hi) hσ₀ k T
      exact ⟨N, p, ζ, C', hp, hζ, hC', fun _ ↦ hhold, fun _ ↦ hgain⟩
    · exact ⟨0, fun _ ↦ 0, fun _ _ ↦ 0, 0, fun _ _ _ _ _ ↦ le_rfl,
        fun _ hj ↦ (Nat.not_lt_zero _ hj).elim, fun _ hj ↦ (Nat.not_lt_zero _ hj).elim,
        fun h ↦ (hi h).elim, fun h ↦ (hi h).elim⟩
  choose N p ζ C' hp hζ hC' hhold hgain using hsingle
  -- Step 2: refine the per-interval stopped strategies onto a single common grid.
  let s : Finset (Σ _ : ℕ, ℕ) := (range n).sigma fun i ↦ range (N i)
  obtain ⟨M, ρ, c, -, hρ, -, -, hc, -, hbound, hH, hG⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ s (fun q ↦ p q.1 q.2) (fun q ↦ p q.1 (q.2 + 1))
      (fun q ↦ ζ q.1 q.2) (fun q hq ↦ hζ q.1 q.2 (mem_range.mp (mem_sigma.mp hq).2))
  refine ⟨M, ρ, c, ∑ i ∈ range n, ∑ _ ∈ range (N i), C' i, hρ.monotoneOn, fun j _ ↦ hc j,
    fun j hj ω ↦ (hbound j hj ω).trans ?_, fun u huT ω ↦ ?_, fun X ω ↦ ?_⟩
  · -- Step 3a: uniform bound on the refined heights.
    dsimp only [s]
    rw [Finset.sum_sigma]
    exact sum_le_sum fun i _ ↦ sum_le_sum fun j hj ↦ hC' i j (mem_range.mp hj) ω
  · -- Step 3b: holding identity on `[0, T]` by summing the per-interval holdings.
    rw [hH]
    dsimp only [s]
    rw [Finset.sum_sigma]
    calc ∑ i ∈ range n, ∑ j ∈ range (N i),
          (Ioc (p i j) (p i (j + 1))).indicator (fun _ ↦ ζ i j ω) u
        = ∑ i ∈ range n, simpleHolding (p i) (N i) (ζ i) u ω := by
          simp only [simpleHolding_def]
      _ = ∑ i ∈ range n, if (u : WithTop ℝ≥0) ≤ σ ω then
            (Ioc (τ i) (τ (i + 1))).indicator (fun _ ↦ a i ω) u else 0 :=
          sum_congr rfl fun i hi ↦ hhold i (mem_range.mp hi) u huT ω
      _ = if (u : WithTop ℝ≥0) ≤ σ ω then simpleHolding τ n a u ω else 0 := by
          rw [simpleHolding_def]; split_ifs <;> simp
  · -- Step 3c: gain identity at `T` by summing the per-interval stopped gains.
    rw [hG]
    dsimp only [s]
    rw [Finset.sum_sigma]
    calc ∑ i ∈ range n, ∑ j ∈ range (N i),
          (if p i j ≤ p i (j + 1) then
            ζ i j ω * (X (min (p i (j + 1)) T) ω - X (min (p i j) T) ω) else 0)
        = ∑ i ∈ range n, simpleGains (p i) (N i) (ζ i) X T ω :=
          sum_congr rfl fun i _ ↦ by
            rw [simpleGains_def]
            exact sum_congr rfl fun j hj ↦ by
              have hj' := mem_range.mp hj
              simp only [hp i hj'.le hj' (Nat.le_succ j), ite_true]
      _ = ∑ i ∈ range n, stoppedProcess (fun u ω ↦ a i ω *
            (X (min (τ (i + 1)) u) ω - X (min (τ i) u) ω)) σ T ω :=
          sum_congr rfl fun i hi ↦ hgain i (mem_range.mp hi) X ω
      _ = stoppedProcess (simpleGains τ n a X) σ T ω := by
          simp only [stoppedProcess, simpleGains_def]

end TauCeti.Finance
