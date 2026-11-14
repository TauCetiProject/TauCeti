/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.Ito.Martingale
public import TauCeti.Probability.BrownianMotion.Integral.Energy.Localization
public import TauCeti.Probability.BrownianMotion.Integral.Stopping
import TauCeti.Probability.BrownianMotion.Martingale
import TauCeti.Probability.Finance.SimpleStrategy.Refinement
import TauCeti.Probability.Martingale.Local.Congruence
import TauCeti.Probability.Process.Patching
import TauCeti.Probability.Process.Stopping
import TauCeti.Probability.Process.StoppingApproximation

/-!
# Stopping and localizing the Brownian Itô integral process

This file proves stability of `TauCeti.IsItoIntegral` under stopping at raw-filtration stopping
times, deduces the native local-martingale property, and constructs predictable almost surely
continuous Itô integral processes across the full pathwise square-energy domain
`TauCeti.LocallyBrownianIntegrable`:

* `IsItoIntegral.stoppedProcess`: against a filtered pre-Brownian motion `W`, stopping an Itô
  integral `I` of `H` at a stopping time `τ` yields an Itô integral of the cutoff integrand
  `H · 1_{[0, τ]}`, without assuming path continuity of `W` or adaptation of `I`.
* `IsItoIntegral.stoppedProcess_indist_of_ae_eq`: local determination of `stoppedProcess I τ` by
  the restriction of the integrand to `[0, τ]`.
* `IsItoIntegral.locally_martingale`: any strongly progressive Itô integral against a filtered
  pre-Brownian motion is a native local martingale (`Locally (Martingale · ℱ P) ℱ I P`).
* `LocallyBrownianIntegrable.exists_isItoIntegral`: against a filtered pre-Brownian motion `W`
  with almost surely continuous paths, every `LocallyBrownianIntegrable` integrand admits a
  predictable almost surely continuous local-martingale Itô integral on the raw filtration.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2.D.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open Set hiding mem_range
open Finset hiding Iic mem_Iic min_zero
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {P : Measure Ω} {W H K I J : ℝ≥0 → Ω → ℝ} {τ : Ω → WithTop ℝ≥0}

private def dyadicCount (d : ℕ) (T : ℝ≥0) : ℕ := ⌊T * 2 ^ d⌋₊ + 1

private def dyadicGrid (d : ℕ) (T : ℝ≥0) (k : ℕ) : ℝ≥0 := min ((k : ℝ≥0) / 2 ^ d) T

private def dyadicStopIndex (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0) : ℕ :=
  match u with
  | ⊤ => dyadicCount d T
  | (r : ℝ≥0) => min ⌈r * 2 ^ d⌉₊ (dyadicCount d T)

private theorem dyadicGrid_mono (d : ℕ) (T : ℝ≥0) : Monotone (dyadicGrid d T) :=
  fun _ _ hab ↦ min_le_min_right T (div_le_div_of_nonneg_right (Nat.cast_le.2 hab) (by positivity))

private theorem dyadicGrid_zero (d : ℕ) (T : ℝ≥0) : dyadicGrid d T 0 = 0 := by
  simp [dyadicGrid]

private theorem dyadicGrid_count (d : ℕ) (T : ℝ≥0) : dyadicGrid d T (dyadicCount d T) = T := by
  rw [dyadicGrid, dyadicCount]
  refine min_eq_right ((le_div_iff₀ (by positivity)).2 ?_)
  exact_mod_cast (Nat.lt_floor_add_one (T * 2 ^ d)).le

private theorem dyadicGrid_of_lt (d : ℕ) (T : ℝ≥0) {k : ℕ} (hk : k < dyadicCount d T) :
    dyadicGrid d T k = (k : ℝ≥0) / 2 ^ d := by
  refine min_eq_left ((div_le_iff₀ (by positivity)).2 ?_)
  exact (Nat.cast_le.2 (Nat.lt_succ_iff.1 hk)).trans (Nat.floor_le (by positivity))

private theorem dyadicStopIndex_spec (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0) :
    dyadicStopIndex d T u ≤ dyadicCount d T ∧
      dyadicGrid d T (dyadicStopIndex d T u) =
        (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA ∧
      ∀ k < dyadicCount d T,
        ((dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u ↔ k < dyadicStopIndex d T u) := by
  cases u with
  | top =>
    dsimp only [dyadicStopIndex]
    refine ⟨le_rfl, ?_, fun k hk ↦ ?_⟩
    · rw [dyadicGrid_count, dyadicCeilTime_top, min_top_right, WithTop.untopA, WithTop.untopD_coe]
    · rw [dyadicCeilTime_top]
      exact ⟨fun _ ↦ hk, fun _ ↦ WithTop.coe_lt_top _⟩
  | coe r =>
    dsimp only [dyadicStopIndex]
    refine ⟨min_le_right _ _, ?_, fun k hk ↦ ?_⟩
    · rw [dyadicCeilTime_coe, ← WithTop.coe_min, WithTop.untopA, WithTop.untopD_coe]
      by_cases hle : ⌈r * 2 ^ d⌉₊ ≤ dyadicCount d T
      · simp [min_eq_left hle, dyadicGrid, min_comm]
      · have hge : dyadicCount d T ≤ ⌈r * 2 ^ d⌉₊ := le_of_not_ge hle
        have hT : T ≤ (⌈r * 2 ^ d⌉₊ : ℝ≥0) / 2 ^ d := by
          have h := dyadicGrid_mono d T hge
          rw [dyadicGrid_count] at h
          exact (le_min_iff.1 h).1
        rw [min_eq_right hge, dyadicGrid_count, min_eq_left hT]
    · rw [dyadicGrid_of_lt d T hk, dyadicCeilTime_coe, WithTop.coe_lt_coe,
        div_lt_div_iff_of_pos_right (by positivity), Nat.cast_lt, lt_min_iff]
      exact ⟨fun h ↦ ⟨h, hk⟩, fun h ↦ h.1⟩

private theorem mem_Ioc_dyadicGrid_le_iff (d : ℕ) (T : ℝ≥0) (u : WithTop ℝ≥0)
    {k : ℕ} (hk : k < dyadicCount d T) {s : ℝ≥0}
    (hs : s ∈ Ioc (dyadicGrid d T k) (dyadicGrid d T (k + 1))) :
    ((s : WithTop ℝ≥0) ≤ dyadicCeilTime d u) ↔
      ((dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u) := by
  obtain ⟨_, hK_eq, hlt_iff⟩ := dyadicStopIndex_spec d T u
  constructor
  · intro hs_le
    exact (WithTop.coe_lt_coe.2 hs.1).trans_le hs_le
  · intro hlt
    have hk1 : k + 1 ≤ dyadicStopIndex d T u := (hlt_iff k hk).1 hlt
    have hs_le : s ≤ (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA :=
      hs.2.trans ((dyadicGrid_mono d T hk1).trans_eq hK_eq)
    have hne : min (T : WithTop ℝ≥0) (dyadicCeilTime d u) ≠ ⊤ :=
      ((min_le_left _ _).trans_lt (WithTop.coe_lt_top T)).ne
    exact ((WithTop.le_untopA_iff hne).1 hs_le).trans (min_le_right _ _)

private theorem sum_dyadicGrid_ite_eq_sub {A B T : ℝ≥0} (hAB : A ≤ B) (d : ℕ) (u : WithTop ℝ≥0)
    (f : ℝ≥0 → ℝ) :
    (∑ k ∈ range (dyadicCount d T),
      if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u then
        (if max A (dyadicGrid d T k) ≤ min B (dyadicGrid d T (k + 1)) then
          f (min B (dyadicGrid d T (k + 1))) - f (max A (dyadicGrid d T k)) else 0)
      else 0) =
      f (min B (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA) -
        f (min A (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA) := by
  obtain ⟨_, hK_eq, hlt_iff⟩ := dyadicStopIndex_spec d T u
  have hfilter : (range (dyadicCount d T)).filter (fun k ↦ k < dyadicStopIndex d T u) =
      range (dyadicStopIndex d T u) := by
    ext k
    simp only [mem_filter, mem_range]
    omega
  have hcongr : (∑ k ∈ range (dyadicCount d T),
      if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u then
        (if max A (dyadicGrid d T k) ≤ min B (dyadicGrid d T (k + 1)) then
          f (min B (dyadicGrid d T (k + 1))) - f (max A (dyadicGrid d T k)) else 0) else 0) =
      ∑ k ∈ range (dyadicStopIndex d T u),
        (f (max A (min B (dyadicGrid d T (k + 1)))) - f (max A (min B (dyadicGrid d T k)))) := by
    rw [← hfilter, sum_filter]
    refine sum_congr rfl fun k hk ↦ ?_
    by_cases hk' : k < dyadicStopIndex d T u
    · rw [ite_eq_left ((hlt_iff k (mem_range.1 hk)).2 hk'), ite_eq_left hk']
      have hlu : dyadicGrid d T k ≤ dyadicGrid d T (k + 1) := dyadicGrid_mono d T (Nat.le_succ k)
      by_cases h : max A (dyadicGrid d T k) ≤ min B (dyadicGrid d T (k + 1))
      · have hlB : dyadicGrid d T k ≤ B := (max_le_iff.1 (le_min_iff.1 h).1).2
        have hAu : A ≤ dyadicGrid d T (k + 1) := (max_le_iff.1 (le_min_iff.1 h).2).1
        rw [ite_eq_left h, min_eq_right hlB, max_eq_right (le_min hAB hAu)]
      · rw [ite_eq_right h]
        by_cases hAu : A ≤ dyadicGrid d T (k + 1)
        · have hBl : B ≤ dyadicGrid d T k :=
            le_of_not_ge fun hlB ↦ h (max_le (le_min hAB hAu) (le_min hlB hlu))
          rw [min_eq_left hBl, min_eq_left (hBl.trans hlu), sub_self]
        · have huA : dyadicGrid d T (k + 1) ≤ A := le_of_not_ge hAu
          rw [max_eq_left ((min_le_right B _).trans huA),
            max_eq_left ((min_le_right B _).trans (hlu.trans huA)), sub_self]
    · have hnlt : ¬ ((dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d u) :=
        fun h ↦ hk' ((hlt_iff k (mem_range.1 hk)).1 h)
      rw [ite_eq_right hnlt, ite_eq_right hk']
  rw [hcongr, sum_range_sub (fun k ↦ f (max A (min B (dyadicGrid d T k)))),
    dyadicGrid_zero, min_zero, max_eq_left zero_le, hK_eq]
  rcases le_total A (min (T : WithTop ℝ≥0) (dyadicCeilTime d u)).untopA with hAu | huA
  · rw [min_eq_left hAu, max_eq_right (le_min hAB hAu)]
  · rw [min_eq_right huA, min_eq_right (huA.trans hAB), max_eq_left huA, sub_self, sub_self]

private theorem sum_dyadicGrid_clipped_mul_sub {n : ℕ} {g : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Iic n)) (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    (W : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    (∑ p ∈ range n ×ˢ range (dyadicCount d T),
      if max (g p.1) (dyadicGrid d T p.2) ≤ min (g (p.1 + 1)) (dyadicGrid d T (p.2 + 1)) then
        (if (dyadicGrid d T p.2 : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then a p.1 ω else 0) *
          (W (min (min (g (p.1 + 1)) (dyadicGrid d T (p.2 + 1))) T) ω -
            W (min (max (g p.1) (dyadicGrid d T p.2)) T) ω)
      else 0) =
      stoppedProcess (Finance.simpleGains g n a W) (fun ω ↦ dyadicCeilTime d (τ ω)) T ω := by
  rw [sum_product]
  have huT (j k : ℕ) : min (g (j + 1)) (dyadicGrid d T (k + 1)) ≤ T :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hsum_j (j : ℕ) (hj : j ∈ range n) :
      (∑ k ∈ range (dyadicCount d T),
        if max (g j) (dyadicGrid d T k) ≤ min (g (j + 1)) (dyadicGrid d T (k + 1)) then
          (if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then a j ω else 0) *
            (W (min (min (g (j + 1)) (dyadicGrid d T (k + 1))) T) ω -
              W (min (max (g j) (dyadicGrid d T k)) T) ω) else 0) =
      a j ω * (W (min (g (j + 1)) (min (T : WithTop ℝ≥0) (dyadicCeilTime d (τ ω))).untopA) ω -
        W (min (g j) (min (T : WithTop ℝ≥0) (dyadicCeilTime d (τ ω))).untopA) ω) := by
    have hAB : g j ≤ g (j + 1) := hg (mem_range.1 hj).le (mem_range.1 hj) (Nat.le_succ j)
    rw [← sum_dyadicGrid_ite_eq_sub hAB d (τ ω) (fun v ↦ W v ω), mul_sum]
    refine sum_congr rfl fun k _ ↦ ?_
    by_cases hlu : max (g j) (dyadicGrid d T k) ≤ min (g (j + 1)) (dyadicGrid d T (k + 1))
    · rw [ite_eq_left hlu, min_eq_left (huT j k), min_eq_left (hlu.trans (huT j k)),
        ite_eq_left hlu, ite_mul, mul_ite, zero_mul, mul_zero]
    · rw [ite_eq_right hlu, ite_eq_right hlu, ite_self, mul_zero]
  rw [sum_congr rfl hsum_j, ← Finance.simpleGains_def, stoppedProcess]

private theorem sum_dyadicGrid_indicator_eq_ite {n : ℕ} (g : ℕ → ℝ≥0) (a : ℕ → Ω → ℝ)
    (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0) {s : ℝ≥0} (hs : s ∈ Ioc 0 T) (ω : Ω) :
    (∑ p ∈ range n ×ˢ range (dyadicCount d T),
      (Ioc (max (g p.1) (dyadicGrid d T p.2))
        (min (g (p.1 + 1)) (dyadicGrid d T (p.2 + 1)))).indicator
        (fun _ ↦ if (dyadicGrid d T p.2 : WithTop ℝ≥0) < dyadicCeilTime d (τ ω)
          then a p.1 ω else 0) s) =
      if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then
        Finance.simpleHolding g n a s ω else 0 := by
  rw [sum_product_right, Finance.simpleHolding_def]
  have hs_mem : s ∈ Ioc (dyadicGrid d T 0) (dyadicGrid d T (dyadicCount d T)) := by
    simpa only [dyadicGrid_zero, dyadicGrid_count] using hs
  obtain ⟨k, hk, hsk⟩ := exists_lt_mem_Ioc_of_mem_Ioc hs_mem
  rw [sum_eq_single k]
  · have hiff (j : ℕ) : s ∈ Ioc (max (g j) (dyadicGrid d T k))
        (min (g (j + 1)) (dyadicGrid d T (k + 1))) ↔ s ∈ Ioc (g j) (g (j + 1)) := by
      simp only [Set.mem_Ioc, max_lt_iff, le_min_iff, hsk.1, hsk.2, and_true]
    by_cases hlt : (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω)
    · rw [ite_eq_left ((mem_Ioc_dyadicGrid_le_iff d T (τ ω) hk hsk).2 hlt)]
      refine sum_congr rfl fun j _ ↦ ?_
      rw [ite_eq_left hlt]
      by_cases hmem : s ∈ Ioc (g j) (g (j + 1))
      · rw [indicator_of_mem ((hiff j).2 hmem), indicator_of_mem hmem]
      · rw [indicator_of_notMem (mt (hiff j).1 hmem), indicator_of_notMem hmem]
    · have hs_nle : ¬ ((s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω)) :=
        fun h ↦ hlt ((mem_Ioc_dyadicGrid_le_iff d T (τ ω) hk hsk).1 h)
      rw [ite_eq_right hs_nle]
      refine sum_eq_zero fun j _ ↦ ?_
      rw [ite_eq_right hlt]
      exact indicator_apply_eq_zero.2 fun _ ↦ rfl
  · intro k' _ hne
    refine sum_eq_zero fun j _ ↦ indicator_of_notMem (fun hmem ↦ ?_) _
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hsk.1.not_ge
        ((le_min_iff.1 hmem.2).2.trans (dyadicGrid_mono d T (Nat.succ_le_of_lt hlt)))
    · exact ((dyadicGrid_mono d T (Nat.succ_le_of_lt hgt)).trans_lt
        (max_lt_iff.1 hmem.1).2).not_ge hsk.2
  · exact fun hk' ↦ (hk' (mem_range.2 hk)).elim

private theorem exists_simpleHolding_stopped_dyadicCeilTime
    (hτ : IsStoppingTime ℱ τ) (d : ℕ) (T : ℝ≥0)
    {n : ℕ} {g : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (g j)] (a j)) :
    ∃ (N : ℕ) (r : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      MonotoneOn r (Iic N) ∧
      (∀ i < N, StronglyMeasurable[ℱ (r i)] (b i)) ∧
      (∀ s ∈ Ioc 0 T, ∀ ω, Finance.simpleHolding r N b s ω =
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then
          Finance.simpleHolding g n a s ω else 0) ∧
      ∀ ω, Finance.simpleGains r N b W T ω =
        stoppedProcess (Finance.simpleGains g n a W) (fun ω ↦ dyadicCeilTime d (τ ω)) T ω := by
  let q := dyadicGrid d T
  let σ (ω : Ω) := dyadicCeilTime d (τ ω)
  have hσ : IsStoppingTime ℱ σ := hτ.dyadicCeilTime d
  let s_idx : Finset (ℕ × ℕ) := range n ×ˢ range (dyadicCount d T)
  let l (p : ℕ × ℕ) : ℝ≥0 := max (g p.1) (q p.2)
  let u (p : ℕ × ℕ) : ℝ≥0 := min (g (p.1 + 1)) (q (p.2 + 1))
  let c (p : ℕ × ℕ) (ω : Ω) : ℝ := if (q p.2 : WithTop ℝ≥0) < σ ω then a p.1 ω else 0
  have hc : ∀ p ∈ s_idx, StronglyMeasurable[ℱ (l p)] (c p) := fun p hp ↦ by
    have hj : p.1 < n := mem_range.1 (mem_product.1 hp).1
    have hmeasA : MeasurableSet[ℱ (l p)] {ω | (q p.2 : WithTop ℝ≥0) < σ ω} :=
      ℱ.mono (le_max_right _ _) _ (hσ.measurableSet_gt (q p.2))
    have hc_eq : c p = {ω | (q p.2 : WithTop ℝ≥0) < σ ω}.indicator (a p.1) := funext fun ω ↦ by
      by_cases h : (q p.2 : WithTop ℝ≥0) < σ ω
      · dsimp only [c]
        rw [ite_eq_left h, Set.indicator_of_mem h]
      · dsimp only [c]
        rw [ite_eq_right h, Set.indicator_of_notMem h]
    exact hc_eq ▸ ((ha p.1 hj).mono (ℱ.mono (le_max_left _ _))).indicator hmeasA
  obtain ⟨N, r, b, -, hr, hb, -, hhold, hgains⟩ :=
    Finance.exists_simpleHolding_simpleGains_eq_sum ℱ s_idx l u c hc
  exact ⟨N, r, b, hr.monotoneOn, hb,
    fun s hs ω ↦ (hhold s ω).trans (sum_dyadicGrid_indicator_eq_ite g a d T τ hs ω),
    fun ω ↦ (hgains W T ω).trans (sum_dyadicGrid_clipped_mul_sub hg d T τ W ω)⟩

private theorem tendstoInMeasure_simpleGains_of_le
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) {v T : ℝ≥0} (hvT : v ≤ T)
    {n : ℕ → ℕ} {g : ℕ → ℕ → ℝ≥0} {a : ℕ → ℕ → Ω → ℝ}
    (hg : ∀ m, MonotoneOn (g m) (Iic (n m)))
    (ha : ∀ m j, j < n m → StronglyMeasurable[ℱ (g m j)] (a m j))
    (hE : ∀ ε : ℝ≥0∞, 0 < ε → Tendsto (fun m ↦ P {ω | ε ≤
      ∫⁻ s, ‖Finance.simpleHolding (g m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
        ∂Probability.timeMeasure T}) atTop (𝓝 0)) :
    TendstoInMeasure P (fun m ↦ Finance.simpleGains (g m) (n m) (a m) W v) atTop (I v) := by
  have hle : Probability.timeMeasure v ≤ Probability.timeMeasure T := by
    rw [Probability.timeMeasure_def, Probability.timeMeasure_def]
    exact Measure.restrict_mono_set _ (Ioc_subset_Ioc_right hvT)
  refine hI.tendstoInMeasure_simpleGains hW hg ha fun δ hδ ↦ ?_
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE δ hδ)
    (fun _ ↦ zero_le) fun m ↦ measure_mono fun ω (hω : δ ≤ _) ↦ ?_
  exact hω.trans (lintegral_mono' hle le_rfl)

private theorem stoppedProcess_dyadicCeilTime
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hτ : IsStoppingTime ℱ τ) (d : ℕ) :
    IsItoIntegral ℱ P W
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H t ω else 0)
      (stoppedProcess I (fun ω ↦ dyadicCeilTime d (τ ω))) := by
  let σ (ω : Ω) := dyadicCeilTime d (τ ω)
  refine ⟨hI.isStronglyPredictable.ite_le (hτ.dyadicCeilTime d),
    hI.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess, fun T ↦ ?_⟩
  obtain ⟨n, g, a, hg, ha, hE, _⟩ := hI.exists_seq_approx T
  choose N r b hr hb hhold hgains using fun m ↦
    exists_simpleHolding_stopped_dyadicCeilTime (W := W) hτ d T (hg m) (ha m)
  refine ⟨N, r, b, hr, hb, fun ε hε ↦ ?_, fun ε hε ↦ ?_⟩
  · have hsub (m : ℕ) :
        {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (r m) (N m) (b m) s ω -
          (if (s : WithTop ℝ≥0) ≤ σ ω then H s ω else 0)‖ₑ ^ 2 ∂Probability.timeMeasure T} ⊆
        {ω | ε ≤ ∫⁻ s, ‖Finance.simpleHolding (g m) (n m) (a m) s ω - H s ω‖ₑ ^ 2
          ∂Probability.timeMeasure T} := fun ω hω ↦ by
      refine hω.trans (lintegral_mono_ae ?_)
      filter_upwards [Probability.ae_mem_Ioc_timeMeasure T] with s hs
      rw [hhold m s hs ω]
      by_cases hsσ : (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω)
      · rw [ite_eq_left hsσ, ite_eq_left hsσ]
      · rw [ite_eq_right hsσ, ite_eq_right hsσ, sub_self, eNorm_zero, zero_pow (by norm_num)]
        exact zero_le
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hE ε hε)
      (fun _ ↦ zero_le) fun m ↦ measure_mono (hsub m)
  · let S : Finset ℝ≥0 := (range (dyadicCount d T + 1)).image (dyadicGrid d T)
    have hv_lim (v : ℝ≥0) (hv : v ∈ S) : Tendsto
        (fun m ↦ P {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)})
        atTop (𝓝 0) := by
      have hvT : v ≤ T := by
        obtain ⟨k, _, rfl⟩ := mem_image.1 hv
        exact min_le_right _ _
      exact tendstoInMeasure_simpleGains_of_le hW hI hvT hg ha hE ε hε
    have hsum : Tendsto (fun m ↦ ∑ v ∈ S,
        P {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)})
        atTop (𝓝 0) := by
      simpa only [sum_const_zero] using tendsto_finsetSum S hv_lim
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ ↦ zero_le) fun m ↦ ?_
    have hsub : {ω | ε ≤ edist (Finance.simpleGains (r m) (N m) (b m) W T ω)
        (stoppedProcess I σ T ω)} ⊆
        ⋃ v ∈ S,
          {ω | ε ≤ edist (Finance.simpleGains (g m) (n m) (a m) W v ω) (I v ω)} := by
      intro ω hω
      obtain ⟨hK_le, hK_eq, -⟩ := dyadicStopIndex_spec d T (τ ω)
      refine mem_biUnion (mem_image.2 ⟨dyadicStopIndex d T (τ ω),
        mem_range.2 (Nat.lt_succ_of_le hK_le), hK_eq⟩) ?_
      simpa only [mem_ofPred_eq, hgains m ω, stoppedProcess] using hω
    exact (measure_mono hsub).trans (measure_biUnion_finset_le S _)

private theorem tendsto_lintegral_dyadicCeilTime {μ : Measure ℝ≥0} {f : ℝ≥0 → ℝ} {u : WithTop ℝ≥0}
    (hf : Measurable f) (hfin : ∫⁻ s, ‖f s‖ₑ ^ 2 ∂μ ≠ ∞) :
    Tendsto (fun d ↦ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u then f s else 0) -
        (if (s : WithTop ℝ≥0) ≤ u then f s else 0)‖ₑ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hset (v : WithTop ℝ≥0) : MeasurableSet {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ v} := by
    cases v with
    | top =>
      have heq : {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ ⊤} = univ :=
        eq_univ_of_forall fun _ ↦ mem_ofPred.2 le_top
      exact heq ▸ MeasurableSet.univ
    | coe r =>
      have heq : {s : ℝ≥0 | (s : WithTop ℝ≥0) ≤ (r : WithTop ℝ≥0)} = Iic r :=
        Set.ext fun _ ↦ WithTop.coe_le_coe
      exact heq ▸ measurableSet_Iic
  have hmeas (d : ℕ) : Measurable (fun s : ℝ≥0 ↦
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u then f s else 0) -
        (if (s : WithTop ℝ≥0) ≤ u then f s else 0)‖ₑ ^ 2) :=
    ((Measurable.ite (hset _) hf measurable_const).sub
      (Measurable.ite (hset _) hf measurable_const)).eNorm.pow_const 2
  have hpt (s : ℝ≥0) : Tendsto (fun d ↦
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d u then f s else 0) -
        (if (s : WithTop ℝ≥0) ≤ u then f s else 0)‖ₑ ^ 2) atTop (𝓝 0) := by
    by_cases hs : (s : WithTop ℝ≥0) ≤ u
    · refine tendsto_const_nhds.congr fun d ↦ ?_
      rw [ite_eq_left (hs.trans (le_dyadicCeilTime d u)), ite_eq_left hs, sub_self,
        eNorm_zero, zero_pow (by norm_num)]
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [(tendsto_dyadicCeilTime u).eventually
        (eventually_lt_nhds (not_le.1 hs))] with d hd
      rw [ite_eq_right hd.not_ge, ite_eq_right hs, sub_self, eNorm_zero, zero_pow (by norm_num)]
  simpa using tendsto_lintegral_of_dominated_convergence (fun s ↦ ‖f s‖ₑ ^ 2) hmeas
    (fun d ↦ .of_forall fun s ↦ by
      dsimp only
      by_cases hs : (s : WithTop ℝ≥0) ≤ u
      · rw [ite_eq_left (hs.trans (le_dyadicCeilTime d u)), ite_eq_left hs, sub_self,
          eNorm_zero, zero_pow (by norm_num)]
        exact zero_le
      · rw [ite_eq_right hs, sub_zero]
        split_ifs <;> simp)
    hfin (.of_forall hpt)

private theorem tendsto_measure_lintegral_dyadicCeilTime [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (hτ : IsStoppingTime ℱ τ)
    (T : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun d ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H s ω else 0) -
        (if (s : WithTop ℝ≥0) ≤ τ ω then H s ω else 0)‖ₑ ^ 2
      ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  let F (d : ℕ) (s : ℝ≥0) (ω : Ω) : ℝ≥0∞ :=
    ‖(if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then H s ω else 0) -
      (if (s : WithTop ℝ≥0) ≤ τ ω then H s ω else 0)‖ₑ ^ 2
  let E (d : ℕ) (ω : Ω) : ℝ≥0∞ := ∫⁻ s, F d s ω ∂Probability.timeMeasure T
  have hF_meas (d : ℕ) : Measurable (fun p : ℝ≥0 × Ω ↦ F d p.1 p.2) :=
    (((hH.isStronglyPredictable.ite_le (hτ.dyadicCeilTime d)).sub
      (hH.isStronglyPredictable.ite_le hτ)).mono ℱ.predictable_le_prod).measurable.eNorm
      |>.pow_const 2
  have hanti : Antitone (fun d ↦ {ω | ε ≤ E d ω}) := fun d₁ d₂ hd ω (hω : ε ≤ E d₂ ω) ↦ by
    refine hω.trans (lintegral_mono fun s ↦ ?_)
    have hsd : dyadicCeilTime d₂ (τ ω) ≤ dyadicCeilTime d₁ (τ ω) :=
      antitone_dyadicCeilTime (τ ω) hd
    by_cases hsτ : (s : WithTop ℝ≥0) ≤ τ ω
    · dsimp only [F]
      rw [ite_eq_left (hsτ.trans (le_dyadicCeilTime d₂ (τ ω))), ite_eq_left hsτ, sub_self,
        eNorm_zero, zero_pow (by norm_num)]
      exact zero_le
    · by_cases hsd₂ : (s : WithTop ℝ≥0) ≤ dyadicCeilTime d₂ (τ ω)
      · dsimp only [F]
        rw [ite_eq_left hsd₂, ite_eq_left (hsd₂.trans hsd)]
      · dsimp only [F]
        rw [ite_eq_right hsd₂, ite_eq_right hsτ, sub_self, eNorm_zero, zero_pow (by norm_num)]
        exact zero_le
  have hH_meas : Measurable (Function.uncurry H) :=
    (hH.isStronglyPredictable.mono ℱ.predictable_le_prod).measurable
  have hae_lim : ∀ᵐ ω ∂P, Tendsto (fun d ↦ E d ω) atTop (𝓝 0) := by
    filter_upwards [hH.ae_memLp] with ω hω
    have hm := hω T
    rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def] at hm
    exact tendsto_lintegral_dyadicCeilTime (u := τ ω) (hH_meas.comp measurable_prodMk_right)
      (hm.aestronglyMeasurable.memLp_two_iff_lintegral_enorm_sq_lt_top.1 hm).ne
  have hsub : (⋂ d, {ω | ε ≤ E d ω}) ⊆ {ω | ¬ Tendsto (fun d ↦ E d ω) atTop (𝓝 0)} :=
    fun ω hω hlim ↦ by
      obtain ⟨d, hd⟩ := (hlim.eventually (eventually_lt_nhds hε)).exists
      exact hd.not_ge (mem_iInter.1 hω d)
  have hnull : P (⋂ d, {ω | ε ≤ E d ω}) = 0 := measure_mono_null hsub (ae_iff.1 hae_lim)
  have hlim := tendsto_measure_iInter_atTop (s := fun d ↦ {ω | ε ≤ E d ω})
    (fun d ↦ ((hF_meas d).lintegral_prod_left' measurableSet_Ici).nullMeasurableSet)
    hanti ⟨0, measure_ne_top P _⟩
  simpa only [Function.comp_def, hnull, E, F] using hlim

private theorem brownianIntegrable_ite_le_energyLocalizer [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (n : ℕ) :
    BrownianIntegrable ℱ P
      (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω then
        H t ω else 0) := by
  let τn := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  have hτn : IsStoppingTime ℱ τn :=
    (hH.isLocalizingSequence_energyLocalizer).isStoppingTime n
  refine (hH.isStronglyPredictable.brownianIntegrable_ite_le_energyLocalizer
    ((n : ℝ≥0) + 1)).congr (hH.isStronglyPredictable.ite_le hτn) fun T ↦ ?_
  have htime : ∀ᵐ t ∂(volume.restrict (Ioc 0 (T : ℝ))).comap ((↑) : ℝ≥0 → ℝ), t ∈ Iic T := by
    rw [NNReal.comap_volume_restrict_Ioc, ← Probability.timeMeasure_def]
    exact (Probability.ae_mem_Ioc_timeMeasure T).mono fun _ ht ↦ ht.2
  filter_upwards [Measure.quasiMeasurePreserving_fst.tendsto_ae htime,
    Measure.quasiMeasurePreserving_snd.tendsto_ae hH.ae_accumulatedEnergy_lt_top] with p ht hfin
  dsimp only [Function.uncurry]
  have hcut : nnvolume.finiteEnergyCutoff H p.1 p.2 = H p.1 p.2 :=
    nnvolume.finiteEnergyCutoff_eqOn (hfin T) ht
  rw [hcut]

private theorem tendsto_measure_energyLocalizer_le [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (T : ℝ≥0) :
    Tendsto (fun n : ℕ ↦ P {ω | nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω ≤ T})
      atTop (𝓝 0) := by
  have hτ := hH.isLocalizingSequence_energyLocalizer
  let s (n : ℕ) : Set Ω := {ω | nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω ≤ T}
  have hsub : (⋂ n, s n) ⊆ {ω | ¬ Tendsto (fun n : ℕ ↦
      nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω) atTop (𝓝 ⊤)} := fun ω hω hlim ↦ by
    obtain ⟨n, hn⟩ := ((WithTop.tendsto_nhds_top_iff _).1 hlim T).exists
    exact hn.not_ge (mem_iInter.1 hω n)
  have hnull : P (⋂ n, s n) = 0 := measure_mono_null hsub (ae_iff.1 hτ.tendsto_top)
  have hlim := tendsto_measure_iInter_atTop (s := s)
    (fun n ↦ (ℱ.le T _ (hτ.isStoppingTime n T)).nullMeasurableSet)
    (fun i j hij ω (hω : nnvolume.energyLocalizer H ((j : ℝ≥0) + 1) ω ≤ T) ↦
      (nnvolume.monotone_energyLocalizer H ω
        (by exact_mod_cast Nat.add_le_add_right hij 1)).trans hω)
    ⟨0, measure_ne_top P _⟩
  simpa only [Function.comp_def, hnull, s] using hlim

private theorem tendsto_measure_lintegral_energyLocalizer [IsFiniteMeasure P]
    (hH : LocallyBrownianIntegrable ℱ P H) (T : ℝ≥0) {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ P {ω | ε ≤ ∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω then H s ω else 0) -
        H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T}) atTop (𝓝 0) := by
  have hτ := hH.isLocalizingSequence_energyLocalizer
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (tendsto_measure_energyLocalizer_le hH T) (fun _ ↦ zero_le) fun n ↦
    measure_mono fun ω (hω : ε ≤ _) ↦ ?_
  by_contra hnot
  have hgt : (T : WithTop ℝ≥0) < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω := not_le.1 hnot
  have hzero : (∫⁻ s,
      ‖(if (s : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω then H s ω else 0) -
        H s ω‖ₑ ^ 2 ∂Probability.timeMeasure T) = 0 := by
    refine (lintegral_eq_zero_iff' ?_).2 ?_
    · exact ((((hH.isStronglyPredictable.ite_le (hτ.isStoppingTime n)).sub
        hH.isStronglyPredictable).mono ℱ.predictable_le_prod).measurable.eNorm.pow_const 2
        |>.comp measurable_prodMk_right).aemeasurable
    · filter_upwards [Probability.ae_mem_Ioc_timeMeasure T] with s hs
      have hsτ : (s : WithTop ℝ≥0) ≤ nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω :=
        (WithTop.coe_le_coe.2 hs.2).trans hgt.le
      rw [Pi.zero_apply, ite_eq_left hsτ, sub_self, eNorm_zero, zero_pow (by norm_num)]
  exact hε.not_ge (hzero ▸ hω)

namespace IsItoIntegral

/-- **Stopping an Itô integral.** Against a filtered pre-Brownian motion, stopping an Itô integral
at a stopping time `τ` on the raw filtration yields an Itô integral of the cutoff integrand
`H · 1_{[0, τ]}`. Neither path continuity of `W` nor adaptation of `I` is needed. -/
theorem stoppedProcess (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hτ : IsStoppingTime ℱ τ) :
    IsItoIntegral ℱ P W (fun t ω ↦ if (t : WithTop ℝ≥0) ≤ τ ω then H t ω else 0)
      (MeasureTheory.stoppedProcess I τ) := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hId (d : ℕ) := stoppedProcess_dyadicCeilTime hW hI hτ d
  have hWm (s : ℝ≥0) : AEStronglyMeasurable (W s) P :=
    ((hW.martingale.stronglyAdapted s).mono (ℱ.le s)).aestronglyMeasurable
  refine of_seq (hI.isStronglyPredictable.ite_le hτ)
    (hI.ae_continuous.mono fun _ hc ↦ hc.stoppedProcess) hId
    (fun T _ hε ↦ tendsto_measure_lintegral_dyadicCeilTime hI.locallyBrownianIntegrable hτ T hε)
    fun T ↦ tendstoInMeasure_of_tendsto_ae (fun d ↦ (hId d).aestronglyMeasurable hWm T) ?_
  filter_upwards [hI.ae_continuous] with ω hω
  exact tendsto_stoppedProcess_dyadicCeilTime I τ T ω hω.continuousAt.continuousWithinAt

/-- **Local congruence of Itô integrals.** Two Itô integrals whose integrands agree
`(timeMeasure T).prod P`-almost everywhere on `[0, τ]` have indistinguishable stopped processes
at `τ`. -/
theorem stoppedProcess_indist_of_ae_eq (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hJ : IsItoIntegral ℱ P W K J)
    (hτ : IsStoppingTime ℱ τ)
    (hHK : ∀ T : ℝ≥0, ∀ᵐ p ∂(Probability.timeMeasure T).prod P,
      (p.1 : WithTop ℝ≥0) ≤ τ p.2 → H p.1 p.2 = K p.1 p.2) :
    MeasureTheory.stoppedProcess I τ ≡ᵐ[P] MeasureTheory.stoppedProcess J τ := by
  refine (hI.stoppedProcess hW hτ).indist_of_ae_eq_prod hW (hJ.stoppedProcess hW hτ) fun T ↦ ?_
  filter_upwards [hHK T] with p hp
  dsimp only [Function.uncurry]
  split_ifs with h
  · exact hp h
  · rfl

/-- **Local martingale property of the Itô integral.** Every strongly progressive Itô integral
against a filtered pre-Brownian motion is a native local martingale on the raw filtration. -/
theorem locally_martingale (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hI : IsItoIntegral ℱ P W H I) (hProg : IsStronglyProgressive ℱ I) :
    Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  have hH := hI.locallyBrownianIntegrable
  have hτ := hH.isLocalizingSequence_energyLocalizer
  have hMart (n : ℕ) : Martingale
      (MeasureTheory.stoppedProcess I (nnvolume.energyLocalizer H ((n : ℝ≥0) + 1))) ℱ P :=
    (hI.stoppedProcess hW (hτ.isStoppingTime n)).martingale hW
      (brownianIntegrable_ite_le_energyLocalizer hH n)
      (hProg.stoppedProcess (hτ.isStoppingTime n)).stronglyAdapted
  refine hProg.locally_martingale_of_ae_stopped_eq hτ hMart fun n t ↦ .of_forall fun ω ↦ ?_
  have hpos : ω ∈ {ω | (⊥ : WithTop ℝ≥0) < nnvolume.energyLocalizer H ((n : ℝ≥0) + 1) ω} :=
    nnvolume.energyLocalizer_pos H (by positivity : (0 : ℝ≥0) < n + 1) ω
  rw [stoppedProcess_indicator_comm']
  exact (Set.indicator_of_mem hpos _).symm

end IsItoIntegral

/-- **Existence of the localized Brownian Itô integral process.** Against a filtered pre-Brownian
motion `W` with almost surely continuous paths, every `LocallyBrownianIntegrable` integrand admits
a predictable almost surely continuous local-martingale Itô integral on the raw filtration. -/
theorem LocallyBrownianIntegrable.exists_isItoIntegral
    (hW : Probability.IsFilteredPreBrownianReal ℱ W P)
    (hcont : ∀ᵐ ω ∂P, Continuous (fun t ↦ W t ω))
    (hH : LocallyBrownianIntegrable ℱ P H) :
    ∃ I : ℝ≥0 → Ω → ℝ, IsItoIntegral ℱ P W H I ∧ IsStronglyPredictable ℱ I ∧
      Locally (fun U ↦ Martingale U ℱ P) ℱ I P := by
  have : IsProbabilityMeasure P := (hW.hasLaw_eval 0).isProbabilityMeasure
  let τn (n : ℕ) := nnvolume.energyLocalizer H ((n : ℝ≥0) + 1)
  have hτ := hH.isLocalizingSequence_energyLocalizer
  choose U hU_ito hU_pred _ using fun n ↦
    (brownianIntegrable_ite_le_energyLocalizer hH n).exists_isItoIntegral hW hcont
  have hcompat (n m : ℕ) (hnm : n ≤ m) :
      MeasureTheory.stoppedProcess (U m) (τn n) ≡ᵐ[P] U n := by
    refine ((hU_ito m).stoppedProcess hW (hτ.isStoppingTime n)).indist_of_ae_eq hW (hU_ito n)
      fun _ ↦ .of_forall fun ω ↦ .of_forall fun t ↦ ?_
    have hmono : τn n ω ≤ τn m ω :=
      nnvolume.monotone_energyLocalizer H ω (by exact_mod_cast Nat.add_le_add_right hnm 1)
    dsimp only
    by_cases ht : (t : WithTop ℝ≥0) ≤ τn n ω
    · have htm : (t : WithTop ℝ≥0) ≤ τn m ω := ht.trans hmono
      dsimp only [τn] at ht htm
      rw [ite_eq_left ht, ite_eq_left htm, ite_eq_left ht]
    · dsimp only [τn] at ht
      rw [ite_eq_right ht, ite_eq_right ht]
  obtain ⟨X, hX_prog, hX_cont, hX_stop⟩ := exists_isStronglyProgressive_patch_stoppedProcess
    hτ.tendsto_top (fun n ↦ (hU_pred n).isStronglyProgressive)
    (fun n ↦ (hU_ito n).ae_continuous) hcompat
  obtain ⟨I, hI_pred, hIX⟩ :=
    hX_prog.stronglyAdapted.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
      (hX_cont.mono fun _ hc ↦ hc.isLeftContinuous)
  have hI_cont : ∀ᵐ ω ∂P, Continuous (fun t ↦ I t ω) := by
    filter_upwards [hX_cont, hIX] with ω hc hω using hc.congr (fun t ↦ (hω t).symm)
  have hI_ito : IsItoIntegral ℱ P W H I := by
    refine IsItoIntegral.of_seq hH.isStronglyPredictable hI_cont hU_ito
      (fun T _ hε ↦ tendsto_measure_lintegral_energyLocalizer hH T hε) fun T ↦ ?_
    refine tendstoInMeasure_of_tendsto_ae
      (fun n ↦ ((hU_pred n).isStronglyProgressive.stronglyAdapted T
        |>.mono (ℱ.le T)).aestronglyMeasurable) ?_
    filter_upwards [hτ.tendsto_top, hIX, ae_all_iff.2 hX_stop] with ω hlim hIXω hstop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(WithTop.tendsto_nhds_top_iff _).1 hlim T] with n hn
    rw [← hstop n T, stoppedProcess_eq_of_le hn.le, hIXω T]
  exact ⟨I, hI_ito, hI_pred, hI_ito.locally_martingale hW hI_pred.isStronglyProgressive⟩

end TauCeti
