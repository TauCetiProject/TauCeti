/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.SimpleStrategy.Basic
public import TauCeti.Probability.Finance.SimpleStrategy.Refinement
public import TauCeti.Probability.Process.StoppingApproximation
import TauCeti.Probability.Finance.SimpleStrategy.Associativity
import TauCeti.Probability.Process.Stopping

/-!
# Dyadic stopping of simple trading strategies

Stopping a left-measurable simple strategy on a nondecreasing grid at `dyadicCeilTime k ∘ τ` up to
horizon `T`, where `τ` is a stopping time for the same filtration as the input strategy, produces a
left-measurable simple strategy on a strictly increasing deterministic grid starting at `0`, with
holding `1_{t ≤ dyadicCeilTime k (τ ω)}` times the original holding on `(0, T]` and gains equal
to `stoppedProcess (simpleGains σ n a X) (dyadicCeilTime k ∘ τ) s` for all `s ≤ T`.

On a horizon `T`, holding one unit on step `k` of `dyadicGrid d T` when
`dyadicGrid d T k < dyadicCeilTime d (τ ω)` realizes `1_{[0, dyadicCeilTime d (τ ω)]}` on `(0, T]`
(`simpleHolding_dyadicGrid_ite_lt`), with gains `stoppedProcess X (dyadicCeilTime d ∘ τ) s - X 0`
at `s ≤ T` (`simpleGains_dyadicGrid_ite_lt`). Combining this with associativity and refinement
represents any stopped left-measurable simple strategy throughout `[0, T]`, universally across `W`,
on one strictly increasing grid starting at `0` with bounded heights
(`exists_simpleHolding_simpleGains_stoppedProcess_dyadicCeilTime`), while
`exists_simpleHolding_simpleGains_dyadicCeilTime` gives the corresponding representation on the
`dyadicNNRat` grid.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, 2nd ed., 2005, §II.2.
* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., 1991, §3.2.D.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open Set hiding mem_range
open Finset hiding Iic mem_Iic Ioc mem_Ioc
open scoped NNReal

namespace TauCeti.Finance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {τ : Ω → WithTop ℝ≥0}

/-- On `(0, T]`, holding one unit on step `k` of `dyadicGrid d T` whenever
`dyadicGrid d T k < dyadicCeilTime d (τ ω)` equals the indicator of
`[0, dyadicCeilTime d (τ ω)]`. -/
theorem simpleHolding_dyadicGrid_ite_lt (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    {s : ℝ≥0} (hs : s ∈ Ioc 0 T) (ω : Ω) :
    simpleHolding (dyadicGrid d T) (dyadicCount d T)
      (fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
      s ω = if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then 1 else 0 := by
  obtain ⟨k, hk, hsk⟩ := exists_lt_mem_Ioc_of_mem_Ioc
    (by simpa only [dyadicGrid_zero, dyadicGrid_count] using hs :
      s ∈ Ioc (dyadicGrid d T 0) (dyadicGrid d T (dyadicCount d T)))
  rw [simpleHolding_of_mem_Ioc ((monotone_dyadicGrid d T).monotoneOn _) hk hsk]
  simp only [coe_le_dyadicCeilTime_iff_of_mem_Ioc d T (τ ω) hk hsk]

/-- At every time `s ≤ T`, the elementary gains of the unit cutoff strategy on `dyadicGrid d T`
against any process `X` equal the stopped increment
`stoppedProcess X (dyadicCeilTime d ∘ τ) s - X 0`. -/
theorem simpleGains_dyadicGrid_ite_lt (d : ℕ) (T : ℝ≥0) (τ : Ω → WithTop ℝ≥0)
    {s : ℝ≥0} (hs : s ≤ T) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    simpleGains (dyadicGrid d T) (dyadicCount d T)
      (fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
      X s ω = stoppedProcess X (fun ω ↦ dyadicCeilTime d (τ ω)) s ω - X 0 ω := by
  let K := dyadicStopIndex d T (τ ω)
  have hfilter : (range (dyadicCount d T)).filter (· < K) = range K := by
    ext k; have := dyadicStopIndex_le d T (τ ω); simp only [mem_filter, mem_range, K]; omega
  have hcongr : simpleGains (dyadicGrid d T) (dyadicCount d T)
      (fun k ω ↦ if (dyadicGrid d T k : WithTop ℝ≥0) < dyadicCeilTime d (τ ω) then 1 else 0)
      X s ω = ∑ k ∈ range K, (X (min (dyadicGrid d T (k + 1)) s) ω -
        X (min (dyadicGrid d T k) s) ω) := by
    rw [simpleGains_def, ← hfilter, sum_filter]
    exact sum_congr rfl fun k hk ↦ by
      simp only [dyadicGrid_lt_dyadicCeilTime_iff d T (τ ω) (mem_range.1 hk), K]; split_ifs <;> simp
  rw [hcongr, sum_range_sub (fun k ↦ X (min (dyadicGrid d T k) s) ω), dyadicGrid_zero,
    min_eq_left (zero_le : 0 ≤ s)]
  congr 1
  rw [min_comm, eval_dyadicGrid_dyadicStopIndex (fun r ↦ X (min s r)), stoppedProcess_const_min]
  simp only [min_eq_left hs]

/-- Stopping a left-measurable simple strategy at the dyadic ceiling `dyadicCeilTime d ∘ τ` of a raw
stopping time `τ` is represented throughout `[0, T]` — both for its holdings and for its elementary
gains against every price process `W` — by a single strictly increasing deterministic-grid
left-measurable simple strategy starting at `0` whose heights are bounded pointwise by the sum of
the original absolute heights. -/
theorem exists_simpleHolding_simpleGains_stoppedProcess_dyadicCeilTime {τ : Ω → WithTop ℝ≥0}
    (hτ : IsStoppingTime ℱ τ) (d : ℕ) (T : ℝ≥0) {n : ℕ} {g : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hg : MonotoneOn g (Iic n)) (ha : ∀ j < n, StronglyMeasurable[ℱ (g j)] (a j)) :
    ∃ (N : ℕ) (r : ℕ → ℝ≥0) (b : ℕ → Ω → ℝ),
      r 0 = 0 ∧ StrictMonoOn r (Iic N) ∧ (∀ i < N, StronglyMeasurable[ℱ (r i)] (b i)) ∧
      (∀ i < N, ∀ ω, ‖b i ω‖ ≤ ∑ j ∈ range n, ‖a j ω‖) ∧
      (∀ s ≤ T, ∀ ω, simpleHolding r N b s ω =
        if (s : WithTop ℝ≥0) ≤ dyadicCeilTime d (τ ω) then simpleHolding g n a s ω else 0) ∧
      ∀ (W : ℝ≥0 → Ω → ℝ), ∀ s ≤ T, ∀ ω, simpleGains r N b W s ω =
        stoppedProcess (simpleGains g n a W) (fun ω ↦ dyadicCeilTime d (τ ω)) s ω := by
  let q := dyadicGrid d T
  let σ (ω : Ω) := dyadicCeilTime d (τ ω)
  let u (k : ℕ) (ω : Ω) : ℝ := if (q k : WithTop ℝ≥0) < σ ω then 1 else 0
  let s_idx : Finset (ℕ × ℕ) := range (dyadicCount d T) ×ˢ range n
  let l (p : ℕ × ℕ) : ℝ≥0 := max (g p.2) (q p.1)
  have hc : ∀ p ∈ s_idx, StronglyMeasurable[ℱ (l p)] (fun ω ↦ u p.1 ω * a p.2 ω) := fun p hp ↦
    (StronglyMeasurable.ite (ℱ.mono (le_max_right _ _) _
      ((hτ.dyadicCeilTime d).measurableSet_gt (q p.1))) stronglyMeasurable_const
      stronglyMeasurable_const).mul
      ((ha p.2 (mem_range.1 (mem_product.1 hp).2)).mono (ℱ.mono (le_max_left _ _)))
  obtain ⟨N, r, b, hr0, hr, -, -, hb, -, -, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ s_idx l
      (fun p ↦ min (g (p.2 + 1)) (q (p.1 + 1))) (fun p ω ↦ u p.1 ω * a p.2 ω) hc
  refine ⟨N, r, b, hr0, hr, fun i _ ↦ hb i, fun i hi_lt ω ↦ ?_, fun s hs ω ↦ ?_,
    fun W s hs ω ↦ ?_⟩
  · have hbi : b i ω = simpleHolding q (dyadicCount d T) u (r (i + 1)) ω *
        simpleHolding g n a (r (i + 1)) ω := by
      rw [← simpleHolding_of_mem_Ioc (a := b) hr.monotoneOn hi_lt
        ⟨hr hi_lt.le hi_lt (Nat.lt_succ_self i), le_rfl⟩ ω, hhold, sum_product,
        ← simpleHolding_mul_eq_sum]
    have hu_le : ‖simpleHolding q (dyadicCount d T) u (r (i + 1)) ω‖ ≤ 1 := by
      by_cases hq : r (i + 1) ∈ Ioc (q 0) (q (dyadicCount d T))
      · obtain ⟨k, hk, hkq⟩ := exists_lt_mem_Ioc_of_mem_Ioc hq
        rw [simpleHolding_of_mem_Ioc ((monotone_dyadicGrid d T).monotoneOn _) hk hkq]
        dsimp only [u]; split_ifs <;> simp
      · rw [simpleHolding_of_notMem_Ioc ((monotone_dyadicGrid d T).monotoneOn _) hq]; simp
    have ha_le : ‖simpleHolding g n a (r (i + 1)) ω‖ ≤ ∑ j ∈ range n, ‖a j ω‖ := by
      rw [simpleHolding_def]
      exact (norm_sum_le _ _).trans (sum_le_sum fun _ _ ↦ norm_indicator_le_norm_self _ _)
    rw [hbi, norm_mul]
    exact (mul_le_mul hu_le ha_le (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · rcases eq_or_lt_of_le (zero_le : 0 ≤ s) with rfl | hs0
    · simp only [simpleHolding_def, Set.mem_Ioc, not_lt_zero, false_and, not_false_eq_true,
        indicator_of_notMem, sum_const_zero, ite_self]
    · rw [hhold, sum_product, ← simpleHolding_mul_eq_sum,
        simpleHolding_dyadicGrid_ite_lt d T τ ⟨hs0, hs⟩]; split_ifs <;> simp
  · rw [hgains, sum_product,
      ← simpleGains_simpleGains_eq_sum hg ((monotone_dyadicGrid d T).monotoneOn _),
      simpleGains_dyadicGrid_ite_lt d T τ hs, simpleGains_of_le hg zero_le, sub_zero]

private noncomputable def dyadicStopHeight (τ : Ω → WithTop ℝ≥0) (k j : ℕ) (ω : Ω) : ℝ :=
  if ((dyadicNNRat k j : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) then 1 else 0

private theorem stronglyMeasurable_dyadicStopHeight (hτ : IsStoppingTime ℱ τ) (k j : ℕ) :
    StronglyMeasurable[ℱ (dyadicNNRat k j : ℝ≥0)] (dyadicStopHeight τ k j) :=
  stronglyMeasurable_const.ite (by
    convert (hτ.dyadicCeilTime k (dyadicNNRat k j : ℝ≥0)).compl using 1
    ext; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]; exact lt_iff_not_ge)
    stronglyMeasurable_const

private theorem simpleHolding_dyadicStopHeight {T t : ℝ≥0} (ht : t ∈ Ioc 0 T) (k : ℕ) (ω : Ω) :
    simpleHolding (fun j ↦ (dyadicNNRat k j : ℝ≥0)) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) t ω =
      if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then 1 else 0 := by
  let j : ℕ := ⌈t * 2 ^ k⌉₊ - 1
  have hpos : 0 < ⌈t * 2 ^ k⌉₊ := Nat.ceil_pos.mpr (mul_pos ht.1 (by positivity))
  have hj1 : j + 1 = ⌈t * 2 ^ k⌉₊ := Nat.sub_add_cancel hpos
  have hjM : j < ⌈T * 2 ^ k⌉₊ :=
    lt_of_lt_of_le (by omega) (Nat.ceil_mono (mul_le_mul_of_nonneg_right ht.2 (by positivity)))
  have hmem : t ∈ Ioc (dyadicNNRat k j : ℝ≥0) (dyadicNNRat k (j + 1) : ℝ≥0) := by
    simp only [coe_dyadicNNRat]
    exact ⟨(div_lt_iff₀ (by positivity)).2 (Nat.lt_ceil.1 (by omega)),
      (le_div_iff₀ (by positivity)).2 (hj1 ▸ Nat.le_ceil _)⟩
  rw [simpleHolding_of_mem_Ioc ((strictMono_coe_dyadicNNRat k).monotone.monotoneOn _) hjM hmem,
    dyadicStopHeight]
  refine if_congr ?_ rfl rfl
  cases τ ω with
  | top => simp only [dyadicCeilTime_top, WithTop.coe_lt_top, le_top]
  | coe s =>
    simp only [dyadicCeilTime_coe, WithTop.coe_lt_coe, WithTop.coe_le_coe, coe_dyadicNNRat]
    rw [div_lt_div_iff_of_pos_right (by positivity), le_div_iff₀ (by positivity), Nat.cast_lt,
      ← Nat.ceil_le, ← hj1]
    omega

private theorem simpleGains_dyadicStopHeight {G : ℝ≥0 → Ω → ℝ} {T s : ℝ≥0} (hs : s ≤ T) {ω : Ω}
    (hG0 : G 0 ω = 0) (k : ℕ) :
    simpleGains (fun j ↦ (dyadicNNRat k j : ℝ≥0)) ⌈T * 2 ^ k⌉₊ (dyadicStopHeight τ k) G s ω =
      MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let f (j : ℕ) : ℝ := G (min (dyadicNNRat k j : ℝ≥0) s) ω
  have hf0 : f 0 = 0 := by simp [f, hG0]
  have hsM : s ≤ (dyadicNNRat k M : ℝ≥0) := by
    rw [coe_dyadicNNRat]
    exact hs.trans ((le_div_iff₀ (by positivity)).2 (Nat.le_ceil _))
  rw [simpleGains_def]
  rcases le_or_gt (s : WithTop ℝ≥0) (dyadicCeilTime k (τ ω)) with hle | hgt
  · have hfM : f M = G s ω := by dsimp only [f]; rw [min_eq_right hsM]
    have hsum : G s ω = ∑ j ∈ range M, (f (j + 1) - f j) := by
      rw [sum_range_sub, hf0, hfM, sub_zero]
    rw [stoppedProcess_eq_of_le (τ := fun ω ↦ dyadicCeilTime k (τ ω)) hle, hsum]
    refine sum_congr rfl fun j _ ↦ ?_
    by_cases hdj : (dyadicNNRat k j : ℝ≥0) < s
    · rw [dyadicStopHeight, ite_eq_left ((WithTop.coe_lt_coe.mpr hdj).trans_le hle), one_mul]
    · have hge := le_of_not_gt hdj
      simp only [f, min_eq_right hge,
        min_eq_right (hge.trans ((strictMono_coe_dyadicNNRat k (Nat.lt_succ_self j)).le)),
        sub_self, mul_zero]
  · obtain ⟨u, -, hρ⟩ := exists_eq_coe_dyadicCeilTime_of_lt hgt
    let r : ℕ := ⌈u * 2 ^ k⌉₊
    have hrs : (dyadicNNRat k r : ℝ≥0) < s := WithTop.coe_lt_coe.mp (hρ ▸ hgt)
    have hrM : r ≤ M := ((strictMono_coe_dyadicNNRat k).lt_iff_lt.mp (hrs.trans_le hsM)).le
    have hfr : f r = MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
      rw [MeasureTheory.stoppedProcess_eq_of_ge (τ := fun ω ↦ dyadicCeilTime k (τ ω)) hgt.le,
        hρ, WithTop.untopA_eq_untop WithTop.coe_ne_top, WithTop.untop_coe]
      dsimp only [f]
      rw [min_eq_left hrs.le]
    have hfilt : (range M).filter (· < r) = range r := by
      ext j; simp only [mem_filter, Finset.mem_range]; omega
    have hsum : MeasureTheory.stoppedProcess G (fun ω ↦ dyadicCeilTime k (τ ω)) s ω =
        ∑ j ∈ range r, (f (j + 1) - f j) := by
      rw [sum_range_sub, hf0, hfr, sub_zero]
    rw [hsum, ← hfilt, sum_filter]
    refine sum_congr rfl fun j _ ↦ ?_
    have hiff : ((dyadicNNRat k j : ℝ≥0) : WithTop ℝ≥0) < dyadicCeilTime k (τ ω) ↔ j < r := by
      rw [hρ, WithTop.coe_lt_coe, (strictMono_coe_dyadicNNRat k).lt_iff_lt]
    rw [dyadicStopHeight, if_congr hiff rfl rfl]
    by_cases hjr : j < r <;> simp [hjr, f]

/-- Stopping a left-measurable simple strategy on a nondecreasing grid at the dyadic ceiling
`dyadicCeilTime k ∘ τ` of a stopping time `τ` up to horizon `T` is represented on `(0, T]` by one
strictly increasing deterministic grid starting at `0`, with left-measurable heights bounded
pathwise by `⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖` and gains at every `s ≤ T` equal to the
stopped gains against any price path `X`. -/
theorem exists_simpleHolding_simpleGains_dyadicCeilTime
    (hτ : IsStoppingTime ℱ τ) (k : ℕ) (T : ℝ≥0) {n : ℕ} {σ : ℕ → ℝ≥0} {a : ℕ → Ω → ℝ}
    (hσ : MonotoneOn σ (Iic n)) (ha : ∀ i < n, StronglyMeasurable[ℱ (σ i)] (a i)) :
    ∃ (N : ℕ) (γ : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ),
      γ 0 = 0 ∧ StrictMonoOn γ (Iic N) ∧
      (∀ j < N, StronglyMeasurable[ℱ (γ j)] (c j)) ∧
      (∀ j < N, ∀ ω, ‖c j ω‖ ≤ ⌈T * 2 ^ k⌉₊ * ∑ i ∈ range n, ‖a i ω‖) ∧
      (∀ t ∈ Ioc 0 T, ∀ ω, simpleHolding γ N c t ω =
        if (t : WithTop ℝ≥0) ≤ dyadicCeilTime k (τ ω) then simpleHolding σ n a t ω else 0) ∧
      ∀ (X : ℝ≥0 → Ω → ℝ) ⦃s : ℝ≥0⦄, s ≤ T → ∀ ω, simpleGains γ N c X s ω =
        MeasureTheory.stoppedProcess (simpleGains σ n a X)
          (fun ω ↦ dyadicCeilTime k (τ ω)) s ω := by
  let M : ℕ := ⌈T * 2 ^ k⌉₊
  let l (p : Fin M × Fin n) : ℝ≥0 := max (σ p.2.val) (dyadicNNRat k p.1.val : ℝ≥0)
  let u (p : Fin M × Fin n) : ℝ≥0 := min (σ (p.2.val + 1)) (dyadicNNRat k (p.1.val + 1) : ℝ≥0)
  let α (p : Fin M × Fin n) (ω : Ω) : ℝ := dyadicStopHeight τ k p.1.val ω * a p.2.val ω
  obtain ⟨N, γ, c, hγ0, hγ, -, -, hcm, -, hcb, hhold, hgains⟩ :=
    exists_simpleHolding_simpleGains_eq_sum ℱ (univ : Finset (Fin M × Fin n)) l u α fun p _ ↦
      ((stronglyMeasurable_dyadicStopHeight hτ k p.1.val).mono (ℱ.mono (le_max_right _ _))).mul
        ((ha p.2.val p.2.isLt).mono (ℱ.mono (le_max_left _ _)))
  refine ⟨N, γ, c, hγ0, hγ, fun j _ ↦ hcm j, fun j hj ω ↦ (hcb j hj ω).trans ?_,
    fun t ht ω ↦ ?_, fun X s hs ω ↦ ?_⟩
  · rw [Fintype.sum_prod_type]
    refine (sum_le_sum (g := fun _ ↦ ∑ i ∈ range n, ‖a i ω‖) fun _ _ ↦ ?_).trans_eq (by simp [M])
    rw [← Fin.sum_univ_eq_sum_range]
    refine sum_le_sum fun r _ ↦ ?_
    rw [norm_mul]; refine (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)).trans_eq (one_mul _)
    unfold dyadicStopHeight; split_ifs <;> norm_num
  · have hmul := simpleHolding_mul_eq_sum (ρ := fun j ↦ (dyadicNNRat k j : ℝ≥0)) (m := M)
      (b := dyadicStopHeight τ k) (τ := σ) (n := n) (a := a) t ω
    simp_rw [← Fin.sum_univ_eq_sum_range] at hmul
    rw [hhold t ω, Fintype.sum_prod_type, ← hmul, simpleHolding_dyadicStopHeight ht k ω]
    split_ifs <;> ring
  · have hg := simpleGains_simpleGains_eq_sum (X := X) hσ
      ((strictMono_coe_dyadicNNRat k).monotone.monotoneOn (Iic M))
      (b := dyadicStopHeight τ k) (a := a) s ω
    simp_rw [← Fin.sum_univ_eq_sum_range] at hg
    rw [hgains X s ω, Fintype.sum_prod_type, ← hg,
      simpleGains_dyadicStopHeight hs (simpleGains_of_le hσ bot_le X ω) k]

end TauCeti.Finance
