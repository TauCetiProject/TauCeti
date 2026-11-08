/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Detection of continuous level hits on dyadic grids

`TauCeti.gridLevelHit X c n` is the first dyadic time `k / 2^n` at which `c < X`.
It is a countable-range stopping time for every adapted process, even on a raw filtration.
The construction uses native `MeasureTheory.hittingAfter` on the discrete sampling index.

If a continuous path reaches a higher level at a finite time, all sufficiently fine grids
detect the lower level no later than that time. Consequently the probability of missing a
measurable higher-level barrier tends to zero. One can select a grid for each of countably
many lower levels so that the miss probabilities are summable. The barrier need not itself
be a stopping time: this distinction is useful for constructing raw-filtration localizers
from processes whose paths are continuous only almost surely.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Chapter 1, §§2 and 5.
-/

public section

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology

namespace TauCeti

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {c : ℝ} {n : ℕ} {t : ℝ≥0} {ω : Ω}

/-- First strict upper-level hit on the dyadic grid of mesh `2⁻ⁿ`, with infinity if no grid
point hits. Time zero is included. -/
def gridLevelHit (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) : WithTop ℝ≥0 :=
  WithTop.map (fun k : ℕ ↦ (k : ℝ≥0) / 2 ^ n)
    (hittingAfter (fun k ↦ X ((k : ℝ≥0) / 2 ^ n)) (Ioi c) 0 ω)

theorem gridLevelHit_def (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (n : ℕ) (ω : Ω) :
    gridLevelHit X c n ω = WithTop.map (fun k : ℕ ↦ (k : ℝ≥0) / 2 ^ n)
      (hittingAfter (fun k ↦ X ((k : ℝ≥0) / 2 ^ n)) (Ioi c) 0 ω) :=
  (rfl)

/-- A grid hit occurs by `t` exactly when some grid point by `t` is above the level. -/
theorem gridLevelHit_le_iff :
    gridLevelHit X c n ω ≤ t ↔ ∃ k : ℕ, (k : ℝ≥0) / 2 ^ n ≤ t ∧
      c < X ((k : ℝ≥0) / 2 ^ n) ω := by
  classical
  let h := hittingAfter (fun k : ℕ ↦ X ((k : ℝ≥0) / 2 ^ n)) (Ioi c) 0 ω
  have hle (k : ℕ) (hk : c < X ((k : ℝ≥0) / 2 ^ n) ω) : h ≤ k :=
    hittingAfter_le_of_mem (Nat.zero_le k) hk
  have heq : gridLevelHit X c n ω = WithTop.map (fun k : ℕ ↦ (k : ℝ≥0) / 2 ^ n) h :=
    gridLevelHit_def X c n ω
  rw [heq]
  cases hh : h using WithTop.recTopCoe with
  | top =>
    simp only [WithTop.map_top, WithTop.top_le_iff, WithTop.coe_ne_top,
      false_iff, not_exists, not_and]
    intro k _ hk
    have := hle k hk
    simp [hh] at this
  | coe j =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    constructor
    · intro hj
      have hd : h ≤ j := hh.le
      obtain ⟨k, hk, hhit⟩ := hittingAfter_le_iff.mp hd
      exact ⟨k, (div_le_div_of_nonneg_right (by exact_mod_cast hk.2)
        (by positivity)).trans hj, hhit⟩
    · rintro ⟨k, hkt, hk⟩
      have hjk : j ≤ k := by simpa [hh] using hle k hk
      exact (div_le_div_of_nonneg_right (by exact_mod_cast hjk) (by positivity)).trans hkt

/-- The sublevel event of a grid hit is the union of the strict upper-level sample events
at grid points no later than the given time. -/
theorem setOf_gridLevelHit_le_eq :
    {ω | gridLevelHit X c n ω ≤ t} =
      ⋃ k : ℕ, ⋃ (_ : (k : ℝ≥0) / 2 ^ n ≤ t),
        {ω | c < X ((k : ℝ≥0) / 2 ^ n) ω} := by
  ext ω
  simp only [mem_iUnion, mem_ofPred, exists_prop]
  exact gridLevelHit_le_iff

/-- No grid hit occurs exactly when every grid sample is at most the level. -/
@[simp]
theorem gridLevelHit_eq_top_iff : gridLevelHit X c n ω = ⊤ ↔
    ∀ k : ℕ, X ((k : ℝ≥0) / 2 ^ n) ω ≤ c := by
  rw [WithTop.eq_top_iff_forall_gt]
  constructor
  · intro h k
    by_contra hk
    exact (not_le_of_gt (h ((k : ℝ≥0) / 2 ^ n)))
      (gridLevelHit_le_iff.mpr ⟨k, le_rfl, lt_of_not_ge hk⟩)
  · intro h t
    apply lt_of_not_ge
    intro ht
    obtain ⟨k, _, hk⟩ := gridLevelHit_le_iff.mp ht
    exact (h k).not_gt hk

/-- Every grid hit takes values in a countable deterministic set. -/
theorem countable_range_gridLevelHit (X : ℝ≥0 → Ω → ℝ) (c : ℝ) (n : ℕ) :
    (Set.range (gridLevelHit X c n)).Countable := by
  exact (Set.countable_range (WithTop.map (fun k : ℕ ↦ (k : ℝ≥0) / 2 ^ n))).mono
    (Set.range_comp_subset_range _ _)

/-- Grid detection is a stopping time on the original filtration, without path regularity
or right continuity of that filtration. -/
theorem isStoppingTime_gridLevelHit {m : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 m}
    (hX : StronglyAdapted ℱ X) (c : ℝ) (n : ℕ) :
    IsStoppingTime ℱ (gridLevelHit X c n) := by
  intro t
  rw [setOf_gridLevelHit_le_eq]
  exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun hk ↦
    ((hX _).mono (ℱ.mono hk)).measurable measurableSet_Ioi

/-- Grid detection is ambient measurable when each deterministic-time sample is measurable. -/
theorem measurable_gridLevelHit {m : MeasurableSpace Ω}
    (hX : ∀ t, Measurable (X t)) (c : ℝ) (n : ℕ) : Measurable (gridLevelHit X c n) := by
  apply measurable_of_Iic
  intro u
  induction u using WithTop.recTopCoe with
  | top => simpa only [Iic_top, preimage_univ] using (MeasurableSet.univ :
      MeasurableSet (univ : Set Ω))
  | coe t =>
    simp only [preimage, mem_Iic, setOf_gridLevelHit_le_eq]
    exact MeasurableSet.iUnion fun k ↦ MeasurableSet.iUnion fun _ ↦
      hX _ measurableSet_Ioi

/-- Continuity at a time strictly above the level ensures eventual detection no later than
that time. No continuity away from that time is needed. -/
theorem eventually_gridLevelHit_le (hc : ContinuousAt (fun s ↦ X s ω) t)
    (ht : c < X t ω) : ∀ᶠ n in atTop, gridLevelHit X c n ω ≤ t := by
  have hlim : Tendsto (fun n : ℕ ↦ (⌊(t : ℝ) * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n)
      atTop (𝓝 t) := by
    apply NNReal.tendsto_coe.mp
    convert (tendsto_nat_floor_mul_div_atTop t.2).comp
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)) using 1
    · ext n
      simp
    · rfl
  filter_upwards [(hc.tendsto.comp hlim).eventually (Ioi_mem_nhds ht)] with n hn
  refine gridLevelHit_le_iff.mpr ⟨⌊(t : ℝ) * 2 ^ n⌋₊, ?_, hn⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ≥0) < 2 ^ n)]
  exact_mod_cast Nat.floor_le (mul_nonneg t.2 (by positivity : (0 : ℝ) ≤ 2 ^ n))

/-- For an almost-surely continuous process with measurable deterministic-time samples,
the probability that a dyadic grid misses a level before a measurable barrier tends to zero,
provided the process is almost surely strictly above the level at every finite barrier time.
A barrier value of infinity never counts as a miss. -/
theorem tendsto_measure_gridLevelHit_miss {m : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) {σ : Ω → WithTop ℝ≥0}
    (hσ : Measurable σ) (hlevel : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω = t → c < X t ω) :
    Tendsto (fun n ↦ P {ω | σ ω < gridLevelHit X c n ω}) atTop (𝓝 0) := by
  have hm (n : ℕ) : MeasurableSet {ω | σ ω < gridLevelHit X c n ω} :=
    measurableSet_lt hσ (measurable_gridLevelHit hX c n)
  have he : ∀ᵐ ω ∂P, ∀ᶠ n in atTop,
      ω ∈ {ω | σ ω < gridLevelHit X c n ω} ↔ ω ∈ (∅ : Set Ω) := by
    filter_upwards [hc, hlevel] with ω hcont hl
    cases hs : σ ω using WithTop.recTopCoe with
    | top => exact .of_forall fun n ↦ by simp
    | coe t =>
      filter_upwards [eventually_gridLevelHit_le (hcont.continuousAt)
        (hl t hs)] with n hn
      simpa only [mem_ofPred, mem_empty_iff_false, iff_false, hs, not_lt] using hn
  simpa using tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    atTop MeasurableSet.empty hm he

/-- For any sequence of levels almost surely strictly below the process at every finite
barrier time, choose successively finer dyadic grids whose probabilities of missing the
barrier have finite sum. In particular, Borel–Cantelli applies to these misses.
The levels need not be monotone or bounded by a common upper level. -/
theorem exists_gridLevelHit_summable_misses {m : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) {σ : Ω → WithTop ℝ≥0}
    (hσ : Measurable σ) {a : ℕ → ℝ}
    (hlevel : ∀ j, ∀ᵐ ω ∂P, ∀ t : ℝ≥0, σ ω = t → a j < X t ω) :
    ∃ q : ℕ → ℕ, StrictMono q ∧
      (∑' j, P {ω | σ ω < gridLevelHit X (a j) (q j) ω}) < ∞ := by
  classical
  have hsmall (j : ℕ) : ∃ N : ℕ, ∀ n ≥ N,
      P {ω | σ ω < gridLevelHit X (a j) n ω} ≤ (2⁻¹ : ℝ≥0∞) ^ j := by
    have hp : (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ j :=
      pos_iff_ne_zero.mpr (pow_ne_zero _ (by norm_num))
    have hlim := tendsto_measure_gridLevelHit_miss hX hc hσ (hlevel j)
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hp))
    exact ⟨N, fun n hn ↦ (hN n hn).le⟩
  choose N hN using hsmall
  let q (j : ℕ) := j + ∑ i ∈ Finset.range (j + 1), N i
  have hq : StrictMono q := by
    apply strictMono_nat_of_lt_succ
    intro j
    simp only [q, Finset.sum_range_succ]
    omega
  have hbound (j : ℕ) : N j ≤ q j := by
    exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans (Nat.le_add_left _ _)
  refine ⟨q, hq, lt_of_le_of_lt (tsum_le_tsum fun j ↦ hN j (q j) (hbound j)) ?_⟩
  rw [ENNReal.tsum_geometric_two]
  norm_num

end TauCeti
