/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Order.Interval.Set.Union

/-!
# Excluding multiple jumps from microscopic increment probabilities

For a nondecreasing natural-valued process with stationary increment laws,
`P(N h - N 0 ≥ 2) = o(h)` implies, on one event of full measure, that no positive
time has a jump from the left of size two or more. The conclusion is expressed without choosing left
limits: at each `t > 0` some `s < t` satisfies `N t ≤ N s + 1`. Monotonicity then
gives the same bound for every time between `s` and `t`.

Neither independence nor right continuity is needed for this implication. In
particular, it applies directly to the simplicity part of the microscopic
characterization of a right-continuous Poisson count process, before identifying
its marginal laws.
It makes no assertion about the count at time zero.

The proof covers each bounded time interval by equal-mesh, right-closed cells.
A multiple jump belongs to a bad cell at every mesh, so the union bound and the
microscopic estimate make its outer measure zero. Thus no measurability of an
uncountable union of jump events is assumed.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025,
  §9.5, microscopic characterization of the Poisson process.
-/

public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
  {N : ℝ≥0 → Ω → ℕ}

private theorem measureReal_multiple_jump_le
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (b : ℝ≥0) {n : ℕ} (hn : n ≠ 0) :
    P.real {ω | Monotone (fun t ↦ N t ω) ∧
      ∃ t ∈ Ioc 0 b, ∀ s < t, N s ω + 1 < N t ω} ≤
        (n : ℝ) * P.real {ω | 2 ≤ N (b / n) ω - N 0 ω} := by
  let h := b / (n : ℝ≥0)
  let B := fun k : ℕ ↦ {ω | 2 ≤ N ((k : ℝ≥0) * h + h) ω - N ((k : ℝ≥0) * h) ω}
  have hcover : {ω | Monotone (fun t ↦ N t ω) ∧
      ∃ t ∈ Ioc 0 b, ∀ s < t, N s ω + 1 < N t ω} ⊆
        ⋃ k ∈ Finset.range n, B k := by
    rintro ω ⟨hmono, t, ht, hjump⟩
    have ht' : t ∈ Ioc ((0 : ℝ≥0) * h) ((n : ℝ≥0) * h) := by
      simpa [h, hn, mul_div_cancel₀] using ht
    obtain ⟨k, hk, hkt⟩ := mem_iUnion₂.mp (Ioc_subset_biUnion_Ioc n
      (fun k ↦ (k : ℝ≥0) * h) (by simpa only [Nat.cast_zero] using ht'))
    refine mem_iUnion₂.mpr ⟨k, hk, ?_⟩
    have hlt := hjump _ hkt.1
    have hle := hmono hkt.2
    simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] at hle
    dsimp [B]
    omega
  have hprob (k : ℕ) : P.real (B k) = P.real {ω | 2 ≤ N h ω - N 0 ω} := by
    have heq := (hstat ((k : ℝ≥0) * h) h).measure_mem_eq (measurableSet_Ici (a := 2))
    simp only [Set.preimage, Set.mem_Ici] at heq
    simp only [B, measureReal_def, heq]
  calc
    _ ≤ P.real (⋃ k ∈ Finset.range n, B k) := measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range n, P.real (B k) := measureReal_biUnion_finset_le _ _
    _ = _ := by simp [hprob, h]

omit [IsFiniteMeasure P] in
private theorem tendsto_mesh_multiple_probability
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h ↦ (h : ℝ))) {b : ℝ≥0} (hb : 0 < b) :
    Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) * P.real {ω | 2 ≤ N (b / (n + 1)) ω - N 0 ω})
      atTop (𝓝 0) := by
  have hmesh : Tendsto (fun n : ℕ ↦ b / (n + 1 : ℝ≥0)) atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat b).comp (tendsto_add_atTop_nat 1)
    · exact Eventually.of_forall fun n ↦ div_pos hb (by positivity)
  have hlim := (hsmall.tendsto_div_nhds_zero.comp hmesh).const_mul (b : ℝ)
  convert hlim using 1
  · funext n
    simp only [Function.comp_apply, NNReal.coe_div, NNReal.coe_add,
      NNReal.coe_natCast, NNReal.coe_one]
    field_simp [ne_of_gt (NNReal.coe_pos.mpr hb)]
  · simp

/-- Stationary increments and `P(N h - N 0 ≥ 2) = o(h)` exclude all multiple jumps
from the left at positive times, simultaneously almost surely. The existential bound expresses
that the jump from the left at `t` is at most one, without requiring left limits
as additional data. Neither independence nor right continuity is assumed, and the
initial count is unrestricted. -/
theorem ae_count_le_add_one_of_small_time
    (hmono : ∀ᵐ ω ∂P, Monotone (fun t ↦ N t ω))
    (hstat : ∀ s h, IdentDistrib (fun ω ↦ N (s + h) ω - N s ω)
      (fun ω ↦ N h ω - N 0 ω) P P)
    (hsmall : (fun h : ℝ≥0 ↦ P.real {ω | 2 ≤ N h ω - N 0 ω}) =o[𝓝[>] 0]
      (fun h ↦ (h : ℝ))) :
    ∀ᵐ ω ∂P, ∀ t > (0 : ℝ≥0), ∃ s < t, N t ω ≤ N s ω + 1 := by
  have hnull (m : ℕ) : P {ω | Monotone (fun t ↦ N t ω) ∧
      ∃ t ∈ Ioc 0 (m + 1 : ℝ≥0), ∀ s < t, N s ω + 1 < N t ω} = 0 := by
    rw [← measureReal_eq_zero_iff]
    apply le_antisymm _ measureReal_nonneg
    refine ge_of_tendsto
      (tendsto_mesh_multiple_probability hsmall (b := (m : ℝ≥0) + 1) (by positivity)) ?_
    exact Eventually.of_forall fun n ↦ by
      simpa only [Nat.cast_succ] using
        measureReal_multiple_jump_le hstat ((m : ℝ≥0) + 1) (Nat.succ_ne_zero n)
  have hae : ∀ᵐ ω ∂P, ∀ m : ℕ, ¬(Monotone (fun t ↦ N t ω) ∧
      ∃ t ∈ Ioc 0 (m + 1 : ℝ≥0), ∀ s < t, N s ω + 1 < N t ω) := by
    exact ae_all_iff.mpr fun m ↦ by simpa only [ae_iff, not_not] using hnull m
  filter_upwards [hmono, hae] with ω hω hgood t ht
  obtain ⟨m, hm⟩ := exists_nat_gt t
  by_contra! hbad
  exact hgood m ⟨hω, t, ⟨ht, hm.le.trans (by simp)⟩, hbad⟩

end TauCeti.Probability
