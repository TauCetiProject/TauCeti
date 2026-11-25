/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import TauCeti.Analysis.BoundedVariation.Real
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Escaping intervals: compactness in `L¹(μ)` needs finite mass

For the weight `0` on `ℝ`, whose measure `e^{-0} · volume` is Lebesgue measure, of infinite
mass, the intervals `U_k = (k, k + 1)` all have perimeter `2`. Their indicators converge to `0` in
`L¹_loc`: every compact set meets `U_k` in a null set, in fact the empty set, for large `k`. They
do not converge to `0` in `L¹`, since each `U_k` has measure `1`, and no subsequence converges in
`L¹` to the indicator of any set, since `U_j` and `U_k` are disjoint for `j ≠ k`, so the distance
between their indicators is `2`. So compactness in `L¹(μ)` of sets with bounded weighted perimeter
needs the finite total mass `μ(E) < ∞`.
-/

open Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal symmDiff Topology

public section

namespace TauCeti.Examples.EscapingIntervals

/-- With weight `0` on `ℝ`, every interval `(k, k + 1)` has perimeter `2`. -/
example (k : ℕ) : weightedPerimeter (0 : ℝ → ℝ) ⊤ (Ioo (k : ℝ) (k + 1)) = 2 := by
  rw [weightedPerimeter_zero_weight, Real.perimeter_Ioo (lt_add_one _)]

/-- The indicators of `(k, k + 1)` converge to `0` in `L¹_loc`: every compact set meets the
intervals in sets whose measure tends to `0`. -/
example {K : Set ℝ} (hK : IsCompact K) :
    Tendsto (fun k : ℕ => volume (Ioo (k : ℝ) (k + 1) ∩ K)) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hK.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_ge R
  refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
  have hNk : (N : ℝ) ≤ k := by exact_mod_cast hk
  rw [eq_comm, measure_eq_zero_iff_ae_notMem]
  refine ae_of_all _ fun x ⟨hx, hxK⟩ => ?_
  linarith [hR hxK, hx.1]

/-- The indicators of `(k, k + 1)` do not converge to `0` in `L¹`: each interval has measure
`1`. -/
example (k : ℕ) : volume (Ioo (k : ℝ) (k + 1) ∆ ∅) = 1 := by
  rw [← bot_eq_empty, symmDiff_bot, Real.volume_Ioo]
  simp

/-- No subsequence of the indicators of `(k, k + 1)` converges in `L¹` to the indicator of any
set: the measure of the symmetric difference of two distinct intervals is `2`. -/
example : ¬ ∃ (U : Set ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
    Tendsto (fun n => volume (Ioo (φ n : ℝ) (φ n + 1) ∆ U)) atTop (𝓝 0) := by
  rintro ⟨U, φ, hφ, hU⟩
  obtain ⟨n, hn⟩ :=
    eventually_atTop.1 (hU.eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1)))
  have hd : Disjoint (Ioo (φ n : ℝ) (φ n + 1)) (Ioo (φ (n + 1) : ℝ) (φ (n + 1) + 1)) := by
    simpa [Function.onFun] using pairwise_disjoint_Ioo_intCast (α := ℝ)
      (show (φ n : ℤ) ≠ φ (n + 1) by exact_mod_cast (hφ (Nat.lt_succ_self n)).ne)
  have h2 : volume (Ioo (φ n : ℝ) (φ n + 1) ∆ Ioo (φ (n + 1) : ℝ) (φ (n + 1) + 1)) = 2 := by
    rw [hd.symmDiff_eq_sup, measure_union hd measurableSet_Ioo]
    simp [Real.volume_Ioo, one_add_one_eq_two]
  have hle := measure_symmDiff_le (μ := volume) (Ioo (φ n : ℝ) (φ n + 1)) U
    (Ioo (φ (n + 1) : ℝ) (φ (n + 1) + 1))
  rw [h2, symmDiff_comm U] at hle
  exact lt_irrefl _ (hle.trans_lt ((ENNReal.add_lt_add (hn n le_rfl)
    (hn (n + 1) (Nat.le_succ n))).trans_eq one_add_one_eq_two))

end TauCeti.Examples.EscapingIntervals
