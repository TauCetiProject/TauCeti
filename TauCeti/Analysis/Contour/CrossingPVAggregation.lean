/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.CauchyPrincipalValue
import TauCeti.Analysis.Contour.CurveDistance
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort

/-!
# Aggregating per-window principal values across finitely many crossings

If the `ε`-truncated integral of `g (γ t) * deriv γ t` converges on each crossing window
`[t_i - r, t_i + r]`, the windows are pairwise disjoint and interior to `[a, b]`, and the curve
keeps a positive distance from `s` off the windows, then the truncated integral over all of
`[a, b]` converges — so the single-point principal value `HasCauchyPVAt` exists
(`exists_hasCauchyPVAt_of_perWindow_tendsto`). Off the windows the truncation is eventually
inactive and each between-piece integral is constant; the windows contribute their given
limits; the total follows by splitting at the window boundaries and induction along the sorted
crossing list.

The per-window limits are hypotheses, so one aggregation serves every integrand: the
simple-pole and higher-order per-window theorems both discharge them.

## Main results

* `Contour.exists_hasCauchyPVAt_of_perWindow_tendsto` — the single-point principal value on
  `[a, b]` from per-window convergence at finitely many crossings.

## Provenance

Migrated from `cpv_tendsto_along_sorted_corner` and the aggregation step of
`hasCauchyPV_inv_sub_multiCrossing_corner` of `MultiCrossingCPV.lean` in the AINTLIB
`LeanModularForms` development, restated for a raw curve on `[a, b]` with a generic integrand
(there the induction is instantiated separately for the simple-pole and higher-order
integrands). See N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a
generalized Residue Theorem*, arXiv:1808.00997, §3.
-/

public section

noncomputable section

namespace TauCeti.Contour

open Filter MeasureTheory Set Topology

/-- On an interval where the curve keeps distance `≥ m > 0` from `s`, the truncated integral
is eventually the constant plain integral. -/
private theorem eventually_truncated_integral_const {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {l u m : ℝ} (hlu : l ≤ u) (hm_pos : 0 < m)
    (h_far : ∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) :
    (fun ε : ℝ => ∫ t in l..u, if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => ∫ t in l..u, g (γ t) * deriv γ t := by
  filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hlu] at ht
  rw [if_pos (lt_of_lt_of_le hε.2 (h_far t ht))]

/-- **Aggregation along a sorted crossing list**: with pairwise-disjoint windows interior to
`[a, b]`, per-window convergence, and a positive off-window distance bound, the truncated
integral over `[a, b]` converges. -/
private theorem tendsto_truncated_integral_along_sorted {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {b r : ℝ} (hr_pos : 0 < r)
    (h_int_tr : ∀ ε : ℝ, 0 < ε → ∀ l u : ℝ, l ≤ u →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume l u) :
    ∀ (sorted : List ℝ), sorted.SortedLT →
    ∀ a : ℝ, a ≤ b → (∀ t ∈ sorted, a < t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r < |t - t'|) →
      (∀ t ∈ sorted, ∃ v : ℂ, Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
          if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v)) →
      (∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) →
        m ≤ ‖γ u - s‖) →
      ∃ L : ℂ, Tendsto (fun ε : ℝ => ∫ u in a..b,
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  intro sorted
  induction sorted with
  | nil =>
    intro _ a hab _ _ _ _ h_far
    obtain ⟨m, hm_pos, hm⟩ := h_far
    exact ⟨∫ u in a..b, g (γ u) * deriv γ u,
      Tendsto.congr' (eventually_truncated_integral_const hab hm_pos
        fun u hu => hm u hu fun t ht => absurd ht (List.not_mem_nil)).symm
        tendsto_const_nhds⟩
  | cons t rest IH =>
    intro h_sorted a hab h_lo h_hi h_pair h_win h_far
    obtain ⟨m, hm_pos, hm⟩ := h_far
    obtain ⟨v_t, h_v_t⟩ := h_win t List.mem_cons_self
    have h_head_lo : a < t - r := h_lo t List.mem_cons_self
    have h_head_hi : t + r ≤ b := h_hi t List.mem_cons_self
    have h_rest_above : ∀ t' ∈ rest, t + r < t' - r := fun t' ht' => by
      have h_lt : t < t' := (List.pairwise_cons.mp h_sorted.pairwise).1 t' ht'
      have h_sep := h_pair t List.mem_cons_self t' (List.mem_cons_of_mem t ht')
        (ne_of_gt h_lt)
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h_sep
      linarith
    -- the left piece is off every window
    have h_far_left : ∀ u ∈ Icc a (t - r), m ≤ ‖γ u - s‖ := fun u hu => by
      refine hm u ⟨hu.1, by linarith [hu.2]⟩ fun t' ht' h_in => ?_
      rcases List.mem_cons.mp ht' with rfl | h_rest
      · linarith [hu.2, h_in.1]
      · linarith [hu.2, h_in.1, h_rest_above t' h_rest]
    -- recurse on the tail, over [t + r, b]
    obtain ⟨L_rest, h_L_rest⟩ := IH
      ((List.pairwise_cons.mp h_sorted.pairwise).2).sortedLT (t + r) h_head_hi
      (fun t' ht' => h_rest_above t' ht')
      (fun t' ht' => h_hi t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' t'' ht'' hne => h_pair t' (List.mem_cons_of_mem t ht')
        t'' (List.mem_cons_of_mem t ht'') hne)
      (fun t' ht' => h_win t' (List.mem_cons_of_mem t ht'))
      ⟨m, hm_pos, fun u hu h_avoid => hm u ⟨by linarith [hu.1], hu.2⟩ fun t' ht' => by
        rcases List.mem_cons.mp ht' with rfl | h_rest
        · exact fun h_in => absurd hu.1 (not_le.mpr h_in.2)
        · exact h_avoid t' h_rest⟩
    refine ⟨(∫ u in a..(t - r), g (γ u) * deriv γ u) + v_t + L_rest, ?_⟩
    have h_split : (fun ε : ℝ => ∫ u in a..b,
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => (∫ u in a..(t - r),
            if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) +
          (∫ u in (t - r)..(t + r),
            if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) +
          (∫ u in (t + r)..b,
            if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      rw [← intervalIntegral.integral_add_adjacent_intervals
          ((h_int_tr ε hε a (t - r) h_head_lo.le).trans
            (h_int_tr ε hε (t - r) (t + r) (by linarith)))
          (h_int_tr ε hε (t + r) b h_head_hi),
        ← intervalIntegral.integral_add_adjacent_intervals
          (h_int_tr ε hε a (t - r) h_head_lo.le)
          (h_int_tr ε hε (t - r) (t + r) (by linarith))]
    refine Tendsto.congr' h_split.symm ?_
    exact ((Tendsto.congr' (eventually_truncated_integral_const h_head_lo.le hm_pos
      h_far_left).symm tendsto_const_nhds).add h_v_t).add h_L_rest

/-- **The single-point principal value from per-window convergence**: if the `ε`-truncated
integral of `g (γ t) * deriv γ t` converges on each crossing window (pairwise disjoint,
interior to `[a, b]`), the truncations are integrable, and the curve keeps a positive distance
from `s` off the windows, then `HasCauchyPVAt γ a b g s` holds for some value. The per-window
limits are hypotheses, so both the simple-pole and higher-order per-window theorems discharge
them. -/
theorem exists_hasCauchyPVAt_of_perWindow_tendsto {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {a b r : ℝ} (hr_pos : 0 < r) (hab : a ≤ b) (crossings : Finset ℝ)
    (h_lo : ∀ t ∈ crossings, a < t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|)
    (h_int_tr : ∀ ε : ℝ, 0 < ε → ∀ l u : ℝ, l ≤ u →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume l u)
    (h_win : ∀ t ∈ crossings, ∃ v : ℂ, Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (h_far : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) →
      m ≤ ‖γ u - s‖) :
    ∃ L : ℂ, HasCauchyPVAt γ a b g s L := by
  classical
  obtain ⟨m, hm_pos, hm⟩ := h_far
  obtain ⟨L, hL⟩ := tendsto_truncated_integral_along_sorted hr_pos h_int_tr
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings) a hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => h_win t ((Finset.mem_sort _).mp ht))
    ⟨m, hm_pos, fun u hu h_avoid => hm u hu
      fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht)⟩
  refine ⟨L, hasCauchyPVAt_iff.mpr ⟨?_, hL⟩⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact h_int_tr ε hε a b hab

end TauCeti.Contour

end
