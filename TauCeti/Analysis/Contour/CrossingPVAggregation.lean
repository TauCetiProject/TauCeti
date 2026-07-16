/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Contour.CauchyPrincipalValue
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Sort

/-!
# Aggregating per-window principal values across finitely many crossings

If the `ε`-truncated integral of `g (γ t) * deriv γ t` converges on each crossing window
`[t_i - r, t_i + r]`, the windows are pairwise disjoint and interior to `[a, b]`, and the curve
keeps a positive distance from `s` off the windows, then the truncated integral over all of
`[a, b]` converges — the single-point principal value exists
(`cauchyPVExistsAt_of_perWindow_tendsto`). Off the windows the truncation is eventually
inactive and each between-piece integral is constant; the windows contribute their given
limits; the pieces concatenate (`HasCauchyPVAt.concat`) along the sorted crossing list.

The per-window limits are hypotheses, so one aggregation serves every integrand: the
simple-pole and higher-order per-window theorems both discharge them.

## Main results

* `Contour.cauchyPVExistsAt_of_perWindow_tendsto` — the single-point principal value on
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

/-- On an interval where the curve keeps distance `≥ m > 0` from `s`, the principal value at
`s` is the plain integral: the truncation is eventually inactive. Continuity of the curve is
not needed — the distance bound and the truncated integrability carry the clauses. -/
private theorem hasCauchyPVAt_of_dist_lower_bound {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {l u m : ℝ} (hlu : l ≤ u) (hm_pos : 0 < m)
    (h_far : ∀ t ∈ Icc l u, m ≤ ‖γ t - s‖)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume l u) :
    HasCauchyPVAt γ l u g s (∫ t in l..u, g (γ t) * deriv γ t) := by
  have h_ev : (fun ε : ℝ => ∫ t in l..u, if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => ∫ t in l..u, g (γ t) * deriv γ t := by
    filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hlu] at ht
    rw [if_pos (lt_of_lt_of_le hε.2 (h_far t ht))]
  refine hasCauchyPVAt_iff.mpr ⟨?_, Tendsto.congr' h_ev.symm tendsto_const_nhds⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact h_int_tr ε hε

/-- **Aggregation along a sorted crossing list**: with pairwise-disjoint windows interior to
`[a, b]`, per-window convergence, and a positive off-window distance bound, the principal
value at `s` exists on `[a, b]` — the between-pieces and windows concatenate. -/
private theorem cauchyPVExistsAt_along_sorted {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {A b r : ℝ} (hr_pos : 0 < r)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume A b) :
    ∀ (sorted : List ℝ), sorted.SortedLT →
    ∀ a : ℝ, A ≤ a → a ≤ b → (∀ t ∈ sorted, a < t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r < |t - t'|) →
      (∀ t ∈ sorted, ∃ v : ℂ, Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
          if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v)) →
      (∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) →
        m ≤ ‖γ u - s‖) →
      CauchyPVExistsAt γ a b g s := by
  intro sorted
  induction sorted with
  | nil =>
    intro _ a hA hab _ _ _ _ h_far
    obtain ⟨m, hm_pos, hm⟩ := h_far
    exact CauchyPVExistsAt.intro (hasCauchyPVAt_of_dist_lower_bound hab hm_pos
      (fun u hu => hm u hu fun t ht => absurd ht (List.not_mem_nil))
      (fun ε hε => (h_int_tr ε hε).mono_set (by
        rw [uIcc_of_le hab, uIcc_of_le (hA.trans hab)]
        exact Icc_subset_Icc hA le_rfl)))
  | cons t rest IH =>
    intro h_sorted a hA hab h_lo h_hi h_pair h_win h_far
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
    -- the between-piece to the left of the head window is off every window
    have h_left : HasCauchyPVAt γ a (t - r) g s
        (∫ u in a..(t - r), g (γ u) * deriv γ u) := by
      refine hasCauchyPVAt_of_dist_lower_bound h_head_lo.le hm_pos (fun u hu => ?_)
        (fun ε hε => (h_int_tr ε hε).mono_set (by
          rw [uIcc_of_le h_head_lo.le, uIcc_of_le (hA.trans hab)]
          exact Icc_subset_Icc hA (by linarith)))
      refine hm u ⟨hu.1, by linarith [hu.2]⟩ fun t' ht' h_in => ?_
      rcases List.mem_cons.mp ht' with rfl | h_rest
      · linarith [hu.2, h_in.1]
      · linarith [hu.2, h_in.1, h_rest_above t' h_rest]
    -- the head window carries its given limit
    have h_window : HasCauchyPVAt γ (t - r) (t + r) g s v_t :=
      hasCauchyPVAt_iff.mpr ⟨by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        exact (h_int_tr ε hε).mono_set (by
          rw [uIcc_of_le (show t - r ≤ t + r by linarith), uIcc_of_le (hA.trans hab)]
          exact Icc_subset_Icc (by linarith) (by linarith)), h_v_t⟩
    -- recurse on the tail, over [t + r, b]
    obtain ⟨L_rest, h_rest⟩ := cauchyPVExistsAt_iff.mp (IH
      ((List.pairwise_cons.mp h_sorted.pairwise).2).sortedLT (t + r)
      (by linarith) h_head_hi
      (fun t' ht' => h_rest_above t' ht')
      (fun t' ht' => h_hi t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' t'' ht'' hne => h_pair t' (List.mem_cons_of_mem t ht')
        t'' (List.mem_cons_of_mem t ht'') hne)
      (fun t' ht' => h_win t' (List.mem_cons_of_mem t ht'))
      ⟨m, hm_pos, fun u hu h_avoid => hm u ⟨by linarith [hu.1], hu.2⟩ fun t' ht' => by
        rcases List.mem_cons.mp ht' with rfl | h_rest
        · exact fun h_in => absurd hu.1 (not_le.mpr h_in.2)
        · exact h_avoid t' h_rest⟩)
    exact CauchyPVExistsAt.intro ((h_left.concat h_window).concat h_rest)

/-- **The single-point principal value from per-window convergence**: if the `ε`-truncated
integral of `g (γ t) * deriv γ t` converges on each crossing window (pairwise disjoint,
interior to `[a, b]`), the truncations are integrable, and the curve keeps a positive distance
from `s` off the windows, then the principal value at `s` exists on `[a, b]`. The per-window
limits are hypotheses, so both the simple-pole and higher-order per-window theorems discharge
them. -/
theorem cauchyPVExistsAt_of_perWindow_tendsto {γ : ℝ → ℂ} {s : ℂ} {g : ℂ → ℂ}
    {a b r : ℝ} (hr_pos : 0 < r) (hab : a ≤ b) (crossings : Finset ℝ)
    (h_lo : ∀ t ∈ crossings, a < t - r) (h_hi : ∀ t ∈ crossings, t + r ≤ b)
    (h_pair : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|)
    (h_int_tr : ∀ ε : ℝ, 0 < ε →
      IntervalIntegrable (fun t => if ‖γ t - s‖ > ε then g (γ t) * deriv γ t else 0)
        MeasureTheory.volume a b)
    (h_win : ∀ t ∈ crossings, ∃ v : ℂ, Tendsto (fun ε : ℝ => ∫ u in (t - r)..(t + r),
        if ‖γ u - s‖ > ε then g (γ u) * deriv γ u else 0) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (h_far : ∃ m : ℝ, 0 < m ∧ ∀ u ∈ Icc a b, (∀ t ∈ crossings, u ∉ Ioo (t - r) (t + r)) →
      m ≤ ‖γ u - s‖) :
    CauchyPVExistsAt γ a b g s := by
  classical
  obtain ⟨m, hm_pos, hm⟩ := h_far
  exact cauchyPVExistsAt_along_sorted hr_pos h_int_tr
    (crossings.sort (· ≤ ·)) (Finset.sortedLT_sort crossings) a le_rfl hab
    (fun t ht => h_lo t ((Finset.mem_sort _).mp ht))
    (fun t ht => h_hi t ((Finset.mem_sort _).mp ht))
    (fun t ht t' ht' hne => h_pair t ((Finset.mem_sort _).mp ht)
      t' ((Finset.mem_sort _).mp ht') hne)
    (fun t ht => h_win t ((Finset.mem_sort _).mp ht))
    ⟨m, hm_pos, fun u hu h_avoid => hm u hu
      fun t ht => h_avoid t ((Finset.mem_sort _).mpr ht)⟩

end TauCeti.Contour

end
