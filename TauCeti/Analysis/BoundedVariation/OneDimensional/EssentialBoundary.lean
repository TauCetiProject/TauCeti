/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
public import TauCeti.MeasureTheory.Covering.EssentialBoundary.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.MeasureTheory.Covering.EssentialBoundary.Real
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Perimeter on the line is bounded by the number of essential boundary points

For a null-measurable set `s ⊆ ℝ` and an open set `Ω ⊆ ℝ`, the perimeter of `s` in `Ω` is at most
the number of points of the essential boundary `∂ᵉs` lying in `Ω`:

`P(s; Ω) ≤ #(∂ᵉs ∩ Ω)`

(`TauCeti.Real.perimeter_le_encard_essentialBoundary_inter`), as an inequality in `ℝ≥0∞`. In
particular `P(s; Ω) ≤ #(frontier s ∩ Ω)`
(`TauCeti.Real.perimeter_le_encard_frontier_inter`). This is the one-dimensional case of the
converse finite-perimeter criterion: a set whose essential boundary is locally finite has locally
finite perimeter. No finiteness of the perimeter is assumed.

## Proof

An infinite `∂ᵉs ∩ Ω` is trivial. Otherwise every `x ∈ Ω` has a ball `B(x, ε) ⊆ Ω` meeting `∂ᵉs`
at most in `x`. On each half of the ball, `s` is null or conull
(`TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero`), so in the ball `s` is
almost everywhere `∅`, everything, or a half-line ending at `x`, and its perimeter there is `0`,
or at most `1` (`TauCeti.Real.perimeter_Iio`, `TauCeti.Real.perimeter_Ioi`), and is `0` when
`x ∉ ∂ᵉs`. Countable subadditivity of the perimeter over the cover of `Ω` by these balls
(`TauCeti.totalVariationOn_iSup_le_tsum`) sums these bounds to `#(∂ᵉs ∩ Ω)`.

## Main results

* `TauCeti.Real.perimeter_ball_le_one` and `TauCeti.Real.perimeter_ball_eq_zero`: the perimeter in a
  ball meeting `∂ᵉs` at most in its centre, or not at all.
* `TauCeti.Real.perimeter_le_encard_essentialBoundary_inter`: `P(s; Ω) ≤ #(∂ᵉs ∩ Ω)`.
* `TauCeti.Real.perimeter_le_encard_frontier_inter`: `P(s; Ω) ≤ #(frontier s ∩ Ω)`.
-/

public section

open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal Set.Notation

namespace TauCeti.Real

variable {s : Set ℝ} {x : ℝ}

/-- **No essential boundary in a ball, no perimeter.** If no point of `B(x, ε)` lies in the
essential boundary of a null-measurable set `s ⊆ ℝ`, then `P(s; B(x, ε)) = 0`. -/
theorem perimeter_ball_eq_zero (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∉ essentialBoundary volume s) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s = 0 := by
  have hball : (⟨ball x ε, isOpen_ball⟩ : Opens ℝ) = ⟨Ioo (x - ε) (x + ε), isOpen_Ioo⟩ := by
    ext1; exact Real.ball_eq_Ioo x ε
  rw [Real.ball_eq_Ioo] at h
  rw [hball]
  rcases measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero hs h with h0 | h0
  · rw [perimeter_congr_ae (t := ∅), perimeter_empty]
    rw [Opens.coe_mk, ae_eq_empty, Measure.restrict_apply' measurableSet_Ioo]
    exact h0
  · rw [perimeter_congr_ae (t := univ), perimeter_univ]
    rw [Opens.coe_mk, ae_eq_univ, Measure.restrict_apply' measurableSet_Ioo, ← sdiff_eq_compl_inter]
    exact h0

/-- On a ball, `s` has the perimeter of any set `t` that agrees with it almost everywhere off the
centre. -/
private theorem perimeter_ball_congr {ε : ℝ} {t : Set ℝ}
    (ht : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ ball x ε → y ≠ x → (y ∈ s ↔ y ∈ t)) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s = perimeter volume ⟨ball x ε, isOpen_ball⟩ t := by
  have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ≠ x := by
    simpa using (measure_eq_zero_iff_ae_notMem.1 (measure_singleton x))
  refine perimeter_congr_ae (eventuallyEqSet_iff.2 ?_)
  rw [Opens.coe_mk, ae_restrict_iff' measurableSet_ball]
  filter_upwards [ht, hne] with y hy hyx hyB
  exact hy hyB hyx

/-- **At most the centre on the essential boundary, perimeter at most one.** If no point of
`B(x, ε)` other than `x` lies in the essential boundary of a null-measurable set `s ⊆ ℝ`, then
`P(s; B(x, ε)) ≤ 1`: on the ball, `s` is almost everywhere `∅`, everything, or a half-line ending
at `x`. -/
theorem perimeter_ball_le_one (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∈ essentialBoundary volume s → y = x) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s ≤ 1 := by
  have hball : ∀ {y}, y ∈ ball x ε ↔ x - ε < y ∧ y < x + ε := by
    intro y; rw [Real.ball_eq_Ioo, mem_Ioo]
  have hL := measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero hs
    (a := x - ε) (b := x) fun y hy hyb =>
      hy.2.ne (h y (hball.2 ⟨hy.1, by linarith [hy.1, hy.2]⟩) hyb)
  have hR := measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero hs
    (a := x) (b := x + ε) fun y hy hyb =>
      hy.1.ne' (h y (hball.2 ⟨by linarith [hy.1, hy.2], hy.2⟩) hyb)
  simp only [measure_eq_zero_iff_ae_notMem, mem_inter_iff, Set.mem_sdiff, mem_Ioo, not_and,
    not_not] at hL hR
  rcases hL with hL | hL <;> rcases hR with hR | hR
  · rw [perimeter_ball_congr (t := ∅) ?_, perimeter_empty]
    · exact zero_le
    filter_upwards [hL, hR] with y hL hR hyB hyx
    simp only [mem_empty_iff_false, iff_false]
    intro hys
    rcases hyx.lt_or_gt with hlt | hgt
    · exact hL hys (hball.1 hyB).1 hlt
    · exact hR hys hgt (hball.1 hyB).2
  · rw [perimeter_ball_congr (t := Ioi x) ?_, perimeter_Ioi]
    · exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le
    filter_upwards [hL, hR] with y hL hR hyB hyx
    rcases hyx.lt_or_gt with hlt | hgt
    · exact iff_of_false (fun hys => hL hys (hball.1 hyB).1 hlt) (by simpa using hlt.le)
    · exact iff_of_true (hR ⟨hgt, (hball.1 hyB).2⟩) hgt
  · rw [perimeter_ball_congr (t := Iio x) ?_, perimeter_Iio]
    · exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le
    filter_upwards [hL, hR] with y hL hR hyB hyx
    rcases hyx.lt_or_gt with hlt | hgt
    · exact iff_of_true (hL ⟨(hball.1 hyB).1, hlt⟩) hlt
    · exact iff_of_false (fun hys => hR hys hgt (hball.1 hyB).2) (by simpa using hgt.le)
  · rw [perimeter_ball_congr (t := univ) ?_, perimeter_univ]
    · exact zero_le
    filter_upwards [hL, hR] with y hL hR hyB hyx
    simp only [mem_univ, iff_true]
    rcases hyx.lt_or_gt with hlt | hgt
    · exact hL ⟨(hball.1 hyB).1, hlt⟩
    · exact hR ⟨hgt, (hball.1 hyB).2⟩

/-- **The perimeter in a ball with at most its centre on the essential boundary.** If no point of
`B(x, ε)` other than `x` lies in `∂ᵉs`, then `P(s; B(x, ε))` is at most `1` if `x ∈ ∂ᵉs` and is
`0` otherwise. -/
theorem perimeter_ball_le_indicator (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∈ essentialBoundary volume s → y = x) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s ≤ (essentialBoundary volume s).indicator 1 x := by
  by_cases hx : x ∈ essentialBoundary volume s
  · rw [indicator_of_mem hx, Pi.one_apply]
    exact perimeter_ball_le_one hs h
  · rw [indicator_of_notMem hx, perimeter_ball_eq_zero hs fun y hy hyb => hx (h y hy hyb ▸ hyb)]

/-- **The perimeter on the line is at most the number of essential boundary points.** For a
null-measurable set `s ⊆ ℝ` and an open set `Ω`, `P(s; Ω) ≤ #(∂ᵉs ∩ Ω)` in `ℝ≥0∞`. In particular a
set whose essential boundary meets `Ω` in finitely many points has finite perimeter in `Ω`. -/
theorem perimeter_le_encard_essentialBoundary_inter (hs : NullMeasurableSet s) (Ω : Opens ℝ) :
    perimeter volume Ω s ≤ (essentialBoundary volume s ∩ Ω).encard := by
  set B := essentialBoundary volume s
  rcases (B ∩ Ω).finite_or_infinite with hfin | hinf
  swap
  · simp [Set.encard_eq_top hinf]
  -- Around each point of `Ω`, a ball inside `Ω` meeting `∂ᵉs` at most in its centre.
  have hball : ∀ x : (Ω : Set ℝ), ∃ ε > 0, ball (x : ℝ) ε ⊆ Ω ∧
      ∀ y ∈ ball (x : ℝ) ε, y ∈ B → y = x := by
    intro x
    have hcl : IsClosed ((B ∩ Ω) \ {(x : ℝ)}) := (hfin.sdiff).isClosed
    have hmem : ((B ∩ Ω) \ {(x : ℝ)})ᶜ ∩ Ω ∈ 𝓝 (x : ℝ) :=
      inter_mem (hcl.isOpen_compl.mem_nhds (by simp)) (Ω.isOpen.mem_nhds x.property)
    obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.1 hmem
    refine ⟨ε, hε, fun y hy => (hεs hy).2, fun y hy hyB => ?_⟩
    have := (hεs hy).1
    simp only [mem_compl_iff, Set.mem_sdiff, mem_inter_iff, mem_singleton_iff, not_and,
      not_not] at this
    exact this ⟨hyB, (hεs hy).2⟩
  choose ε hε hεΩ hεB using hball
  let U : ↥(Ω : Set ℝ) → Opens ℝ := fun x => ⟨ball (x : ℝ) (ε x), isOpen_ball⟩
  have hU : (⨆ x, U x) = Ω := by
    refine le_antisymm (iSup_le fun x => hεΩ x) fun y hy => ?_
    exact Opens.mem_iSup.2 ⟨⟨y, hy⟩, mem_ball_self (hε _)⟩
  calc perimeter volume Ω s = perimeter volume (⨆ x, U x) s := by rw [hU]
    _ ≤ ∑' x, perimeter volume (U x) s := by
        simp only [perimeter_def]
        exact totalVariationOn_iSup_le_tsum (locallyIntegrableOn_indicator_const
          (hs.mono Measure.restrict_le_self) (1 : ℝ))
    _ ≤ ∑' x : (Ω : Set ℝ), ((Ω : Set ℝ) ↓∩ (B ∩ Ω)).indicator 1 x := by
        refine tsum_le_tsum fun x => (perimeter_ball_le_indicator hs (hεB x)).trans (le_of_eq ?_)
        classical simp [B, indicator_apply]
    _ = ((Ω : Set ℝ) ↓∩ (B ∩ Ω)).encard := ENNReal.tsum_indicator_one _
    _ ≤ (B ∩ Ω).encard := by
        exact_mod_cast encard_preimage_val_le_encard_right _ _

/-- **The perimeter on the line is at most the number of frontier points.** For a null-measurable
set `s ⊆ ℝ` and an open set `Ω`, `P(s; Ω) ≤ #(frontier s ∩ Ω)` in `ℝ≥0∞`. -/
theorem perimeter_le_encard_frontier_inter (hs : NullMeasurableSet s) (Ω : Opens ℝ) :
    perimeter volume Ω s ≤ (frontier s ∩ Ω).encard :=
  (perimeter_le_encard_essentialBoundary_inter hs Ω).trans <| by
    exact_mod_cast encard_le_encard (inter_subset_inter_left _ essentialBoundary_subset_frontier)

end TauCeti.Real
