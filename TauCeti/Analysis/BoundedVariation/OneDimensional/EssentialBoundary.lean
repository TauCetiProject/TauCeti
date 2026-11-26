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
import TauCeti.MeasureTheory.Measure.Interval
import TauCeti.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Perimeter on the line counts essential boundary points

For a null-measurable set `s ⊆ ℝ` and an open set `Ω ⊆ ℝ`, the perimeter of `s` in `Ω` is the
number of points of the essential boundary `∂ᵉs` lying in `Ω`:

`P(s; Ω) = #(∂ᵉs ∩ Ω)`

(`TauCeti.Real.perimeter_eq_encard_essentialBoundary_inter`), as an identity in `ℝ≥0∞`. In
particular `P(s; Ω) ≤ #(frontier s ∩ Ω)` (`TauCeti.Real.perimeter_le_encard_frontier_inter`), and a
set of finite perimeter in `Ω` has only finitely many essential boundary points there
(`TauCeti.Real.finite_essentialBoundary_inter_of_perimeter_ne_top`), so a set of locally finite
perimeter in `Ω` has a locally finite essential boundary in `Ω`. No finiteness of the perimeter is
assumed.

## Proof

Upper bound: an infinite `∂ᵉs ∩ Ω` is trivial. Otherwise every `x ∈ Ω` has a ball `B(x, ε) ⊆ Ω`
meeting `∂ᵉs` at most in `x`. On each half of the ball, `s` is null or conull
(`TauCeti.Real.measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero`), so in the ball `s` is
almost everywhere `∅`, everything, or a half-line ending at `x`
(`MeasureTheory.measure_symmDiff_Iio_or_Ioi_inter_Ioo_eq_zero`), and its perimeter there is `0`
(`TauCeti.Real.perimeter_Ioo_eq_zero_iff`), or at most `1` (`TauCeti.Real.perimeter_Iio`,
`TauCeti.Real.perimeter_Ioi`), and is `0` when `x ∉ ∂ᵉs`. Countable subadditivity of the perimeter
over the cover of `Ω` by these balls (`TauCeti.totalVariationOn_iSup_le_tsum`) sums these bounds to
`#(∂ᵉs ∩ Ω)`.

Lower bound: at a point `x ∈ ∂ᵉs ∩ Ω`, both `s` and its complement fill a positive proportion of
arbitrarily small balls around `x`
(`TauCeti.exists_pos_frequently_ofReal_mul_measure_closedBall_le`), so such a ball inside `Ω`
charges both `s` and its complement, which gives `1 ≤ P(s; Ω)`
(`TauCeti.Real.one_le_perimeter_of_ordConnected`). For finitely many
points of `∂ᵉs ∩ Ω`, split `Ω` into a small ball around one of them and the complement of its
closure, and add the perimeters over these disjoint open sets
(`TauCeti.totalVariationOn_sup_of_disjoint`).

## Main results

* `TauCeti.Real.perimeter_ball_le_one` and `TauCeti.Real.perimeter_ball_eq_zero`: the perimeter in a
  ball meeting `∂ᵉs` at most in its centre, or not at all.
* `TauCeti.Real.perimeter_le_encard_essentialBoundary_inter`: `P(s; Ω) ≤ #(∂ᵉs ∩ Ω)`.
* `TauCeti.Real.perimeter_le_encard_frontier_inter`: `P(s; Ω) ≤ #(frontier s ∩ Ω)`.
* `TauCeti.Real.one_le_perimeter_of_mem_essentialBoundary`: `1 ≤ P(s; Ω)` if `∂ᵉs` meets `Ω`.
* `TauCeti.Real.card_le_perimeter_of_subset_essentialBoundary`: `#F ≤ P(s; Ω)` for a finite set
  `F ⊆ ∂ᵉs ∩ Ω`.
* `TauCeti.Real.perimeter_eq_encard_essentialBoundary_inter`: `P(s; Ω) = #(∂ᵉs ∩ Ω)`.
* `TauCeti.Real.finite_essentialBoundary_inter_of_perimeter_ne_top`: finite perimeter in `Ω` gives
  finitely many essential boundary points in `Ω`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (sets of finite perimeter in one variable).
* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. (2011) (the one-dimensional characterization of sets of finite perimeter).
-/

public section

open Filter Set MeasureTheory Metric TopologicalSpace
open scoped Topology ENNReal Set.Notation symmDiff

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
  exact (perimeter_Ioo_eq_zero_iff (hs.inter measurableSet_Ioo.nullMeasurableSet)).2
    (measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero hs h)

/-- **At most the centre on the essential boundary, perimeter at most one.** If no point of
`B(x, ε)` other than `x` lies in the essential boundary of a null-measurable set `s ⊆ ℝ`, then
`P(s; B(x, ε)) ≤ 1`: on the ball, `s` is almost everywhere `∅`, everything, or a half-line ending
at `x`. -/
theorem perimeter_ball_le_one (hs : NullMeasurableSet s) {ε : ℝ}
    (h : ∀ y ∈ ball x ε, y ∈ essentialBoundary volume s → y = x) :
    perimeter volume ⟨ball x ε, isOpen_ball⟩ s ≤ 1 := by
  have hball : (⟨ball x ε, isOpen_ball⟩ : Opens ℝ) = ⟨Ioo (x - ε) (x + ε), isOpen_Ioo⟩ := by
    ext1; exact Real.ball_eq_Ioo x ε
  by_cases h0 : volume (s ∩ Ioo (x - ε) (x + ε)) = 0 ∨ volume (Ioo (x - ε) (x + ε) \ s) = 0
  · rw [hball, (perimeter_Ioo_eq_zero_iff (hs.inter measurableSet_Ioo.nullMeasurableSet)).2 h0]
    exact zero_le
  rw [not_or] at h0
  have hL := measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero hs
    (a := x - ε) (b := x) fun y hy hyb =>
      hy.2.ne (h y ((Real.ball_eq_Ioo x ε).symm ▸ ⟨hy.1, by linarith [hy.1, hy.2]⟩) hyb)
  have hR := measure_inter_Ioo_eq_zero_or_measure_Ioo_sdiff_eq_zero hs
    (a := x) (b := x + ε) fun y hy hyb =>
      hy.1.ne' (h y ((Real.ball_eq_Ioo x ε).symm ▸ ⟨by linarith [hy.1, hy.2], hy.2⟩) hyb)
  have hae {t : Set ℝ} (ht : volume ((s ∆ t) ∩ Ioo (x - ε) (x + ε)) = 0) :
      s =ᵐ[volume.restrict (ball x ε)] t := by
    rwa [← measure_symmDiff_eq_zero_iff, Measure.restrict_apply' measurableSet_ball,
      Real.ball_eq_Ioo]
  rcases measure_symmDiff_Iio_or_Ioi_inter_Ioo_eq_zero h0.1 h0.2 hL hR Real.volume_singleton
    with hΔ | hΔ
  · rw [perimeter_congr_ae (hae hΔ), perimeter_Iio]
    exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le
  · rw [perimeter_congr_ae (hae hΔ), perimeter_Ioi]
    exact indicator_apply_le' (fun _ => le_rfl) fun _ => zero_le

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

/-- **An essential boundary point carries perimeter at least one.** If a point `x` of the essential
boundary of a null-measurable set `s ⊆ ℝ` lies in the open set `Ω`, then `1 ≤ P(s; Ω)`. -/
theorem one_le_perimeter_of_mem_essentialBoundary (hs : NullMeasurableSet s) {Ω : Opens ℝ}
    (hx : x ∈ essentialBoundary volume s) (hxΩ : x ∈ Ω) : 1 ≤ perimeter volume Ω s := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.isOpen_iff.1 Ω.isOpen x hxΩ
  obtain ⟨a, ha, hfreq⟩ := exists_pos_frequently_ofReal_mul_measure_closedBall_le hx
  obtain ⟨r, ⟨h₁, h₂⟩, hr0, hrε⟩ := (hfreq.and_eventually (Ioo_mem_nhdsGT hε)).exists
  have hpos : 0 < ENNReal.ofReal a * volume (closedBall x r) :=
    ENNReal.mul_pos (ENNReal.ofReal_pos.2 ha).ne' (measure_closedBall_pos volume x hr0).ne'
  have hrB : closedBall x r ⊆ ball x ε := closedBall_subset_ball hrε
  -- The ball `B(x, ε) ⊆ Ω` charges both `s` and its complement.
  let V : Opens ℝ := ⟨ball x ε, isOpen_ball⟩
  refine le_trans ?_ (perimeter_mono (μ := volume) (s := s) (show V ≤ Ω from hεΩ))
  refine one_le_perimeter_of_ordConnected (hs.mono Measure.restrict_le_self)
    (convex_ball x ε).ordConnected ?_ ?_
  · exact (hpos.trans_le (h₁.trans (measure_mono (inter_subset_inter_right _ hrB)))).ne'
  · have hsub : closedBall x r \ s ⊆ sᶜ ∩ V := fun y hy => ⟨hy.2, hrB hy.1⟩
    exact (hpos.trans_le (h₂.trans (measure_mono hsub))).ne'

/-- **Every finite set of essential boundary points is counted by the perimeter.** If a finite set
`F` of points of the essential boundary of a null-measurable `s ⊆ ℝ` lies in the open set `Ω`, then
`#F ≤ P(s; Ω)`. -/
theorem card_le_perimeter_of_subset_essentialBoundary (hs : NullMeasurableSet s) (F : Finset ℝ)
    {Ω : Opens ℝ} (hF : (F : Set ℝ) ⊆ essentialBoundary volume s ∩ Ω) :
    (F.card : ℝ≥0∞) ≤ perimeter volume Ω s := by
  classical
  induction F using Finset.induction_on generalizing Ω with
  | empty => simp
  | insert a F haF ih =>
    -- A ball around `a` missing `F` splits `Ω` into two disjoint open sets.
    obtain ⟨δ, hδ, hδF⟩ := Metric.isOpen_iff.1 F.finite_toSet.isClosed.isOpen_compl a
      (by simpa using haF)
    have ha := hF (Finset.mem_coe.2 (Finset.mem_insert_self a F))
    let Ω₁ : Opens ℝ := Ω ⊓ ⟨ball a (δ / 2), isOpen_ball⟩
    let Ω₂ : Opens ℝ := Ω ⊓ ⟨(closedBall a (δ / 2))ᶜ, isClosed_closedBall.isOpen_compl⟩
    have hdisj : Disjoint Ω₁ Ω₂ := by
      rw [disjoint_iff, ← SetLike.coe_set_eq]
      ext y
      simp only [Ω₁, Ω₂, Opens.coe_inf, Opens.coe_mk, Opens.coe_bot, mem_inter_iff,
        mem_compl_iff, mem_empty_iff_false, iff_false, not_and, not_not]
      exact fun h _ => ball_subset_closedBall h.2
    have h₁ : 1 ≤ perimeter volume Ω₁ s :=
      one_le_perimeter_of_mem_essentialBoundary hs ha.1 ⟨ha.2, mem_ball_self (half_pos hδ)⟩
    have h₂ : (F.card : ℝ≥0∞) ≤ perimeter volume Ω₂ s := by
      refine ih fun y hy => ?_
      have hyF := hF (Finset.mem_coe.2 (Finset.mem_insert_of_mem hy))
      refine ⟨hyF.1, hyF.2, fun hyB => ?_⟩
      exact hδF (closedBall_subset_ball (half_lt_self hδ) hyB) hy
    have hu : LocallyIntegrableOn (s.indicator (1 : ℝ → ℝ)) ((Ω₁ ⊔ Ω₂ : Opens ℝ) : Set ℝ) := by
      rw [Pi.one_def]
      exact locallyIntegrableOn_indicator_const (hs.mono Measure.restrict_le_self) (1 : ℝ)
    calc ((insert a F).card : ℝ≥0∞) = 1 + F.card := by
          rw [Finset.card_insert_of_notMem haF, Nat.cast_add, Nat.cast_one, add_comm]
      _ ≤ perimeter volume Ω₁ s + perimeter volume Ω₂ s := add_le_add h₁ h₂
      _ = perimeter volume (Ω₁ ⊔ Ω₂) s := by
          simp only [perimeter_def]
          exact (totalVariationOn_sup_of_disjoint hu hdisj).symm
      _ ≤ perimeter volume Ω s := perimeter_mono (sup_le inf_le_left inf_le_left)

/-- **The perimeter on the line counts essential boundary points.** For a null-measurable set
`s ⊆ ℝ` and an open set `Ω`, `P(s; Ω) = #(∂ᵉs ∩ Ω)` in `ℝ≥0∞`. -/
theorem perimeter_eq_encard_essentialBoundary_inter (hs : NullMeasurableSet s) (Ω : Opens ℝ) :
    perimeter volume Ω s = (essentialBoundary volume s ∩ Ω).encard := by
  refine le_antisymm (perimeter_le_encard_essentialBoundary_inter hs Ω) ?_
  rcases (essentialBoundary volume s ∩ Ω).finite_or_infinite with hfin | hinf
  · rw [hfin.encard_eq_coe_toFinset_card, ENat.toENNReal_coe]
    exact card_le_perimeter_of_subset_essentialBoundary hs _ (by simp)
  · rw [Set.encard_eq_top hinf, ENat.toENNReal_top, top_le_iff]
    refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
    obtain ⟨F, hF, hcard⟩ := hinf.exists_subset_card_eq ⌈(r : ℝ)⌉₊
    calc (r : ℝ≥0∞) ≤ (⌈(r : ℝ)⌉₊ : ℝ≥0∞) := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
      _ ≤ perimeter volume Ω s := hcard ▸ card_le_perimeter_of_subset_essentialBoundary hs F hF

/-- **Finite perimeter on the line, finitely many essential boundary points.** If a
null-measurable `s ⊆ ℝ` has finite perimeter in the open set `Ω`, then only finitely many points
of `∂ᵉs` lie in `Ω`. -/
theorem finite_essentialBoundary_inter_of_perimeter_ne_top (hs : NullMeasurableSet s)
    {Ω : Opens ℝ} (h : perimeter volume Ω s ≠ ∞) :
    (essentialBoundary volume s ∩ Ω).Finite := by
  rw [perimeter_eq_encard_essentialBoundary_inter hs] at h
  exact Set.encard_lt_top_iff.1 (lt_top_iff_ne_top.2 fun h' => h (by simp [h']))

end TauCeti.Real
