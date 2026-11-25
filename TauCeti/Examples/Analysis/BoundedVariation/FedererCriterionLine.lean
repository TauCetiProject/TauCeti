/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Real
public import TauCeti.Analysis.BoundedVariation.Slicing.Criterion
public import TauCeti.MeasureTheory.Measure.Hausdorff

import TauCeti.MeasureTheory.Function.LocallyIntegrable

/-!
# Federer's criterion on the line: locally finite but infinite perimeter

In `ℝ`, let `s = ⋃_{k ≥ 1} (1/(2k + 1), 1/(2k))` (`intervals`) and `Ω = (0, 1)`
(`unitIoo`). This file checks the second Check of §5.4 of
`TauCetiRoadmap/GeometricMeasureTheory/README.md`:

* every compact `K ⊆ (0, 1)` meets the essential boundary of `s` in finitely many points
  (`encard_essentialBoundary_inter_ne_top`), so Federer's criterion
  `TauCeti.exists_perimeter_ne_top_of_euclideanHausdorffMeasure_essentialBoundary_inter_ne_top`
  gives locally finite perimeter in `(0, 1)` (`exists_perimeter_ne_top`);
* `P(s; (0, 1)) = ∞` (`perimeter_eq_top`), since each window `(1/(2k + 3), 1/(2k + 1))` meets `s`
  and its complement in positive measure and so carries perimeter at least `1`;
* this equals `H⁰` of the essential boundary in `(0, 1)`, an infinite set
  (`perimeter_eq_euclideanHausdorffMeasure`, `infinite_essentialBoundary_inter`).
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace Module
open scoped ENNReal

namespace TauCeti.Examples.FedererCriterionLine

/-- The interval `(1/(2k + 3), 1/(2k + 2))`, the `(k + 1)`-st interval of the Check. -/
noncomputable def piece (k : ℕ) : Set ℝ := Ioo (1 / (2 * k + 3)) (1 / (2 * k + 2))

/-- The set `⋃_{k ≥ 1} (1/(2k + 1), 1/(2k))`. -/
noncomputable def intervals : Set ℝ := ⋃ k : ℕ, piece k

/-- The open interval `(0, 1)`. -/
def unitIoo : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩

/-- The window `(1/(2k + 3), 1/(2k + 1))` around the left end of the gap `[1/(2k + 2), 1/(2k + 1)]`
and the interval `piece k`. -/
noncomputable def window (k : ℕ) : Opens ℝ := ⟨Ioo (1 / (2 * k + 3)) (1 / (2 * k + 1)), isOpen_Ioo⟩

theorem measurableSet_intervals : MeasurableSet intervals :=
  MeasurableSet.iUnion fun _ => measurableSet_Ioo

/-- The gaps `(1/(2k + 2), 1/(2k + 1))` lie outside `intervals`. -/
theorem Ioo_subset_compl_intervals (k : ℕ) :
    Ioo (1 / (2 * (k : ℝ) + 2)) (1 / (2 * k + 1)) ⊆ intervalsᶜ := by
  rintro x ⟨hx₁, hx₂⟩ hx
  obtain ⟨j, hj₁, hj₂⟩ := mem_iUnion.1 hx
  rcases le_or_gt k j with hkj | hjk
  · have : (k : ℝ) ≤ j := by exact_mod_cast hkj
    have : 1 / (2 * (j : ℝ) + 2) ≤ 1 / (2 * k + 2) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 / (2 * j + 3) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith

private theorem volume_ne_zero_of_Ioo_subset {a b : ℝ} {t : Set ℝ} (hab : a < b)
    (h : Ioo a b ⊆ t) : volume t ≠ 0 :=
  ((ENNReal.ofReal_pos.2 (sub_pos.2 hab)).trans_le
    (by rw [← Real.volume_Ioo]; exact measure_mono h)).ne'

/-- Each window carries perimeter at least `1`. -/
theorem one_le_perimeter_window (k : ℕ) : 1 ≤ perimeter volume (window k) intervals := by
  have h₁ : 1 / (2 * (k : ℝ) + 3) < 1 / (2 * k + 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have h₂ : 1 / (2 * (k : ℝ) + 2) < 1 / (2 * k + 1) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  refine Real.one_le_perimeter_of_ordConnected measurableSet_intervals.nullMeasurableSet
    ordConnected_Ioo (volume_ne_zero_of_Ioo_subset h₁ fun x hx => ⟨mem_iUnion.2 ⟨k, hx⟩, ?_⟩)
    (volume_ne_zero_of_Ioo_subset h₂ fun x hx => ⟨Ioo_subset_compl_intervals k hx, ?_⟩)
  · exact ⟨hx.1, hx.2.trans h₂⟩
  · exact ⟨h₁.trans hx.1, hx.2⟩

/-- Distinct windows are disjoint. -/
theorem disjoint_window {j k : ℕ} (hjk : j < k) : Disjoint (window j) (window k) := by
  have hset : Disjoint (window j : Set ℝ) (window k) := by
    refine disjoint_left.2 fun x hj hk => ?_
    have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 / (2 * j + 3) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    exact absurd (hj.1.trans hk.2) (not_lt.2 this)
  rw [disjoint_iff, ← SetLike.coe_set_eq]
  simpa [← disjoint_iff_inter_eq_empty] using hset

/-- The first `N` windows carry perimeter at least `N`. -/
theorem natCast_le_perimeter_sup_window (N : ℕ) :
    (N : ℝ≥0∞) ≤ perimeter volume ((Finset.range N).sup window) intervals := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hdisj : Disjoint ((Finset.range N).sup window) (window N) :=
      Finset.disjoint_sup_left.2 fun j hj => disjoint_window (Finset.mem_range.1 hj)
    have hli : LocallyIntegrableOn (intervals.indicator (1 : ℝ → ℝ))
        (((Finset.range N).sup window ⊔ window N : Opens ℝ) : Set ℝ) volume :=
      locallyIntegrableOn_indicator_const measurableSet_intervals.nullMeasurableSet 1
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm, perimeter_def,
      totalVariationOn_sup_of_disjoint hli hdisj,
      ← perimeter_def, ← perimeter_def, Nat.cast_add, Nat.cast_one]
    exact add_le_add ih (one_le_perimeter_window N)

/-- **Infinite perimeter.** `P(s; (0, 1)) = ∞`. -/
theorem perimeter_eq_top : perimeter volume unitIoo intervals = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  have hsub : (Finset.range ⌈(r : ℝ)⌉₊).sup window ≤ unitIoo := by
    refine Finset.sup_le fun k _ x hx => ⟨(by positivity : (0 : ℝ) < 1 / (2 * k + 3)).trans hx.1,
      hx.2.trans_le ?_⟩
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc (r : ℝ≥0∞) ≤ (⌈(r : ℝ)⌉₊ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    _ ≤ _ := natCast_le_perimeter_sup_window _
    _ ≤ _ := perimeter_mono hsub

/-- **The perimeter is `H⁰` of the essential boundary.** Both are infinite: the sharp bound
`TauCeti.perimeter_le_euclideanHausdorffMeasure_essentialBoundary_inter` forces
`H⁰(∂ᵉs ∩ (0, 1)) = ∞`. -/
theorem perimeter_eq_euclideanHausdorffMeasure :
    perimeter volume unitIoo intervals =
      μHE[0] (essentialBoundary volume intervals ∩ unitIoo) := by
  have h := perimeter_le_euclideanHausdorffMeasure_essentialBoundary_inter unitIoo
    measurableSet_intervals.nullMeasurableSet
  rw [finrank_self, Nat.sub_self, perimeter_eq_top, top_le_iff] at h
  rw [perimeter_eq_top, h]

/-- The essential boundary of `s` in `(0, 1)` is infinite. -/
theorem infinite_essentialBoundary_inter :
    (essentialBoundary volume intervals ∩ unitIoo).Infinite := by
  have h := perimeter_eq_euclideanHausdorffMeasure
  rw [perimeter_eq_top, Measure.euclideanHausdorffMeasure_zero, hausdorffMeasure_zero_apply]
    at h
  exact encard_eq_top_iff.1 (by exact_mod_cast h.symm)

/-- On `(t, ∞)` with `1/(2N + 2) ≤ t`, the set `s` agrees with its first `N` intervals. -/
private theorem intervals_inter_Ioi {t : ℝ} {N : ℕ} (hN : 1 / (2 * (N : ℝ) + 2) ≤ t) :
    intervals ∩ Ioi t = (⋃ k ∈ Finset.range N, piece k) ∩ Ioi t := by
  refine Subset.antisymm (fun x ⟨hx, hxt⟩ => ⟨?_, hxt⟩)
    (inter_subset_inter_left _ (iUnion₂_subset fun k _ => subset_iUnion piece k))
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  refine mem_biUnion (Finset.mem_range.2 ?_) hk
  by_contra! hNk
  have : (N : ℝ) ≤ k := by exact_mod_cast hNk
  have : 1 / (2 * (k : ℝ) + 2) ≤ 1 / (2 * N + 2) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact absurd (hk.2.trans_le (this.trans hN)) (not_lt.2 hxt.le)

/-- The frontier of the first `N` intervals is finite. -/
private theorem finite_frontier_biUnion (N : ℕ) :
    (frontier (⋃ k ∈ Finset.range N, piece k)).Finite := by
  refine ((Finset.range N).finite_toSet.biUnion
    (t := fun k : ℕ => ({1 / (2 * (k : ℝ) + 3), 1 / (2 * (k : ℝ) + 2)} : Set ℝ))
    fun k _ => toFinite _).subset ?_
  have ho : IsOpen (⋃ k ∈ Finset.range N, piece k) :=
    isOpen_biUnion fun k _ => isOpen_Ioo
  rw [ho.frontier_eq, Finset.closure_biUnion]
  rintro x ⟨hx, hxs⟩
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.1 hx
  have hlt : 1 / (2 * (k : ℝ) + 3) < 1 / (2 * k + 2) :=
    one_div_lt_one_div_of_lt (by positivity) (by linarith)
  rw [piece, closure_Ioo hlt.ne] at hxk
  refine mem_biUnion hk ?_
  have hxk' : x ∉ piece k := fun h => hxs (mem_biUnion hk h)
  rcases hxk.1.eq_or_lt with h | h
  · exact Or.inl h.symm
  rcases hxk.2.eq_or_lt with h' | h'
  · exact Or.inr h'
  exact absurd ⟨h, h'⟩ hxk'

/-- Every compact subset of `(0, 1)` meets the essential boundary of `s` in finitely many
points. -/
theorem encard_essentialBoundary_inter_ne_top {K : Set ℝ} (hK : IsCompact K)
    (hKΩ : K ⊆ unitIoo) : (essentialBoundary volume intervals ∩ K).encard ≠ ⊤ := by
  rw [Ne, encard_eq_top_iff, not_infinite]
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨δ, hδK, hδ⟩ := hK.exists_isLeast hne
  have hδ0 : 0 < δ := (hKΩ hδK).1
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt (half_pos hδ0)
  have hN' : 1 / (2 * (N : ℝ) + 2) ≤ δ / 2 := by
    refine (one_div_le_one_div_of_le (by positivity) ?_).trans hN.le
    linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]
  have hKt : K ⊆ Ioi (δ / 2) := fun x hx => (half_lt_self hδ0).trans_le (hδ hx)
  refine (finite_frontier_biUnion N).subset fun x ⟨hx, hxK⟩ => ?_
  have hxt : x ∈ Ioi (δ / 2) := hKt hxK
  have h := frontier_inter_open_inter (s := intervals) isOpen_Ioi (t := Ioi (δ / 2))
  rw [intervals_inter_Ioi hN', frontier_inter_open_inter isOpen_Ioi] at h
  have : x ∈ frontier intervals ∩ Ioi (δ / 2) := ⟨essentialBoundary_subset_frontier hx, hxt⟩
  exact (h ▸ this).1

/-- **Federer's criterion gives locally finite perimeter.** Every compact `K ⊆ (0, 1)` has an
open neighbourhood in which `s` has finite perimeter. -/
theorem exists_perimeter_ne_top {K : Set ℝ} (hK : IsCompact K) (hKΩ : K ⊆ unitIoo) :
    ∃ U : Opens ℝ, K ⊆ (U : Set ℝ) ∧ perimeter volume U intervals ≠ ∞ := by
  refine exists_perimeter_ne_top_of_euclideanHausdorffMeasure_essentialBoundary_inter_ne_top
    measurableSet_intervals.nullMeasurableSet (fun K' hK' hK'Ω => ?_) hK hKΩ
  rw [finrank_self, Nat.sub_self, Measure.euclideanHausdorffMeasure_zero,
    hausdorffMeasure_zero_apply]
  exact_mod_cast encard_essentialBoundary_inter_ne_top hK' hK'Ω

end TauCeti.Examples.FedererCriterionLine
