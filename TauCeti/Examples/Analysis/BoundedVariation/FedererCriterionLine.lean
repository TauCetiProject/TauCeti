/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Real
public import TauCeti.Analysis.BoundedVariation.Slicing.Criterion
public import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Federer's criterion on the line: locally finite but infinite perimeter

In `ℝ`, let `s = ⋃_{k ≥ 1} (1/(2k + 1), 1/(2k))` (`intervals`) and `Ω = (0, 1)` (`unitIoo`). The
set `s` has locally finite perimeter in `(0, 1)` but infinite perimeter there, so Federer's
criterion gives only local finiteness:

* every compact `K ⊆ (0, 1)` meets the essential boundary of `s` in finitely many points
  (`encard_essentialBoundary_inter_ne_top`), so Federer's criterion
  `TauCeti.exists_perimeter_ne_top_of_euclideanHausdorffMeasure_essentialBoundary_inter_ne_top`
  gives locally finite perimeter in `(0, 1)` (`exists_perimeter_ne_top`);
* `P(s; (0, 1)) = ∞` (`perimeter_eq_top`), since each window `(1/(2k + 3), 1/(2k + 1))` meets `s`
  and its complement in positive measure and so carries perimeter at least `1`;
* this equals `H⁰` of the essential boundary in `(0, 1)`, an infinite set
  (`perimeter_eq_euclideanHausdorffMeasure`, `infinite_essentialBoundary_inter`).
-/

public section

open MeasureTheory Set TopologicalSpace Module
open scoped ENNReal

namespace TauCeti.Examples.FedererCriterionLine

/-- The interval `(1/(2k + 3), 1/(2k + 2))`, the `(k + 1)`-st interval of `intervals`. -/
private noncomputable def piece (k : ℕ) : Set ℝ := Ioo (1 / (2 * k + 3)) (1 / (2 * k + 2))

/-- The set `⋃_{k ≥ 1} (1/(2k + 1), 1/(2k))`. -/
noncomputable def intervals : Set ℝ := ⋃ k : ℕ, piece k

/-- `x ∈ intervals` exactly when `x ∈ (1/(2k + 3), 1/(2k + 2))` for some `k : ℕ`. -/
theorem mem_intervals_iff {x : ℝ} :
    x ∈ intervals ↔ ∃ k : ℕ, x ∈ Ioo (1 / (2 * (k : ℝ) + 3)) (1 / (2 * k + 2)) :=
  mem_iUnion

/-- The open interval `(0, 1)`. -/
def unitIoo : Opens ℝ := ⟨Ioo 0 1, isOpen_Ioo⟩

/-- `unitIoo` is the open interval `(0, 1)`. -/
@[simp]
theorem coe_unitIoo : (unitIoo : Set ℝ) = Ioo 0 1 :=
  (rfl)

/-- The window `(1/(2k + 3), 1/(2k + 1))` around the left end of the gap `[1/(2k + 2), 1/(2k + 1)]`
and the interval `piece k`. -/
private noncomputable def window (k : ℕ) : Opens ℝ :=
  ⟨Ioo (1 / (2 * k + 3)) (1 / (2 * k + 1)), isOpen_Ioo⟩

/-- `window k` is the open interval `(1/(2k + 3), 1/(2k + 1))`. -/
@[simp]
private theorem coe_window (k : ℕ) :
    (window k : Set ℝ) = Ioo (1 / (2 * (k : ℝ) + 3)) (1 / (2 * k + 1)) :=
  (rfl)

theorem measurableSet_intervals : MeasurableSet intervals := by
  rw [intervals]
  exact MeasurableSet.iUnion fun k => by rw [piece]; exact measurableSet_Ioo

/-- For `j < k`, the right end `1/(2k + 1)` of the `k`-th gap lies left of `piece j`. -/
private theorem one_div_two_mul_add_one_le_of_lt {j k : ℕ} (hjk : j < k) :
    1 / (2 * (k : ℝ) + 1) ≤ 1 / (2 * j + 3) := by
  have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hjk
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- The gaps `(1/(2k + 2), 1/(2k + 1))` lie outside `intervals`. -/
private theorem Ioo_subset_compl_intervals (k : ℕ) :
    Ioo (1 / (2 * (k : ℝ) + 2)) (1 / (2 * k + 1)) ⊆ intervalsᶜ := by
  rintro x ⟨hx₁, hx₂⟩ hx
  obtain ⟨j, hj₁, hj₂⟩ := mem_intervals_iff.1 hx
  rcases le_or_gt k j with hkj | hjk
  · have : 1 / (2 * (j : ℝ) + 2) ≤ 1 / (2 * k + 2) := by gcongr
    linarith
  · linarith [one_div_two_mul_add_one_le_of_lt hjk]

/-- Each window carries perimeter at least `1`. -/
private theorem one_le_perimeter_window (k : ℕ) :
    1 ≤ perimeter volume (window k) intervals := by
  have h₁ : 1 / (2 * (k : ℝ) + 3) < 1 / (2 * k + 2) := by gcongr; norm_num
  have h₂ : 1 / (2 * (k : ℝ) + 2) < 1 / (2 * k + 1) := by gcongr; norm_num
  have hs : Ioo (1 / (2 * (k : ℝ) + 3)) (1 / (2 * k + 2)) ⊆ intervals ∩ window k := by
    rw [coe_window]
    exact fun x hx => ⟨mem_intervals_iff.2 ⟨k, hx⟩, hx.1, hx.2.trans h₂⟩
  have hc : Ioo (1 / (2 * (k : ℝ) + 2)) (1 / (2 * k + 1)) ⊆ intervalsᶜ ∩ window k := by
    rw [coe_window]
    exact fun x hx => ⟨Ioo_subset_compl_intervals k hx, h₁.trans hx.1, hx.2⟩
  exact Real.one_le_perimeter_of_ordConnected measurableSet_intervals.nullMeasurableSet
    (by rw [coe_window]; exact ordConnected_Ioo)
    (fun h0 => ((Measure.measure_Ioo_pos volume).2 h₁).ne' (measure_mono_null hs h0))
    (fun h0 => ((Measure.measure_Ioo_pos volume).2 h₂).ne' (measure_mono_null hc h0))

/-- Distinct windows are disjoint. -/
private theorem disjoint_window {j k : ℕ} (hjk : j < k) : Disjoint (window j) (window k) :=
  Opens.coe_disjoint.1 <| by
    rw [coe_window, coe_window]
    exact disjoint_left.2 fun _ hj hk =>
      absurd (hj.1.trans hk.2) (not_lt.2 (one_div_two_mul_add_one_le_of_lt hjk))

/-- The first `N` windows carry perimeter at least `N`. -/
private theorem natCast_le_perimeter_sup_window (N : ℕ) :
    (N : ℝ≥0∞) ≤ perimeter volume ((Finset.range N).sup window) intervals := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hdisj : Disjoint ((Finset.range N).sup window) (window N) :=
      Finset.disjoint_sup_left.2 fun j hj => disjoint_window (Finset.mem_range.1 hj)
    rw [Finset.range_add_one, Finset.sup_insert, sup_comm,
      perimeter_sup_of_disjoint measurableSet_intervals.nullMeasurableSet hdisj, Nat.cast_add,
      Nat.cast_one]
    exact add_le_add ih (one_le_perimeter_window N)

/-- **Infinite perimeter.** `P(s; (0, 1)) = ∞`. -/
theorem perimeter_eq_top : perimeter volume unitIoo intervals = ∞ := by
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  have hsub : (Finset.range ⌈(r : ℝ)⌉₊).sup window ≤ unitIoo := by
    refine Finset.sup_le fun k _ => ?_
    rw [← SetLike.coe_subset_coe, coe_window, coe_unitIoo]
    refine Ioo_subset_Ioo (by positivity) ?_
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc (r : ℝ≥0∞) ≤ (⌈(r : ℝ)⌉₊ : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_natCast]
        exact ENNReal.ofReal_le_ofReal (Nat.le_ceil _)
    _ ≤ _ := natCast_le_perimeter_sup_window _
    _ ≤ _ := perimeter_mono hsub

/-- The essential boundary of `s` in `(0, 1)` is infinite. -/
theorem infinite_essentialBoundary_inter :
    (essentialBoundary volume intervals ∩ unitIoo).Infinite := by
  -- The sharp bound `P(s; Ω) ≤ H⁰(∂ᵉs ∩ Ω)` with `P(s; (0, 1)) = ∞`.
  have h := perimeter_le_euclideanHausdorffMeasure_essentialBoundary_inter unitIoo
    measurableSet_intervals.nullMeasurableSet
  rw [perimeter_eq_top, top_le_iff, finrank_self, Nat.sub_self,
    euclideanHausdorffMeasure_zero_apply] at h
  exact encard_eq_top_iff.1 (by exact_mod_cast h)

/-- **The perimeter is `H⁰` of the essential boundary.** `P(s; (0, 1)) = H⁰(∂ᵉs ∩ (0, 1))`; both
sides are `∞`. -/
theorem perimeter_eq_euclideanHausdorffMeasure :
    perimeter volume unitIoo intervals =
      μHE[0] (essentialBoundary volume intervals ∩ unitIoo) := by
  rw [perimeter_eq_top, euclideanHausdorffMeasure_zero_apply,
    infinite_essentialBoundary_inter.encard_eq, ENat.toENNReal_top]

/-- On `(t, ∞)` with `1/(2N + 2) ≤ t`, the set `s` agrees with its first `N` intervals. -/
private theorem intervals_inter_Ioi {t : ℝ} {N : ℕ} (hN : 1 / (2 * (N : ℝ) + 2) ≤ t) :
    intervals ∩ Ioi t = (⋃ k ∈ Finset.range N, piece k) ∩ Ioi t := by
  rw [intervals]
  refine Subset.antisymm (fun x ⟨hx, hxt⟩ => ⟨?_, hxt⟩)
    (inter_subset_inter_left _ (iUnion₂_subset fun k _ => subset_iUnion piece k))
  obtain ⟨k, hk⟩ := mem_iUnion.1 hx
  refine mem_biUnion (Finset.mem_range.2 ?_) hk
  by_contra! hNk
  have : 1 / (2 * (k : ℝ) + 2) ≤ 1 / (2 * N + 2) := by gcongr
  rw [piece] at hk
  exact absurd (hk.2.trans_le (this.trans hN)) (not_lt.2 hxt.le)

/-- The frontier of the first `N` intervals is finite. -/
private theorem finite_frontier_biUnion (N : ℕ) :
    (frontier (⋃ k ∈ Finset.range N, piece k)).Finite :=
  ((Finset.range N).finite_toSet.biUnion fun k _ => by
    rw [piece, frontier_Ioo (by gcongr; norm_num)]
    exact toFinite _).subset (Finset.frontier_biUnion_subset _ _)

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
  rw [finrank_self, Nat.sub_self, euclideanHausdorffMeasure_zero_apply]
  exact_mod_cast encard_essentialBoundary_inter_ne_top hK' hK'Ω

end TauCeti.Examples.FedererCriterionLine
