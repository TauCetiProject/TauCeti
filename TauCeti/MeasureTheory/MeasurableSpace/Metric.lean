/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
public import Mathlib.MeasureTheory.Function.SimpleFuncDense
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.Topology.UniformSpace.Cauchy
public import TauCeti.Topology.MetricSpace.SeparatedBalls
import Mathlib.Topology.UniformSpace.HeineCantor
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator

/-!
# Measurable discretization of pseudometric spaces

This file provides measurable maps onto finitely many points of a pseudometric space whose open
sets are measurable: a nearest-point projection onto any nonempty finite set, a finite
measurable approximation of a totally bounded space, and a measurable partition of a measurable
totally bounded set into finitely many small cells. Such a partition of a compact set
approximates a function continuous on a compact product uniformly by functions that are piecewise
constant in the first variable.

## Main statements

* `TauCeti.exists_measurable_edist_eq_infEDist` — a nonempty finite set carries a measurable
  nearest-point projection, sending every point to a point of the set at minimal distance.
* `TauCeti.exists_measurable_dist_lt` — a totally bounded pseudometric space admits a measurable map
  to a finite type whose indexed approximation point is uniformly close to every point.
* `TotallyBounded.exists_measurable_dist_lt` — a measurable totally bounded set is the union of
  finitely many measurable cells of small diameter, labelled by a measurable map that gives its
  complement a label of its own.
* `TotallyBounded.exists_measurable_partition_ball` — a measurable totally bounded set is the
  disjoint union of finitely many measurable pieces, each inside a small ball centred in the set.
* `IsCompact.exists_enorm_sub_sum_indicator_le` — a function continuous on a product of compact
  sets and zero outside it is uniformly close to a function that is piecewise constant in the
  first variable on a finite measurable partition, with values the slices at the centres.
* `TauCeti.measurable_ballIndex` — for `2 s`-separated points `θ i`, the index of the ball of
  radius `s` containing a point is measurable, for an arbitrary index type.
* `TauCeti.nearestIndex` — for finitely many points `θ i` indexed by a nonempty linear order, the
  least index of a nearest point; it is measurable (`TauCeti.measurable_nearestIndex`), minimizes
  the distance (`TauCeti.dist_nearestIndex_le`), and lands within twice the distance to any
  `θ j` (`TauCeti.dist_nearestIndex_le_two_mul`).
-/

public section

noncomputable section

open Metric Set Function
open scoped ENNReal NNReal

namespace TauCeti

universe u

/-- **A measurable nearest-point projection onto a finite set.** In a pseudo-extended-metric space
whose open sets are measurable, every nonempty finite set `s` is the target of a measurable map
`T` that sends each point `x` to a point of `s` nearest to it: `edist x (T x) = infEDist x s`. -/
theorem exists_measurable_edist_eq_infEDist {X : Type u} [PseudoEMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {s : Finset X} (hs : s.Nonempty) :
    ∃ T : X → X, Measurable T ∧ (∀ x, T x ∈ s) ∧ ∀ x, edist x (T x) = infEDist x s := by
  obtain ⟨x₀, hx₀⟩ := hs
  set e : ℕ → X := fun k ↦ s.toList.getD k x₀ with he
  have he_mem (k : ℕ) : e k ∈ s := by
    rcases lt_or_ge k s.toList.length with hk | hk
    · simpa [he, List.getElem?_eq_getElem hk] using Finset.mem_toList.1 (List.getElem_mem hk)
    · simpa [he, List.getElem?_eq_none hk] using hx₀
  have he_surj {y : X} (hy : y ∈ s) : ∃ k ≤ s.card, e k = y := by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hy)
    exact ⟨k, (Finset.length_toList s ▸ hk).le, by simp [he, List.getElem?_eq_getElem hk]⟩
  set T := MeasureTheory.SimpleFunc.nearestPt e s.card with hT
  have hTe (x : X) : T x = e (MeasureTheory.SimpleFunc.nearestPtInd e s.card x) := by
    simp [hT, MeasureTheory.SimpleFunc.nearestPt]
  refine ⟨T, T.measurable, fun x ↦ hTe x ▸ he_mem _, fun x ↦ le_antisymm ?_ ?_⟩
  · refine le_infEDist.2 fun y hy ↦ ?_
    obtain ⟨k, hk, rfl⟩ := he_surj hy
    simpa only [edist_comm] using MeasureTheory.SimpleFunc.edist_nearestPt_le e x hk
  · exact infEDist_le_edist_of_mem (hTe x ▸ he_mem _)

/-- A totally bounded pseudometric space admits, up to any positive error, an indexed finite family
of approximation points and a measurable map assigning every point to a nearby one. -/
theorem exists_measurable_dist_lt (X : Type u) [PseudoMetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (hX : TotallyBounded (Set.univ : Set X)) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (v : Fin n → X) (q : X → Fin n), Measurable q ∧ ∀ x, dist x (v (q x)) < δ := by
  rcases isEmpty_or_nonempty X with h | ⟨⟨x₀⟩⟩
  · exact ⟨0, isEmptyElim, isEmptyElim, measurable_of_countable _, isEmptyElim⟩
  obtain ⟨s, -, hs, hcover⟩ := finite_approx_of_totallyBounded hX δ hδ
  have := hs.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin s
  have hcover (x : X) : ∃ i : Fin n, dist x (e.symm i) < δ := by
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover (mem_univ x))
    exact ⟨e ⟨z, hz⟩, by simpa using hxz⟩
  have : NeZero n := ⟨fun hn ↦ (hn ▸ (hcover x₀).choose).elim0⟩
  -- enumerate the approximation points along `ℕ` and take the index of a nearest one
  set v : ℕ → X := fun k ↦ e.symm (Fin.ofNat n k) with hv
  set r := MeasureTheory.SimpleFunc.nearestPtInd v n
  refine ⟨n, fun i ↦ e.symm i, fun x ↦ Fin.ofNat n (r x),
    (measurable_of_countable (Fin.ofNat n)).comp r.measurable, fun x ↦ ?_⟩
  obtain ⟨i, hi⟩ := hcover x
  have hle : edist (v (r x)) x ≤ edist (v i) x := by
    simpa [MeasureTheory.SimpleFunc.nearestPt] using
      MeasureTheory.SimpleFunc.edist_nearestPt_le v x i.isLt.le
  rw [← edist_lt_ofReal, edist_comm]
  exact hle.trans_lt (by simpa [hv, edist_comm, edist_lt_ofReal] using hi)

/-- **A measurable partition of a totally bounded set into small cells.** In a pseudometric space
whose open sets are measurable, a measurable totally bounded set `s` admits, for every `δ > 0`, a
measurable map `q : X → Fin (n + 1)` that gives the complement of `s` the label `Fin.last n` and
gives two points of `s` the same label only when they are at distance less than `δ`. -/
theorem _root_.TotallyBounded.exists_measurable_dist_lt {X : Type u} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {s : Set X} (hs : TotallyBounded s)
    (hsm : MeasurableSet s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (q : X → Fin (n + 1)), Measurable q ∧ (∀ x, q x = Fin.last n ↔ x ∉ s) ∧
      ∀ x ∈ s, ∀ y ∈ s, q x = q y → dist x y < δ := by
  classical
  have hs' : TotallyBounded (univ : Set s) :=
    (totallyBounded_image_iff isUniformEmbedding_subtypeVal.isUniformInducing).1 (by simpa)
  obtain ⟨n, v, r, hr, hrv⟩ := TauCeti.exists_measurable_dist_lt s hs' (half_pos hδ)
  refine ⟨n, fun x ↦ if hx : x ∈ s then (r ⟨x, hx⟩).castSucc else Fin.last n,
    ((measurable_of_countable Fin.castSucc).comp hr).dite measurable_const hsm,
    fun x ↦ ?_, fun x hx y hy hxy ↦ ?_⟩
  · by_cases hx : x ∈ s <;> simp [hx, Fin.castSucc_ne_last]
  · simp only [hx, hy, dite_true, Fin.castSucc_inj] at hxy
    -- both points lie within `δ / 2` of the approximation point of their common label
    have hx' := hrv ⟨x, hx⟩
    have hy' := hrv ⟨y, hy⟩
    rw [hxy] at hx'
    rw [Subtype.dist_eq] at hx' hy'
    linarith [dist_triangle_right x y (v (r ⟨y, hy⟩) : X)]

/-- **A measurable partition of a totally bounded set into pieces of small balls.** In a
pseudometric space whose open sets are measurable, a measurable totally bounded set `s` is, for
every `δ > 0`, the union of finitely many pairwise disjoint measurable pieces
`P i ⊆ s ∩ ball (c i) δ` with centres `c i ∈ s`. -/
theorem _root_.TotallyBounded.exists_measurable_partition_ball {X : Type u} [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {s : Set X} (hs : TotallyBounded s)
    (hsm : MeasurableSet s) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (n : ℕ) (c : Fin n → X) (P : Fin n → Set X), (∀ i, c i ∈ s) ∧
      (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ s ∩ ball (c i) δ) ∧
      Pairwise (Disjoint on P) ∧ ⋃ i, P i = s := by
  obtain ⟨T, hTs, hT, hcover⟩ := finite_approx_of_totallyBounded hs δ hδ
  have := hT.to_subtype
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin T
  set c : Fin n → X := fun i ↦ e.symm i
  set f : Fin n → Set X := fun i ↦ s ∩ ball (c i) δ
  have hf : ∀ i, MeasurableSet (f i) := fun i ↦ hsm.inter isOpen_ball.measurableSet
  refine ⟨n, c, disjointed f, fun i ↦ hTs (e.symm i).property, fun i ↦ ?_,
    fun i ↦ disjointed_subset f i, disjoint_disjointed f, ?_⟩
  · rw [disjointed_eq_inter_compl]
    exact (hf i).inter (.iInter fun j ↦ .iInter fun _ ↦ (hf j).compl)
  · rw [iUnion_disjointed]
    refine Subset.antisymm (iUnion_subset fun i ↦ inter_subset_left) fun x hx ↦ ?_
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hcover hx)
    exact mem_iUnion.2 ⟨e ⟨y, hy⟩, hx, by simpa [c] using hxy⟩

/-- **Uniform approximation by functions piecewise constant in the first variable.** A function
`K` continuous on a product `s ×ˢ t` of compact sets and zero outside it is within `ε` of a
function that is piecewise constant in the first variable on a finite measurable partition of
`s`, equal on the piece `P i` to the slice `K (c i)` at a point `c i ∈ s`: the difference is at
most `ε` on `s ×ˢ t` and vanishes outside it. -/
theorem _root_.IsCompact.exists_enorm_sub_sum_indicator_le {α β E : Type*} [MetricSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [PseudoMetricSpace β]
    [SeminormedAddCommGroup E] {K : α → β → E} {s : Set α} {t : Set β} (hs : IsCompact s)
    (ht : IsCompact t) (hKc : ContinuousOn (uncurry K) (s ×ˢ t))
    (hK0 : ∀ x y, (x, y) ∉ s ×ˢ t → K x y = 0) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (n : ℕ) (c : Fin n → α) (P : Fin n → Set α), (∀ i, c i ∈ s) ∧
      (∀ i, MeasurableSet (P i)) ∧ (∀ i, P i ⊆ s) ∧ Pairwise (Disjoint on P) ∧
      ∀ x y, ‖K x y - ∑ i, (P i).indicator (fun _ ↦ K (c i) y) x‖ₑ ≤
        s.indicator (fun _ ↦ t.indicator (fun _ ↦ (ε : ℝ≥0∞)) y) x := by
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((hs.prod ht).uniformContinuousOn_of_continuous hKc) ε (by exact_mod_cast hε)
  obtain ⟨n, c, P, hcs, hPm, hPs, hPd, hPU⟩ :=
    hs.totallyBounded.exists_measurable_partition_ball hs.isClosed.measurableSet hδ
  refine ⟨n, c, P, hcs, hPm, fun i x hx ↦ (hPs i hx).1, hPd, fun x y ↦ ?_⟩
  by_cases hx : x ∈ s
  · obtain ⟨i, hi⟩ := mem_iUnion.1 (hPU.symm ▸ hx)
    rw [Finset.sum_indicator_apply_of_mem (hPd.set_pairwise _) (Finset.mem_univ i) hi,
      indicator_of_mem hx]
    by_cases hy : y ∈ t
    · rw [indicator_of_mem hy, ← ofReal_norm, ← dist_eq_norm]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      have h := hunif (x, y) ⟨hx, hy⟩ (c i, y) ⟨hcs i, hy⟩ (by
        rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]
        exact (hPs i hi).2)
      simpa using h.le
    · simp [hK0 x y fun h ↦ hy h.2, hK0 (c i) y fun h ↦ hy h.2]
  · simp [Finset.sum_eq_zero fun i _ ↦ indicator_of_notMem (fun h ↦ hx (hPs i h).1) _,
      hK0 x y fun h ↦ hx h.1]

/-- For `2 s`-separated points, `ballIndex θ s i₀` is measurable, for every σ-algebra on the
index set and with no countability assumption: every preimage is the union of an open set and a
closed set. -/
@[fun_prop]
theorem measurable_ballIndex {ι Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [OpensMeasurableSpace Y] [MeasurableSpace ι] {θ : ι → Y} {s : ℝ}
    (hθ : ∀ i j, i ≠ j → 2 * s ≤ dist (θ i) (θ j)) (i₀ : ι) :
    Measurable (ballIndex θ s i₀) := fun A _ ↦ by
  rw [ballIndex_preimage hθ i₀ A]
  exact (isOpen_biUnion fun i _ ↦ isOpen_ball).measurableSet.union
    ((MeasurableSet.const _).inter
      (isClosed_iInter fun i ↦ isOpen_ball.isClosed_compl).measurableSet)

section NearestIndex

variable {ι Y : Type*} [PseudoMetricSpace Y] [Fintype ι] [Nonempty ι] [LinearOrder ι]

open scoped Classical in
/-- The index of a nearest point to `y` among the `θ i`: the least `i`, for the linear order of
`ι`, such that `dist y (θ i) ≤ dist y (θ j)` for every `j`. -/
def nearestIndex (θ : ι → Y) (y : Y) : ι :=
  (Finset.univ.filter fun i ↦ ∀ j, dist y (θ i) ≤ dist y (θ j)).min' <| by
    obtain ⟨i, -, hi⟩ :=
      Finset.univ.exists_min_image (fun i ↦ dist y (θ i)) Finset.univ_nonempty
    exact ⟨i, by simpa using hi⟩

/-- `nearestIndex θ y = i` exactly when `θ i` is a nearest point to `y` and every index of a
nearest point is at least `i`. -/
theorem nearestIndex_eq_iff {θ : ι → Y} {y : Y} {i : ι} :
    nearestIndex θ y = i ↔ (∀ j, dist y (θ i) ≤ dist y (θ j)) ∧
      ∀ j, (∀ k, dist y (θ j) ≤ dist y (θ k)) → i ≤ j := by
  simp [nearestIndex, Finset.min'_eq_iff]

/-- `θ (nearestIndex θ y)` is a nearest point to `y`. -/
theorem dist_nearestIndex_le (θ : ι → Y) (y : Y) (j : ι) :
    dist y (θ (nearestIndex θ y)) ≤ dist y (θ j) :=
  (nearestIndex_eq_iff.1 rfl).1 j

/-- The nearest point to `y` is within twice the distance from `y` to `θ j` of `θ j`. -/
theorem dist_nearestIndex_le_two_mul (θ : ι → Y) (y : Y) (j : ι) :
    dist (θ (nearestIndex θ y)) (θ j) ≤ 2 * dist y (θ j) := by
  calc dist (θ (nearestIndex θ y)) (θ j) ≤ dist y (θ (nearestIndex θ y)) + dist y (θ j) :=
        dist_triangle_left _ _ _
    _ ≤ 2 * dist y (θ j) := by linarith [dist_nearestIndex_le θ y j]

/-- `nearestIndex θ` is measurable, for every σ-algebra on the index set: each fibre is a finite
Boolean combination of the closed sets `{y | dist y (θ j) ≤ dist y (θ k)}`. -/
@[fun_prop]
theorem measurable_nearestIndex [MeasurableSpace Y] [OpensMeasurableSpace Y] [MeasurableSpace ι]
    (θ : ι → Y) : Measurable (nearestIndex θ) := by
  have hle (j k : ι) : Measurable fun y ↦ dist y (θ j) ≤ dist y (θ k) :=
    (continuous_id.dist continuous_const).measurable.le'
      (continuous_id.dist continuous_const).measurable
  refine measurable_to_countable' fun i ↦ ?_
  simp_rw [preimage, mem_singleton_iff, nearestIndex_eq_iff]
  exact (Measurable.forall fun k ↦ hle i k).and
    (Measurable.forall fun j ↦ (Measurable.forall fun k ↦ hle j k).imp measurable_const) |>.setOf

end NearestIndex

end TauCeti
