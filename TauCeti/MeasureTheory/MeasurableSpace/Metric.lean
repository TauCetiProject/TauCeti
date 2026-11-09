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
  classical
  cases isEmpty_or_nonempty X with
  | inl h =>
      let _ := h
      exact ⟨0, isEmptyElim, isEmptyElim, measurable_of_countable _, isEmptyElim⟩
  | inr h =>
      let _ := h
      obtain ⟨s, -, hs, hcover⟩ :=
        Metric.finite_approx_of_totallyBounded (s := (Set.univ : Set X))
          hX δ hδ
      let t := hs.toFinset
      set n := t.card
      set v : Fin n → X := fun i ↦ (t.equivFin.symm i : X) with hv
      have hcover : ∀ x : X, ∃ i : Fin n, dist x (v i) < δ := by
        intro x
        obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (hcover (Set.mem_univ x))
        have hzt : z ∈ t := by simpa [t] using hz
        exact ⟨t.equivFin ⟨z, hzt⟩, by simpa [hv] using hxz⟩
      have hn : 0 < n := by
        obtain ⟨i, -⟩ := hcover (Classical.arbitrary X)
        exact Fin.pos_iff_nonempty.2 ⟨i⟩
      let e : ℕ → X := fun k ↦ if hk : k < n then v ⟨k, hk⟩ else Classical.arbitrary X
      let N := n - 1
      have hN : N < n := Nat.sub_one_lt hn.ne'
      let nearest := MeasureTheory.SimpleFunc.nearestPtInd e N
      set q : X → Fin n := fun x ↦
        ⟨nearest x, (MeasureTheory.SimpleFunc.nearestPtInd_le e N x).trans_lt hN⟩ with hq
      refine ⟨n, v, q, ?_, fun x ↦ ?_⟩
      · refine measurable_to_countable' fun i ↦ ?_
        have hfib : q ⁻¹' {i} = nearest ⁻¹' {i.val} := by
          ext x
          simp only [Set.mem_preimage, Set.mem_singleton_iff, hq]
          constructor
          · exact fun h ↦ congrArg Fin.val h
          · exact fun h ↦ Fin.ext h
        rw [hfib]
        exact nearest.measurable (MeasurableSet.singleton i.val)
      · obtain ⟨i, hi⟩ := hcover x
        have hle : i.val ≤ N := Nat.le_sub_one_of_lt i.isLt
        have hnear := MeasureTheory.SimpleFunc.edist_nearestPt_le e x hle
        have he : e i.val = v i := by simp [e, i.isLt]
        have hqv : v (q x) = MeasureTheory.SimpleFunc.nearestPt e N x := by
          simp [MeasureTheory.SimpleFunc.nearestPt, hq, nearest, e,
            (MeasureTheory.SimpleFunc.nearestPtInd_le e N x).trans_lt hN]
        rw [← edist_lt_ofReal, hqv, edist_comm]
        exact hnear.trans_lt (edist_lt_ofReal.2 (by simpa [he, dist_comm] using hi))

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
  have hs' : TotallyBounded (univ : Set s) := by
    have :=
      totallyBounded_preimage (isUniformEmbedding_subtype_val (p := (· ∈ s))).isUniformInducing hs
    rwa [Subtype.coe_preimage_self] at this
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
  refine ⟨n, c, disjointed f, fun i ↦ hTs (e.symm i).2, fun i ↦ ?_,
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
    · rw [hK0 x y fun h ↦ hy h.2, hK0 (c i) y fun h ↦ hy h.2, sub_zero, ← ofReal_norm,
        norm_zero, ENNReal.ofReal_zero]
      exact zero_le
  · rw [Finset.sum_eq_zero fun i _ ↦ indicator_of_notMem (fun h ↦ hx (hPs i h).1) _,
      hK0 x y fun h ↦ hx h.1, sub_zero, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
    exact zero_le

end TauCeti
