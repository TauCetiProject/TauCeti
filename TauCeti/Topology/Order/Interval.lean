/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact

/-!
# Intervals in order topologies

An unordered closed interval is a neighbourhood of each of its points other than its endpoints.
A nonempty compact subset of an open interval lies in the interior of a smaller closed interval.
Every nonempty closed unbounded order-connected set in a conditionally complete linear order is
a left half-line, a right half-line, or the whole space.

The image of a half-infinite real interval under a continuous strictly monotone map is determined
by its value at the finite endpoint and its limit at infinity.  The endpoint at infinity is omitted
when the limit is finite.

## Main results

* `TauCeti.uIcc_mem_nhds_of_ne` — `uIcc a b` is a neighbourhood of each of its points other than
  `a` and `b`.
* `IsCompact.exists_Icc_between` — a nonempty compact subset of `Ioo a b` lies in the interior of
  a closed interval contained in `Ioo a b`.
* `Set.OrdConnected.eq_Ici_or_eq_Iic_or_eq_univ` — classification of nonempty closed unbounded
  order-connected sets.
* `ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto` — a continuous strictly
  increasing map
  on `Ici p` with a finite limit at `+∞` maps that interval to the half-open interval between its
  endpoint value and its limit.
-/

public section

open Filter Set Topology

namespace TauCeti

/-- An unordered closed interval `uIcc a b` is a neighbourhood of each of its points other than
its endpoints `a` and `b`. -/
theorem uIcc_mem_nhds_of_ne {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {a b t : α} (ht : t ∈ uIcc a b) (ha : t ≠ a) (hb : t ≠ b) :
    uIcc a b ∈ 𝓝 t := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at ht ⊢
    exact Icc_mem_nhds (lt_of_le_of_ne ht.1 ha.symm) (lt_of_le_of_ne ht.2 hb)
  · rw [uIcc_of_ge hab] at ht ⊢
    exact Icc_mem_nhds (lt_of_le_of_ne ht.1 hb.symm) (lt_of_le_of_ne ht.2 ha)

/-- A nonempty compact subset `K` of an open interval `Ioo a b` lies in the interior `Ioo c d` of
a closed interval `Icc c d ⊆ Ioo a b`. This is the interval form of `exists_compact_between`. -/
theorem _root_.IsCompact.exists_Icc_between {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [DenselyOrdered α] {K : Set α} {a b : α} (hK : IsCompact K)
    (hne : K.Nonempty) (hKs : K ⊆ Ioo a b) :
    ∃ c d, K ⊆ Ioo c d ∧ Icc c d ⊆ Ioo a b := by
  obtain ⟨m, hmK, hm⟩ := hK.exists_isLeast hne
  obtain ⟨M, hMK, hM⟩ := hK.exists_isGreatest hne
  obtain ⟨c, hac, hcm⟩ := exists_between (hKs hmK).1
  obtain ⟨d, hMd, hdb⟩ := exists_between (hKs hMK).2
  exact ⟨c, d, fun x hx ↦ ⟨hcm.trans_le (hm hx), (hM hx).trans_lt hMd⟩,
    fun x hx ↦ ⟨hac.trans_le hx.1, hx.2.trans_lt hdb⟩⟩

/-- A nonempty closed order-connected set which is not bounded on both sides is a right
half-line, a left half-line, or the whole space. -/
theorem _root_.Set.OrdConnected.eq_Ici_or_eq_Iic_or_eq_univ
    {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : s.OrdConnected) (hne : s.Nonempty) (hclosed : IsClosed s)
    (hunbounded : ¬(BddBelow s ∧ BddAbove s)) :
    (∃ a, s = Ici a) ∨ (∃ b, s = Iic b) ∨ s = univ := by
  have exists_gt (x : α) (h : ¬BddAbove s) : ∃ y ∈ s, x < y := by
    by_contra! h'
    exact h ⟨x, h'⟩
  have exists_lt (x : α) (h : ¬BddBelow s) : ∃ y ∈ s, y < x := by
    by_contra! h'
    exact h ⟨x, h'⟩
  by_cases hbelow : BddBelow s
  · have habove : ¬BddAbove s := fun h ↦ hunbounded ⟨hbelow, h⟩
    refine Or.inl ⟨sInf s, ?_⟩
    rw [← upperClosure_eq_Ici_csInf hne hbelow hclosed]
    apply Subset.antisymm subset_upperClosure
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hxz⟩ := exists_gt x habove
    exact hs.out hy hz ⟨hyx, hxz.le⟩
  · by_cases habove : BddAbove s
    · refine Or.inr <| Or.inl ⟨sSup s, ?_⟩
      rw [← lowerClosure_eq_Iic_csSup hne habove hclosed]
      apply Subset.antisymm subset_lowerClosure
      rintro x ⟨y, hy, hxy⟩
      obtain ⟨z, hz, hzx⟩ := exists_lt x hbelow
      exact hs.out hz hy ⟨hzx.le, hxy⟩
    · refine Or.inr <| Or.inr <| eq_univ_of_forall fun x ↦ ?_
      obtain ⟨y, hy, hyx⟩ := exists_lt x hbelow
      obtain ⟨z, hz, hxz⟩ := exists_gt x habove
      exact hs.out hy hz ⟨hyx.le, hxz.le⟩

/-- **A continuous strictly increasing map sends a half-line to a half-open interval.** The finite
limit at `+∞` is approached but is not attained. -/
theorem _root_.ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto
    {α β : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [DenselyOrdered α] [NoMaxOrder α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {d : α → β} {p : α} {D : β}
    (hdcont : ContinuousOn d (Ici p))
    (hdmono : StrictMonoOn d (Ici p)) (hdl : Tendsto d atTop (𝓝 D)) :
    d '' Ici p = Ico (d p) D := by
  have hle : ∀ x ∈ Ici p, d x ≤ D := by
    intro x hx
    apply ge_of_tendsto hdl
    filter_upwards [eventually_ge_atTop x] with y hxy
    have hy : y ∈ Ici p := hx.trans hxy
    exact hdmono.monotoneOn hx hy hxy
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have hxp : p ≤ x := hx
    obtain ⟨x1, hx1⟩ := exists_gt x
    have hx1' : x1 ∈ Ici p := hx.trans hx1.le
    have hlt : d x < D := lt_of_lt_of_le
      (hdmono hx hx1' hx1) (hle x1 hx1')
    exact ⟨hdmono.monotoneOn self_mem_Ici hx hxp, hlt⟩
  · exact isPreconnected_Ici.intermediate_value_Ico self_mem_Ici
      (le_principal_iff.mpr (Ici_mem_atTop p)) hdcont hdl

end TauCeti
