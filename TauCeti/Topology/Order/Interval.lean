/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc

/-!
# Intervals in order topologies

An unordered closed interval is a neighbourhood of each of its points other than its endpoints.
Each point of the open interval between two endpoints that avoids a closed set is interior to a
closed subinterval whose interior avoids that set.
A nonempty compact subset of an open interval lies in the interior of a smaller closed interval.
Every nonempty closed unbounded order-connected set in a conditionally complete linear order is
a left half-line, a right half-line, or the whole space.

The image of a half-infinite real interval under a continuous strictly monotone map is determined
by its value at the finite endpoint and its limit at infinity.  The endpoint at infinity is omitted
when the limit is finite.
A continuous strictly increasing real function on a compact interval has a continuous inverse on
its range, extended to the whole line by clamping.

## Main results

* `TauCeti.uIcc_mem_nhds_of_ne` — `uIcc a b` is a neighbourhood of each of its points other than
  `a` and `b`.
* `TauCeti.exists_Icc_subset_uIcc_disjoint` — a point of the open interval between `a` and `b`
  outside a closed set `s` lies in the interior of a closed subinterval of `[[a, b]]` whose
  interior is disjoint from `s`.
* `TauCeti.tendsto_sub_nhdsGT_nhdsWithin_Icc` — the curve `δ ↦ b - δ` tends to `b` within `[a, b]`
  as `δ → 0⁺`.
* `IsCompact.exists_Icc_between` — a nonempty compact subset of `Ioo a b` lies in the interior of
  a closed interval contained in `Ioo a b`.
* `Set.OrdConnected.eq_Ici_or_eq_Iic_or_eq_univ` — classification of nonempty closed unbounded
  order-connected sets.
* `ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto` — a continuous strictly
  increasing map
  on `Ici p` with a finite limit at `+∞` maps that interval to the half-open interval between its
  endpoint value and its limit.
* `TauCeti.exists_continuous_projIcc_inverse` — a continuous strictly increasing real function on
  `[a, b]` has a continuous inverse on its range, clamped to be constant outside it.
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

/-- Around any point `t` of the open interval between `a` and `b` outside a closed set `s` there
is a closed subinterval of `[[a, b]]` whose interior contains `t` and is disjoint from `s`. -/
theorem exists_Icc_subset_uIcc_disjoint {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] {a b t : α} {s : Set α}
    (hs : IsClosed s) (ht : t ∈ Ioo (min a b) (max a b)) (hts : t ∉ s) :
    ∃ c d : α, t ∈ Ioo c d ∧ Icc c d ⊆ uIcc a b ∧ Disjoint s (Ioo c d) := by
  have hmem : Ioo (min a b) (max a b) \ s ∈ 𝓝 t := (isOpen_Ioo.sdiff hs).mem_nhds ⟨ht, hts⟩
  obtain ⟨l, u, ⟨hlt, htu⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨_, ht.1⟩ ⟨_, ht.2⟩).mp hmem
  obtain ⟨c, hlc, hct⟩ := exists_between hlt
  obtain ⟨d, htd, hdu⟩ := exists_between htu
  have hcd : Icc c d ⊆ Ioo (min a b) (max a b) \ s :=
    fun x hx => hsub ⟨hlc.trans_le hx.1, hx.2.trans_lt hdu⟩
  refine ⟨c, d, ⟨hct, htd⟩, fun x hx => Icc_min_max.subset (Ioo_subset_Icc_self (hcd hx).1),
    disjoint_right.mpr fun x hx => (hcd (Ioo_subset_Icc_self hx)).2⟩

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

/-- A continuous strictly increasing function `f` on `[a, b]` has a continuous inverse `τ` on its
range `[c, d]`, extended to all of `ℝ` by being constant outside `[c, d]` (that is, `τ` is the
inverse composed with the clamp `projIcc c d`, whose value is `max c (min d r)`). -/
theorem exists_continuous_projIcc_inverse {f : ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) (hc : f a = c) (hd : f b = d) :
    ∃ τ : ℝ → ℝ, Continuous τ ∧ (∀ r, τ r ∈ Icc a b) ∧
      (∀ r, f (τ r) = max c (min d r)) ∧ ∀ s ∈ Icc a b, τ (f s) = s := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  have hcd : c ≤ d := hc ▸ hd ▸ hm.monotoneOn ha hb hab
  subst hc hd
  let g : Icc a b → Icc (f a) (f b) := fun s ↦
    ⟨f s, hm.monotoneOn ha s.2 s.2.1, hm.monotoneOn s.2 hb s.2.2⟩
  have hg_cont : Continuous g :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.1 hf) _
  have hg_bij : Function.Bijective g := by
    refine ⟨fun s s' h ↦ Subtype.ext (hm.injOn s.2 s'.2 (congrArg Subtype.val h)), fun r ↦ ?_⟩
    obtain ⟨s, hs, hsr⟩ := intermediate_value_Icc hab hf r.2
    exact ⟨⟨s, hs⟩, Subtype.ext hsr⟩
  -- `homeoOfEquivCompactToT2` only adds continuity data to the equivalence `Equiv.ofBijective g`,
  -- and Mathlib states no lemma for its coercion.
  let F : Icc a b ≃ₜ Icc (f a) (f b) :=
    hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)
  have hF (s : Icc a b) : (F s : ℝ) = f s := rfl
  refine ⟨fun r ↦ F.symm (projIcc (f a) (f b) hcd r),
    continuous_subtype_val.comp (F.symm.continuous.comp continuous_projIcc), fun r ↦ (F.symm _).2,
    fun r ↦ ?_, fun s hs ↦ ?_⟩
  · rw [← hF, Homeomorph.apply_symm_apply, coe_projIcc, min_comm]
  · have : projIcc (f a) (f b) hcd (f s) = F ⟨s, hs⟩ :=
      Subtype.ext (by rw [hF, projIcc_of_mem]; exact (F ⟨s, hs⟩).2)
    simp only [this, Homeomorph.symm_apply_apply]

/-- The curve `δ ↦ b - δ` tends to `b` within `[a, b]` as `δ → 0⁺`. -/
theorem tendsto_sub_nhdsGT_nhdsWithin_Icc {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [TopologicalSpace G] [OrderTopology G] {a b : G} (hab : a < b) :
    Tendsto (fun δ : G ↦ b - δ) (𝓝[>] 0) (𝓝[Icc a b] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun δ : G ↦ b - δ) (𝓝 0) (𝓝 (b - 0)) := tendsto_const_nhds.sub tendsto_id
    rw [sub_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hab)] with δ hδ
    exact ⟨le_sub_comm.1 hδ.2.le, sub_le_self _ hδ.1.le⟩

end TauCeti
