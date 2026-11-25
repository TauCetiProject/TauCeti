/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc

/-!
# Intervals in order topologies

An unordered closed interval is a neighbourhood of each of its points other than its endpoints.
The frontier of a closed or half-open interval avoids every set that misses both endpoints.
In `ℝ`, an interval with endpoints near a point lies in the ball about that point, and the
interval from a point of an order-connected set to a nearby point of that set stays in the ball
about the first point.
Two points of an order-connected set lie in a closed interval inside the set that is a
neighbourhood of the second point within the set.
Each point of the open interval between two endpoints that avoids a closed set is interior to a
closed subinterval whose interior avoids that set.
A nonempty compact subset of an open interval lies in the interior of a smaller closed interval.
An open set containing a closed interval contains an open interval around it.
Every nonempty closed unbounded order-connected set in a conditionally complete linear order is
a left half-line, a right half-line, or the whole space.

A continuous function on a half-infinite interval, above `v`, tending to `v` at infinity and to `+∞`
at the finite endpoint, has image `Ioi v`.
The image of a half-infinite interval under a continuous strictly monotone map is determined
by its value at the finite endpoint and its limit at infinity.  The endpoint at infinity is omitted
when the limit is finite.
A continuous strictly increasing function on a compact interval has a continuous inverse on
its range, extended to the whole codomain by clamping.
A function continuous on every closed interval `[a, b]` with `b ≥ a` is continuous on `[a, ∞)`.
A path that starts in an open set and leaves it has a first exit time.
A function continuous on `[a, b]` and strictly monotone or antitone on `(a, b)` is so on `[a, b]`.

## Main results

* `ContinuousOn.piecewise_Iic` — paste continuous maps across a closed cut on any set.
* `ContinuousOn.piecewise_Iic_Icc` — the adjacent-interval version, with a conditional join.

* `TauCeti.uIcc_mem_nhds_of_ne` — `uIcc a b` is a neighbourhood of each of its points other than
  `a` and `b`.
* `TauCeti.disjoint_frontier_Icc`, `TauCeti.disjoint_frontier_Ioc` — the frontier of `[a, b]` or
  `(a, b]` avoids a set containing neither `a` nor `b`.
* `Real.Icc_subset_ball` — in `ℝ`, an interval whose endpoints lie within `ε` of `x` is
  contained in `ball x ε`.
* `Set.OrdConnected.uIcc_subset_ball_inter` — in `ℝ`, the interval between a point `x` of an
  order-connected set `s` and a point of `ball x ε ∩ s` lies in `ball x ε ∩ s`.
* `Set.OrdConnected.exists_Icc_mem_nhdsWithin` — for points `a` and `b` of an order-connected
  set `I`, a closed interval in `I` contains both and is a neighbourhood of `b` within `I`.
* `TauCeti.continuousOn_Ici_of_forall_Icc` — continuity on `Ici a` from continuity on `Icc a b`
  for every `b ≥ a`.
* `TauCeti.exists_Icc_subset_uIcc_disjoint` — a point of the open interval between `a` and `b`
  outside a closed set `s` lies in the interior of a closed subinterval of `[[a, b]]` whose
  interior is disjoint from `s`.
* `TauCeti.exists_Icc_mem_subset_of_mem_nhdsWithin_Icc` — every neighbourhood of `t₀ ∈ [u, v]`
  (`u < v`) within `[u, v]` contains a nondegenerate closed subinterval `[p, q] ⊆ [u, v]` that is
  itself a neighbourhood of `t₀` within `[u, v]`.
* `TauCeti.tendsto_sub_nhdsGT_nhdsWithin_Icc` — the curve `δ ↦ b - δ` tends to `b` within `[a, b]`
  as `δ → 0⁺`.
* `TauCeti.continuous_neg_Ioo` — negation maps the symmetric open interval `(-a, a)` continuously
  to itself.
* `IsCompact.exists_Icc_between` — a nonempty compact subset of `Ioo a b` lies in the interior of
  a closed interval contained in `Ioo a b`.
* `IsOpen.exists_Ioo_subset_of_uIcc_subset` — an open set containing `[[a, b]]` contains an open
  interval around it.
* `Set.OrdConnected.eq_Ici_or_eq_Iic_or_eq_univ` — classification of nonempty closed unbounded
  order-connected sets.
* `ContinuousOn.apply_ne_apply_of_injOn_Ico` — a continuous function injective on `[a, b)` takes
  different values at `a` and `b`.
* `ContinuousOn.strictMonoOn_Icc_of_strictMonoOn_Ioo`,
  `ContinuousOn.strictAntiOn_Icc_of_strictAntiOn_Ioo` — a function continuous on `[a, b]` and
  strictly monotone (antitone) on `(a, b)` is strictly monotone (antitone) on `[a, b]`.
* `ContinuousOn.image_Ici_of_strictMonoOn_of_tendsto` — a continuous strictly increasing map on
  `Ici p` with a finite limit at `+∞` maps that interval to the half-open interval between its
  endpoint value and its limit.
* `ContinuousOn.image_Ioi_eq_Ioi_of_tendsto`, `ContinuousOn.image_Iio_eq_Ioi_of_tendsto` — a
  continuous function on a half-infinite interval that stays above `v`, tends to `v` at infinity
  and to `+∞` at the finite endpoint has image `Ioi v`.
* `TauCeti.exists_continuous_projIcc_inverse` — a continuous strictly increasing function on
  `[a, b]` has a continuous inverse on its range, clamped to be constant outside it.
* `IsOpen.exists_first_exit` — a path continuous on `[a, b]` that starts in an open set and leaves
  it has a first exit time.
* `TauCeti.locallyFinite_Icc_of_tendsto`, `TauCeti.locallyFinite_Icc_nsmul`,
  `TauCeti.locallyFinite_Icc_natCast_mul` — closed intervals `[f n, g n]` with `f n → +∞` form
  a locally finite family, and in particular `[n • τ, (n + 1) • τ]` and `[n τ, (n + 1) τ]` for
  `τ > 0` in an Archimedean ordered monoid or semiring.
-/

public section

open Filter Set Topology

/-- Paste two continuous maps across a closed cut. Agreement at the cut is needed only when
that point belongs to the set on which continuity is asserted. -/
theorem ContinuousOn.piecewise_Iic {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [TopologicalSpace X] {s : Set α} {b : α} {l₁ l₂ : α → X}
    [∀ t, Decidable (t ∈ Iic b)] (h₁ : ContinuousOn l₁ (s ∩ Iic b))
    (h₂ : ContinuousOn l₂ (s ∩ Ici b)) (hjoin : b ∈ s → l₁ b = l₂ b) :
    ContinuousOn ((Iic b).piecewise l₁ l₂) s := by
  have hclosure : closure (Iic b)ᶜ ⊆ Ici b := by
    rw [compl_Iic]
    exact closure_minimal Ioi_subset_Ici_self isClosed_Ici
  apply ContinuousOn.piecewise
  · intro t ht
    have : t = b := frontier_Iic_subset b ht.2
    subst t
    exact hjoin ht.1
  · exact h₁.mono fun _ ht ↦ ⟨ht.1, isClosed_Iic.closure_subset ht.2⟩
  · exact h₂.mono fun _ ht ↦ ⟨ht.1, hclosure ht.2⟩

/-- Two maps continuous on adjacent closed intervals have a continuous pasting on the combined
interval. They need agree at the cut only when it lies in that combined interval; no ordering
of the three endpoints or separation assumption on the codomain is required. -/
theorem ContinuousOn.piecewise_Iic_Icc {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [TopologicalSpace X] {a b d : α} {l₁ l₂ : α → X}
    [∀ t, Decidable (t ∈ Iic b)] (h₁ : ContinuousOn l₁ (Icc a b))
    (h₂ : ContinuousOn l₂ (Icc b d)) (hjoin : b ∈ Icc a d → l₁ b = l₂ b) :
    ContinuousOn ((Iic b).piecewise l₁ l₂) (Icc a d) :=
  ContinuousOn.piecewise_Iic (s := Icc a d)
    (h₁.mono fun _ ht ↦ ⟨ht.1.1, ht.2⟩)
    (h₂.mono fun _ ht ↦ ⟨ht.2, ht.1.2⟩) hjoin

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

/-- The frontier of `[a, b]` avoids a set containing neither `a` nor `b`. -/
theorem disjoint_frontier_Icc {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {a b : α} {s : Set α} (ha : a ∉ s) (hb : b ∉ s) :
    Disjoint (frontier (Icc a b)) s := by
  refine disjoint_left.2 fun x hx hxs ↦ ?_
  -- The frontier lies in `[a, b]`, but not in the interior, which contains `(a, b)`.
  have hx' : x ∈ Icc a b \ Ioo a b := ⟨isClosed_Icc.frontier_subset hx, fun h ↦
    disjoint_left.1 disjoint_interior_frontier (interior_maximal Ioo_subset_Icc_self isOpen_Ioo h)
      hx⟩
  rw [Icc_sdiff_Ioo_same (hx'.1.1.trans hx'.1.2)] at hx'
  rcases hx' with rfl | rfl
  exacts [ha hxs, hb hxs]

/-- The frontier of `(a, b]` avoids a set containing neither `a` nor `b`. -/
theorem disjoint_frontier_Ioc {α : Type*} [TopologicalSpace α] [LinearOrder α]
    [OrderClosedTopology α] {a b : α} {s : Set α} (ha : a ∉ s) (hb : b ∉ s) :
    Disjoint (frontier (Ioc a b)) s := by
  refine disjoint_left.2 fun x hx hxs ↦ ?_
  -- The frontier lies in the closure, inside `[a, b]`, but not in the interior, which contains
  -- `(a, b)`.
  have hx' : x ∈ Icc a b \ Ioo a b :=
    ⟨closure_minimal Ioc_subset_Icc_self isClosed_Icc (frontier_subset_closure hx), fun h ↦
      disjoint_left.1 disjoint_interior_frontier (interior_maximal Ioo_subset_Ioc_self isOpen_Ioo h)
        hx⟩
  rw [Icc_sdiff_Ioo_same (hx'.1.1.trans hx'.1.2)] at hx'
  rcases hx' with rfl | rfl
  exacts [ha hxs, hb hxs]

/-- In `ℝ`, an interval whose endpoints lie within `ε` of `x` is contained in the ball of radius
`ε` about `x`. -/
theorem _root_.Real.Icc_subset_ball {x ε s t : ℝ} (hs : x - ε < s) (ht : t < x + ε) :
    Icc s t ⊆ Metric.ball x ε := by
  rw [Real.ball_eq_Ioo]
  exact Icc_subset_Ioo hs ht

/-- In `ℝ`, the interval between a point `x` of an order-connected set `s` and a point `y` of
`ball x ε ∩ s` lies in `ball x ε ∩ s`. -/
theorem _root_.Set.OrdConnected.uIcc_subset_ball_inter {s : Set ℝ} (hs : s.OrdConnected)
    {x y ε : ℝ} (hx : x ∈ s) (hy : y ∈ Metric.ball x ε ∩ s) :
    uIcc x y ⊆ Metric.ball x ε ∩ s := by
  have hball : (Metric.ball x ε).OrdConnected := by
    rw [Real.ball_eq_Ioo]
    exact ordConnected_Ioo
  exact (hball.inter hs).uIcc_subset ⟨Metric.mem_ball_self (Metric.pos_of_mem_ball hy.1), hx⟩ hy

/-- For points `a` and `b` of an order-connected set `I`, some closed interval contained in `I`
contains `a` and `b` and is a neighbourhood of `b` within `I`. -/
theorem _root_.Set.OrdConnected.exists_Icc_mem_nhdsWithin {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderClosedTopology α] {I : Set α} (hI : I.OrdConnected) {a b : α}
    (ha : a ∈ I) (hb : b ∈ I) :
    ∃ c d, Icc c d ⊆ I ∧ a ∈ Icc c d ∧ b ∈ Icc c d ∧ Icc c d ∈ 𝓝[I] b := by
  obtain ⟨c, hcI, hc, hbc⟩ : ∃ c ∈ I, c ≤ min a b ∧ (c < b ∨ ∀ y ∈ I, c ≤ y) := by
    by_cases h : ∃ c ∈ I, c < min a b
    · obtain ⟨c, hcI, hc⟩ := h
      exact ⟨c, hcI, hc.le, Or.inl (hc.trans_le (min_le_right _ _))⟩
    · exact ⟨_, min_rec' (· ∈ I) ha hb, le_rfl, Or.inr fun y hy ↦ not_lt.mp fun h' ↦ h ⟨y, hy, h'⟩⟩
  obtain ⟨d, hdI, hd, hbd⟩ : ∃ d ∈ I, max a b ≤ d ∧ (b < d ∨ ∀ y ∈ I, y ≤ d) := by
    by_cases h : ∃ d ∈ I, max a b < d
    · obtain ⟨d, hdI, hd⟩ := h
      exact ⟨d, hdI, hd.le, Or.inl ((le_max_right _ _).trans_lt hd)⟩
    · exact ⟨_, max_rec' (· ∈ I) ha hb, le_rfl, Or.inr fun y hy ↦ not_lt.mp fun h' ↦ h ⟨y, hy, h'⟩⟩
  have hleft : ∀ᶠ y in 𝓝 b, y ∈ I → c ≤ y := by
    rcases hbc with hbc | hbc
    · exact (eventually_gt_nhds hbc).mono fun y hy _ ↦ hy.le
    · exact Eventually.of_forall hbc
  have hright : ∀ᶠ y in 𝓝 b, y ∈ I → y ≤ d := by
    rcases hbd with hbd | hbd
    · exact (eventually_lt_nhds hbd).mono fun y hy _ ↦ hy.le
    · exact Eventually.of_forall hbd
  exact ⟨c, d, hI.out hcI hdI, ⟨hc.trans (min_le_left _ _), (le_max_left _ _).trans hd⟩,
    ⟨hc.trans (min_le_right _ _), (le_max_right _ _).trans hd⟩,
    mem_nhdsWithin_iff_eventually.mpr
      ((hleft.and hright).mono fun y hy hyI ↦ ⟨hy.1 hyI, hy.2 hyI⟩)⟩

/-- A function into a topological space that is continuous on `[a, b]` for every `b ≥ a` is
continuous on `[a, ∞)`. -/
theorem continuousOn_Ici_of_forall_Icc {α X : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] [NoMaxOrder α] [TopologicalSpace X] {f : α → X} {a : α}
    (h : ∀ b ≥ a, ContinuousOn f (Icc a b)) : ContinuousOn f (Ici a) :=
  continuousOn_of_locally_continuousOn fun t ht ↦
    let ⟨b, htb⟩ := exists_gt t
    ⟨Iio b, isOpen_Iio, htb,
      (h b (mem_Ici.1 ht |>.trans htb.le)).mono fun _ hr ↦ ⟨hr.1, hr.2.le⟩⟩

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

/-- Every neighbourhood of `t₀ ∈ [u, v]` (with `u < v`) within `[u, v]` contains a nondegenerate
closed subinterval `[p, q] ⊆ [u, v]` around `t₀` that is itself a neighbourhood of `t₀` within
`[u, v]`. -/
theorem exists_Icc_mem_subset_of_mem_nhdsWithin_Icc {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] {u v t₀ : α} {s : Set α}
    (huv : u < v) (ht₀ : t₀ ∈ Icc u v) (hs : s ∈ 𝓝[Icc u v] t₀) :
    ∃ p q, u ≤ p ∧ p < q ∧ q ≤ v ∧ t₀ ∈ Icc p q ∧
      Icc p q ∈ 𝓝[Icc u v] t₀ ∧ Icc p q ⊆ s := by
  rcases ht₀.1.eq_or_lt with rfl | hut
  · rw [nhdsWithin_Icc_eq_nhdsGE huv] at hs ⊢
    obtain ⟨r, hur, hrs⟩ := (nhdsGE_basis_of_exists_gt ⟨v, huv⟩).mem_iff.1
      (inter_mem hs (Ico_mem_nhdsGE huv))
    obtain ⟨q, huq, hqr⟩ := exists_between hur
    exact ⟨u, q, le_rfl, huq, (hrs ⟨huq.le, hqr⟩).2.2.le, ⟨le_rfl, huq.le⟩, Icc_mem_nhdsGE huq,
      fun x hx ↦ (hrs ⟨hx.1, hx.2.trans_lt hqr⟩).1⟩
  · rcases ht₀.2.eq_or_lt with rfl | htv
    · rw [nhdsWithin_Icc_eq_nhdsLE huv] at hs ⊢
      obtain ⟨l, hlt, hls⟩ := (nhdsLE_basis_of_exists_lt ⟨u, huv⟩).mem_iff.1
        (inter_mem hs (Ioc_mem_nhdsLE huv))
      obtain ⟨p, hlp, hpt⟩ := exists_between hlt
      exact ⟨p, t₀, (hls ⟨hlp, hpt.le⟩).2.1.le, hpt, le_rfl, ⟨hpt.le, le_rfl⟩, Icc_mem_nhdsLE hpt,
        fun x hx ↦ (hls ⟨hlp.trans_le hx.1, hx.2⟩).1⟩
    · have hmem : s ∩ Ioo u v ∈ 𝓝 t₀ :=
        inter_mem (nhdsWithin_eq_nhds.2 (Icc_mem_nhds hut htv) ▸ hs) (Ioo_mem_nhds hut htv)
      obtain ⟨l, r, ⟨hlt, htr⟩, hlr⟩ := (mem_nhds_iff_exists_Ioo_subset' ⟨u, hut⟩ ⟨v, htv⟩).1 hmem
      obtain ⟨p, hlp, hpt⟩ := exists_between hlt
      obtain ⟨q, htq, hqr⟩ := exists_between htr
      have hsub : Icc p q ⊆ s ∩ Ioo u v := fun x hx ↦ hlr ⟨hlp.trans_le hx.1, hx.2.trans_lt hqr⟩
      exact ⟨p, q, (hsub ⟨le_rfl, hpt.le.trans htq.le⟩).2.1.le, hpt.trans htq,
        (hsub ⟨hpt.le.trans htq.le, le_rfl⟩).2.2.le, ⟨hpt.le, htq.le⟩,
        nhdsWithin_le_nhds (Icc_mem_nhds hpt htq), hsub.trans inter_subset_left⟩

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

/-- An open set `s` containing the unordered closed interval `[[a, b]]` contains an open interval
`Ioo c d` around `[[a, b]]`. -/
theorem _root_.IsOpen.exists_Ioo_subset_of_uIcc_subset {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [NoMinOrder α] [NoMaxOrder α] {s : Set α}
    (hs : IsOpen s) {a b : α} (h : uIcc a b ⊆ s) :
    ∃ c d, uIcc a b ⊆ Ioo c d ∧ Ioo c d ⊆ s := by
  obtain ⟨c, hc, hcs⟩ := exists_Ioc_subset_of_mem_nhds
    (hs.mem_nhds (h ⟨le_rfl, inf_le_sup⟩)) (exists_lt (a ⊓ b))
  obtain ⟨d, hd, hds⟩ := exists_Ico_subset_of_mem_nhds
    (hs.mem_nhds (h ⟨inf_le_sup, le_rfl⟩)) (exists_gt (a ⊔ b))
  refine ⟨c, d, fun u hu ↦ ⟨hc.trans_le hu.1, hu.2.trans_lt hd⟩, fun u hu ↦ ?_⟩
  rcases le_or_gt u (a ⊓ b) with hu₁ | hu₁
  · exact hcs ⟨hu.1, hu₁⟩
  rcases le_or_gt (a ⊔ b) u with hu₂ | hu₂
  · exact hds ⟨hu₂, hu.2⟩
  exact h ⟨hu₁.le, hu₂.le⟩

/-- A nonempty closed order-connected set which is not bounded on both sides is a right
half-line, a left half-line, or the whole space. -/
theorem _root_.Set.OrdConnected.eq_Ici_or_eq_Iic_or_eq_univ
    {α : Type*} [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {s : Set α} (hs : s.OrdConnected) (hne : s.Nonempty) (hclosed : IsClosed s)
    (hunbounded : ¬(BddBelow s ∧ BddAbove s)) :
    (∃ a, s = Ici a) ∨ (∃ b, s = Iic b) ∨ s = univ := by
  by_cases hbelow : BddBelow s
  · have habove : ¬BddAbove s := fun h ↦ hunbounded ⟨hbelow, h⟩
    refine Or.inl ⟨sInf s, ?_⟩
    rw [← upperClosure_eq_Ici_csInf hne hbelow hclosed]
    apply Subset.antisymm subset_upperClosure
    rintro x ⟨y, hy, hyx⟩
    obtain ⟨z, hz, hxz⟩ := not_bddAbove_iff.1 habove x
    exact hs.out hy hz ⟨hyx, hxz.le⟩
  · by_cases habove : BddAbove s
    · refine Or.inr <| Or.inl ⟨sSup s, ?_⟩
      rw [← lowerClosure_eq_Iic_csSup hne habove hclosed]
      apply Subset.antisymm subset_lowerClosure
      rintro x ⟨y, hy, hxy⟩
      obtain ⟨z, hz, hzx⟩ := not_bddBelow_iff.1 hbelow x
      exact hs.out hz hy ⟨hzx.le, hxy⟩
    · refine Or.inr <| Or.inr <| eq_univ_of_forall fun x ↦ ?_
      obtain ⟨y, hy, hyx⟩ := not_bddBelow_iff.1 hbelow x
      obtain ⟨z, hz, hxz⟩ := not_bddAbove_iff.1 habove x
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
  refine Subset.antisymm ?_ <| isPreconnected_Ici.intermediate_value_Ico self_mem_Ici
    (le_principal_iff.mpr (Ici_mem_atTop p)) hdcont hdl
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hxy⟩ := exists_gt x
  have hy : y ∈ Ici p := hx.trans hxy.le
  have hyD : d y ≤ D := ge_of_tendsto hdl <|
    eventually_atTop.2 ⟨y, fun z hz ↦ hdmono.monotoneOn hy (hy.trans hz) hz⟩
  exact ⟨hdmono.monotoneOn self_mem_Ici hx hx, (hdmono hx hy hxy).trans_le hyD⟩

/-- A continuous strictly increasing function `f` on `[a, b]` has a continuous inverse `τ` on its
range `[c, d]`, extended to the whole codomain by being constant outside `[c, d]` (that is, `τ` is
the inverse composed with the clamp `projIcc c d`, whose value is `max c (min d r)`). -/
theorem exists_continuous_projIcc_inverse {α β : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [LinearOrder β] [TopologicalSpace β]
    [OrderTopology β] {f : α → β} {a b : α} {c d : β} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hm : StrictMonoOn f (Icc a b)) (hc : f a = c) (hd : f b = d) :
    ∃ τ : β → α, Continuous τ ∧ (∀ r, τ r ∈ Icc a b) ∧
      (∀ r, f (τ r) = max c (min d r)) ∧ ∀ s ∈ Icc a b, τ (f s) = s := by
  have ha : a ∈ Icc a b := left_mem_Icc.2 hab
  have hb : b ∈ Icc a b := right_mem_Icc.2 hab
  have hcd : c ≤ d := hc ▸ hd ▸ hm.monotoneOn ha hb hab
  subst hc hd
  let g : Icc a b → Icc (f a) (f b) := fun s ↦
    ⟨f s, hm.monotoneOn ha s.property s.property.1, hm.monotoneOn s.property hb s.property.2⟩
  have hg_cont : Continuous g :=
    Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.1 hf) _
  have hg_bij : Function.Bijective g := by
    refine ⟨fun s s' h ↦ Subtype.ext (hm.injOn s.property s'.property (congrArg Subtype.val h)),
        fun r ↦ ?_⟩
    obtain ⟨s, hs, hsr⟩ := intermediate_value_Icc hab hf r.property
    exact ⟨⟨s, hs⟩, Subtype.ext hsr⟩
  -- `homeoOfEquivCompactToT2` only adds continuity data to the equivalence `Equiv.ofBijective g`,
  -- and Mathlib states no lemma for its coercion.
  let F : Icc a b ≃ₜ Icc (f a) (f b) :=
    hg_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hg_bij)
  have hF (s : Icc a b) : (F s : β) = f s := rfl
  refine ⟨fun r ↦ F.symm (projIcc (f a) (f b) hcd r),
    continuous_subtypeVal.comp (F.symm.continuous.comp continuous_projIcc), fun r ↦
        (F.symm _).property,
    fun r ↦ ?_, fun s hs ↦ ?_⟩
  · rw [← hF, Homeomorph.apply_symm_apply, coe_projIcc, min_comm]
  · have : projIcc (f a) (f b) hcd (f s) = F ⟨s, hs⟩ :=
      Subtype.ext (by rw [hF, projIcc_of_mem]; exact (F ⟨s, hs⟩).property)
    simp only [this, Homeomorph.symm_apply_apply]

/-- **First exit from an open set.** A path continuous on `[a, b]` that starts in an open set `V`
and leaves it has a first exit time `T > a`: the path stays in `V` on `[a, T)`, and `γ T` lies in
the closure of `V` but not in `V`. -/
theorem _root_.IsOpen.exists_first_exit {α X : Type*} [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [TopologicalSpace X] {V : Set X}
    (hV : IsOpen V) {γ : α → X} {a b : α} (hγ : ContinuousOn γ (Icc a b)) (ha : γ a ∈ V)
    (hex : ∃ t ∈ Icc a b, γ t ∉ V) :
    ∃ T ∈ Icc a b, a < T ∧ γ T ∉ V ∧ γ T ∈ closure V ∧ ∀ t ∈ Ico a T, γ t ∈ V := by
  obtain ⟨t₀, ht₀, ht₀V⟩ := hex
  have hA_closed : IsClosed (Icc a b ∩ γ ⁻¹' Vᶜ) :=
    hγ.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl
  obtain ⟨T, hTA, hT⟩ := (isCompact_Icc.of_isClosed_subset hA_closed fun t ht ↦ ht.1).exists_isLeast
    ⟨t₀, ht₀, ht₀V⟩
  have hbefore : ∀ t ∈ Ico a T, γ t ∈ V := by
    intro t ht
    by_contra hnot
    exact (not_le.mpr ht.2) (hT ⟨⟨ht.1, ht.2.le.trans hTA.1.2⟩, hnot⟩)
  have hTpos : a < T := lt_of_le_of_ne hTA.1.1 fun h ↦ hTA.2 (h ▸ ha)
  have := right_nhdsWithin_Ioo_neBot hTpos
  have htend : Tendsto γ (𝓝[Ioo a T] T) (𝓝 (γ T)) :=
    ((hγ T hTA.1).mono (Ioo_subset_Icc_self.trans (Icc_subset_Icc le_rfl hTA.1.2))).tendsto
  exact ⟨T, hTA.1, hTpos, hTA.2, mem_closure_of_tendsto htend
    (eventually_nhdsWithin_of_forall fun t ht ↦ hbefore t ⟨ht.1.le, ht.2⟩), hbefore⟩

/-- The curve `δ ↦ b - δ` tends to `b` within `[a, b]` as `δ → 0⁺`. -/
theorem tendsto_sub_nhdsGT_nhdsWithin_Icc {G : Type*} [AddCommGroup G] [LinearOrder G]
    [IsOrderedAddMonoid G] [TopologicalSpace G] [OrderTopology G] {a b : G} (hab : a < b) :
    Tendsto (fun δ : G ↦ b - δ) (𝓝[>] 0) (𝓝[Icc a b] b) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact ((continuous_const.sub continuous_id).tendsto' 0 b (sub_zero b)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hab)] with δ hδ
    exact ⟨le_sub_comm.1 hδ.2.le, sub_le_self _ hδ.1.le⟩

/-- Negation `v ↦ -v` maps the symmetric open interval `(-a, a)` continuously to itself. -/
theorem continuous_neg_Ioo {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [TopologicalSpace G] [ContinuousNeg G] (a : G) :
    Continuous fun v : Ioo (-a) a ↦
      (⟨-v, neg_lt_neg v.property.2, neg_lt.1 v.property.1⟩ : Ioo (-a) a) :=
  continuous_subtypeVal.neg.subtype_mk _

/-- A continuous function on `[a, b]` that is injective on `[a, b)` takes different values at the
two endpoints. -/
theorem _root_.ContinuousOn.apply_ne_apply_of_injOn_Ico {α δ : Type*}
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
    [LinearOrder δ] [TopologicalSpace δ] [OrderClosedTopology δ] {f : α → δ}
    {a b : α} (hf : ContinuousOn f (Icc a b)) (hab : a < b) (hinj : InjOn f (Ico a b)) :
    f a ≠ f b := by
  have ha : a ∈ Ico a b := ⟨le_rfl, hab⟩
  intro hab'
  obtain ⟨m, hm⟩ := exists_between hab
  -- A value strictly between `f a` and `f m` would be attained on both `[a, m]` and `[m, b]`.
  obtain ⟨v, hv, hva, hvm⟩ : ∃ v ∈ uIcc (f a) (f m), v ≠ f a ∧ v ≠ f m := by
    obtain ⟨m', hm'⟩ := exists_between hm.1
    have ham' : a ∈ Icc a m := ⟨le_rfl, hm.1.le⟩
    have hm'm : m' ∈ Icc a m := ⟨hm'.1.le, hm'.2.le⟩
    have hmm : m ∈ Icc a m := ⟨hm.1.le, le_rfl⟩
    rcases (hf.mono (Icc_subset_Icc le_rfl hm.2.le)).strictMonoOn_of_injOn_Icc' hm.1.le
      (hinj.mono (Icc_subset_Ico_right hm.2)) with h | h
    · exact ⟨f m', mem_uIcc.2 (Or.inl ⟨(h ham' hm'm hm'.1).le, (h hm'm hmm hm'.2).le⟩),
        (h ham' hm'm hm'.1).ne', (h hm'm hmm hm'.2).ne⟩
    · exact ⟨f m', mem_uIcc.2 (Or.inr ⟨(h hm'm hmm hm'.2).le, (h ham' hm'm hm'.1).le⟩),
        (h ham' hm'm hm'.1).ne, (h hm'm hmm hm'.2).ne'⟩
  obtain ⟨s, hs, hsv⟩ := intermediate_value_uIcc
    (hf.mono (by rw [uIcc_of_le hm.1.le]; exact Icc_subset_Icc le_rfl hm.2.le)) hv
  obtain ⟨t, ht, htv⟩ := intermediate_value_uIcc
    (hf.mono (by rw [uIcc_of_le hm.2.le]; exact Icc_subset_Icc hm.1.le le_rfl))
    (by simpa only [← hab', uIcc_comm] using hv)
  rw [uIcc_of_le hm.1.le] at hs
  rw [uIcc_of_le hm.2.le] at ht
  have htb : t ≠ b := by rintro rfl; exact hva (htv.symm.trans hab'.symm)
  have hst : s = t := hinj ⟨hs.1, hs.2.trans_lt hm.2⟩ ⟨hm.1.le.trans ht.1, ht.2.lt_of_ne htb⟩
    (hsv.trans htv.symm)
  have hsm : s = m := le_antisymm hs.2 (hst ▸ ht.1)
  exact hvm (hsv.symm.trans (congrArg f hsm))

/-- A function continuous on `[a, b]` and strictly monotone on `(a, b)` is strictly monotone on
`[a, b]`. -/
theorem _root_.ContinuousOn.strictMonoOn_Icc_of_strictMonoOn_Ioo {α β : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [LinearOrder β]
    [TopologicalSpace β] [OrderClosedTopology β] {f : α → β} {a b : α}
    (hf : ContinuousOn f (Icc a b)) (h : StrictMonoOn f (Ioo a b)) :
    StrictMonoOn f (Icc a b) := by
  rcases le_or_gt b a with hba | hab
  · exact (subsingleton_Icc_of_ge hba).strictMonoOn f
  -- By continuity, `f` stays monotone when the two endpoints are added.
  have hmono : MonotoneOn f (Icc a b) := by
    have hIco : MonotoneOn f (Ico a b) := by
      rw [← insert_left_Ioo hab]
      exact h.monotoneOn.insert_of_continuousWithinAt (left_nhdsWithin_Ioo_neBot hab)
        ((hf a (left_mem_Icc.2 hab.le)).mono Ioo_subset_Icc_self)
    rw [← insert_right_Ico hab.le]
    exact hIco.insert_of_continuousWithinAt (right_nhdsWithin_Ico_neBot hab)
      ((hf b (right_mem_Icc.2 hab.le)).mono Ico_subset_Icc_self)
  -- Between `x < y` lie two points of `(a, b)`, where `f` increases strictly.
  intro x hx y hy hxy
  obtain ⟨s, hxs, hsy⟩ := exists_between hxy
  obtain ⟨t, hst, hty⟩ := exists_between hsy
  have hs : s ∈ Ioo a b := ⟨hx.1.trans_lt hxs, (hst.trans hty).trans_le hy.2⟩
  have ht : t ∈ Ioo a b := ⟨hs.1.trans hst, hty.trans_le hy.2⟩
  exact (hmono hx (Ioo_subset_Icc_self hs) hxs.le).trans_lt
    ((h hs ht hst).trans_le (hmono (Ioo_subset_Icc_self ht) hy hty.le))

/-- A function continuous on `[a, b]` and strictly antitone on `(a, b)` is strictly antitone on
`[a, b]`. -/
theorem _root_.ContinuousOn.strictAntiOn_Icc_of_strictAntiOn_Ioo {α β : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [LinearOrder β]
    [TopologicalSpace β] [OrderClosedTopology β] {f : α → β} {a b : α}
    (hf : ContinuousOn f (Icc a b)) (h : StrictAntiOn f (Ioo a b)) :
    StrictAntiOn f (Icc a b) :=
  ContinuousOn.strictMonoOn_Icc_of_strictMonoOn_Ioo (β := βᵒᵈ) hf h

/-- A continuous function on `Ioi p` that is above `v`, tends to `v` at `+∞` and to `+∞` at `p⁺`
has image `Ioi v`. -/
theorem _root_.ContinuousOn.image_Ioi_eq_Ioi_of_tendsto {α β : Type*}
    [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMaxOrder α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {d : α → β} {p : α} {v : β}
    (hcont : ContinuousOn d (Ioi p)) (hpos : ∀ x ∈ Ioi p, v < d x)
    (htop : Tendsto d atTop (𝓝 v)) (hp : Tendsto d (𝓝[>] p) atTop) : d '' Ioi p = Ioi v :=
  Subset.antisymm (by rintro _ ⟨x, hx, rfl⟩; exact hpos x hx)
    (isPreconnected_Ioi.intermediate_value_Ioi (le_principal_iff.mpr (Ioi_mem_atTop p))
      (le_principal_iff.mpr self_mem_nhdsWithin) hcont htop hp)

/-- A continuous function on `Iio p` that is above `v`, tends to `v` at `-∞` and to `+∞` at `p⁻`
has image `Ioi v`. -/
theorem _root_.ContinuousOn.image_Iio_eq_Ioi_of_tendsto {α β : Type*}
    [ConditionallyCompleteLinearOrder α]
    [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] [NoMinOrder α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β] {d : α → β} {p : α} {v : β}
    (hcont : ContinuousOn d (Iio p)) (hpos : ∀ x ∈ Iio p, v < d x)
    (hbot : Tendsto d atBot (𝓝 v)) (hp : Tendsto d (𝓝[<] p) atTop) : d '' Iio p = Ioi v :=
  ContinuousOn.image_Ioi_eq_Ioi_of_tendsto (α := αᵒᵈ) hcont hpos hbot hp

/-- In a linear order with the order topology and no maximum element, closed intervals
`[f n, g n]` form a locally finite family whenever `f n → +∞`. -/
theorem locallyFinite_Icc_of_tendsto {K : Type*} [LinearOrder K] [TopologicalSpace K]
    [OrderTopology K] [NoMaxOrder K] {f g : ℕ → K} (hf : Tendsto f atTop atTop) :
    LocallyFinite fun n : ℕ ↦ Icc (f n) (g n) := by
  intro t
  obtain ⟨u, hu⟩ := exists_gt t
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hf.eventually_gt_atTop u)
  refine ⟨Iio u, Iio_mem_nhds hu, (finite_lt_nat N).subset fun n ⟨x, hx, hxu⟩ ↦ ?_⟩
  rw [Set.mem_ofPred_eq]
  by_contra! hNn
  exact not_le_of_gt (hxu.trans_le (hN n hNn).le) hx.1

/-- For `τ > 0` in an Archimedean linearly ordered cancellative additive monoid with the order
topology, the closed grid intervals `[n • τ, (n + 1) • τ]` (`n : ℕ`) form a locally finite
family. -/
theorem locallyFinite_Icc_nsmul {K : Type*} [AddCommMonoid K] [LinearOrder K]
    [IsOrderedCancelAddMonoid K] [TopologicalSpace K] [OrderTopology K] [Archimedean K]
    {τ : K} (hτ : 0 < τ) :
    LocallyFinite fun n : ℕ ↦ Icc (n • τ) ((n + 1) • τ) := by
  have : NoMaxOrder K := ⟨fun x ↦ ⟨x + τ, lt_add_of_pos_right x hτ⟩⟩
  refine locallyFinite_Icc_of_tendsto (tendsto_atTop_atTop.2 fun b ↦ ?_)
  obtain ⟨n, hn⟩ := Archimedean.arch b hτ
  exact ⟨n, fun m hm ↦ hn.trans (nsmul_le_nsmul_left hτ.le hm)⟩

/-- For `τ > 0` in an Archimedean ordered semiring with the order topology, the closed grid
intervals `[n τ, (n + 1) τ]` (`n : ℕ`) form a locally finite family. -/
theorem locallyFinite_Icc_natCast_mul {K : Type*} [Semiring K] [LinearOrder K]
    [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] [Archimedean K]
    {τ : K} (hτ : 0 < τ) :
    LocallyFinite fun n : ℕ ↦ Icc ((n : K) * τ) (((n : K) + 1) * τ) := by
  simpa only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one] using locallyFinite_Icc_nsmul hτ

end TauCeti
