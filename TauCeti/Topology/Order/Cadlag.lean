/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag
import TauCeti.Topology.Order.LeftRightLim

/-!
# Path properties of càdlàg functions

A step function taking its right-hand value at its jump time is càdlàg (`TauCeti.isCadlag_ite_le`),
and stopping any càdlàg path at a deterministic horizon preserves the càdlàg property
(`IsCadlag.comp_min_const`). Conversely, a function into a discrete space is right-continuous
exactly when it is constant on a right neighbourhood of each point
(`TauCeti.isRightContinuous_iff_eventually_eq`, `IsRightContinuous.eventually_eq`), as for counting
paths.

For a càdlàg path into a regular space, its strict left limit converges from the right to `f x`
(`IsCadlag.tendsto_nhdsGT_leftLim`). Consequently, the first time at which a path or its left
limit enters a closed set is attained whenever the path is right-continuous at that infimum and the
entry set is nonempty and bounded below
(`IsClosed.csInf_mem_or_leftLim_mem_of_continuousWithinAt`). On a compact lower ray `(-∞, T]`, no
value or left limit of a càdlàg function into a linear order with closed upper and lower rays
reaches `ε` if and only if its values on `(-∞, T]` admit a uniform upper bound strictly below `ε`
(`IsCadlag.forall_lt_and_leftLim_lt_iff_exists_le`), yielding the conditionally complete supremum
criterion `IsCadlag.exists_le_or_le_leftLim_iff_le_sSup` and its complete-order form
`IsCadlag.exists_le_or_le_leftLim_iff_le_biSup`.
-/

public section

open Filter Function Set TopologicalSpace
open scoped Topology

namespace TauCeti

/-- A single step, with the right-hand value at the jump, is càdlàg. -/
theorem isCadlag_ite_le {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderClosedTopology ι] [TopologicalSpace E] (a : ι) (x y : E) :
    IsCadlag (fun t => if a ≤ t then x else y) := by
  constructor
  · intro t
    by_cases hat : a ≤ t
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [hat.trans (le_of_lt hs), hat]
    · apply tendsto_const_nhds.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hat))] with s hs
      simp [not_le.mpr hs, hat]
  · intro t
    by_cases hat : a < t
    · refine ⟨x, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat)] with s hs
      simp [hs.le]
    · refine ⟨y, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [not_le.mpr (hs.trans_le (le_of_not_gt hat))]

/-- A function into a discrete space is right-continuous exactly when, at each point, it
eventually takes its value there on the right. -/
theorem isRightContinuous_iff_eventually_eq {X Y : Type*} [TopologicalSpace X] [Preorder X]
    [TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y} :
    IsRightContinuous f ↔ ∀ a, ∀ᶠ x in 𝓝[>] a, f x = f a := by
  simp only [IsRightContinuous, ContinuousWithinAt, nhds_discrete, tendsto_pure]

end TauCeti

/-- A right-continuous function into a discrete space is constant on a right neighbourhood of
each point. -/
theorem IsRightContinuous.eventually_eq {X Y : Type*} [TopologicalSpace X] [Preorder X]
    [TopologicalSpace Y] [DiscreteTopology Y] {f : X → Y} (hf : IsRightContinuous f) (a : X) :
    ∀ᶠ x in 𝓝[>] a, f x = f a :=
  TauCeti.isRightContinuous_iff_eventually_eq.1 hf a

namespace IsCadlag

/-- Along times approaching `x` strictly from the right, the strict left limit of a càdlàg
function into a regular space converges to `f x`. -/
theorem tendsto_nhdsGT_leftLim {X Y : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [TopologicalSpace Y] [RegularSpace Y] {f : X → Y} (hf : IsCadlag f)
    (x : X) : Tendsto f.leftLim (𝓝[>] x) (𝓝 (f x)) :=
  (hf.isRightContinuous x).tendsto.leftLim_nhdsGT

/-- Stopping a càdlàg path at a deterministic horizon preserves the càdlàg property. -/
theorem comp_min_const {X Y : Type*} [LinearOrder X] [TopologicalSpace X] [OrderClosedTopology X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsCadlag f) (u : X) :
    IsCadlag (fun t => f (min t u)) where
  isRightContinuous t := by
    rcases lt_or_ge t u with htu | hut
    · refine (hf.isRightContinuous t).congr_of_eventuallyEq ?_ (by simp [htu.le])
      filter_upwards [Ioo_mem_nhdsGT htu] with s hs
      simp [hs.2.le]
    · refine (continuousWithinAt_const (b := f u)).congr (fun s hs => ?_)
        (by simp [min_eq_right hut])
      simp [min_eq_right (hut.trans (le_of_lt hs))]
  tendsto_nhdsLT t := by
    rcases le_or_gt t u with htu | hut
    · obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT t
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [(le_of_lt hs).trans htu]
    · refine ⟨f u, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [Ioo_mem_nhdsLT hut] with s hs
      simp [min_eq_right hs.1.le]

/-- On a compact lower ray `(-∞, T]`, no value or strict left limit of a càdlàg function into a
linear order with closed upper and lower rays reaches `ε` if and only if its values on `(-∞, T]`
admit a uniform upper bound strictly below `ε`. -/
theorem forall_lt_and_leftLim_lt_iff_exists_le {X α : Type*}
    [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [LinearOrder α] [TopologicalSpace α] [ClosedIciTopology α] [ClosedIicTopology α]
    {g : X → α} (hg : IsCadlag g) {T : X} (hT : IsCompact (Iic T)) (ε : α) :
    (∀ t ≤ T, g t < ε ∧ g.leftLim t < ε) ↔ ∃ c < ε, ∀ t ≤ T, g t ≤ c := by
  constructor
  · intro hlt
    have hc_ex (t : Iic T) :
        ∃ c < ε, Iic c ∈ 𝓝 (g t.val) ∧ Iic c ∈ 𝓝 (g.leftLim t.val) := by
      have hm_lt : max (g t.val) (g.leftLim t.val) < ε :=
        max_lt (hlt t.val t.property).1 (hlt t.val t.property).2
      by_cases hbet : ∃ c, max (g t.val) (g.leftLim t.val) < c ∧ c < ε
      · obtain ⟨c, hc_gt, hc_lt⟩ := hbet
        exact ⟨c, hc_lt,
          mem_of_superset (Iio_mem_nhds ((le_max_left _ _).trans_lt hc_gt)) Iio_subset_Iic_self,
          mem_of_superset (Iio_mem_nhds ((le_max_right _ _).trans_lt hc_gt)) Iio_subset_Iic_self⟩
      · have hsub : Iio ε ⊆ Iic (max (g t.val) (g.leftLim t.val)) := fun y hy =>
          not_lt.mp fun hy_gt => hbet ⟨y, hy_gt, hy⟩
        exact ⟨max (g t.val) (g.leftLim t.val), hm_lt,
          mem_of_superset (Iio_mem_nhds (hlt t.val t.property).1) hsub,
          mem_of_superset (Iio_mem_nhds (hlt t.val t.property).2) hsub⟩
    choose c hc_lt hc_val hc_lim using hc_ex
    have hnhds (t : Iic T) : {x | g x ≤ c t} ∈ 𝓝 t.val := by
      rw [← nhdsLT_sup_nhdsGE t.val, mem_sup]
      refine ⟨(hg.tendsto_nhdsLT_leftLim t.val).eventually (hc_lim t),
        (isRightContinuous_iff_continuousWithinAt_Ici.mp hg.isRightContinuous t.val).eventually
          (hc_val t)⟩
    choose U hU_sub hU_open htU using fun t => mem_nhds_iff.mp (hnhds t)
    obtain ⟨F, hF⟩ := hT.elim_finite_subcover U hU_open fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, htU ⟨x, hx⟩⟩
    let i₀ : Iic T := ⟨T, le_rfl⟩
    let F' : Finset (Iic T) := insert i₀ F
    have hF'_ne : F'.Nonempty := Finset.insert_nonempty i₀ F
    refine ⟨F'.sup' hF'_ne c, (Finset.sup'_lt_iff hF'_ne).mpr fun i _ => hc_lt i,
      fun x hx => ?_⟩
    obtain ⟨i, hiF, hxi⟩ := mem_iUnion₂.mp (hF hx)
    exact (hU_sub i hxi).trans (Finset.le_sup' c (Finset.mem_insert_of_mem hiF))
  · rintro ⟨c, hc_lt, hg_le⟩ t ht
    exact ⟨(hg_le t ht).trans_lt hc_lt,
      (TauCeti.leftLim_le_of_forall_le fun s hs => hg_le s (hs.trans ht)).trans_lt hc_lt⟩

/-- On a compact lower ray `(-∞, T]`, a càdlàg function into a conditionally complete linear order
with closed upper and lower rays whose values on `(-∞, T]` are bounded above reaches `ε` in value
or left limit at some time `t ≤ T` if and only if the supremum of its values up to `T` is at
least `ε`. -/
theorem exists_le_or_le_leftLim_iff_le_sSup {X α : Type*}
    [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [ConditionallyCompleteLinearOrder α] [TopologicalSpace α]
    [ClosedIciTopology α] [ClosedIicTopology α]
    {g : X → α} (hg : IsCadlag g) {T : X} (hT : IsCompact (Iic T))
    (hbdd : BddAbove (g '' Iic T)) (ε : α) :
    (∃ t ≤ T, ε ≤ g t ∨ ε ≤ g.leftLim t) ↔ ε ≤ sSup (g '' Iic T) := by
  rw [← not_iff_not]
  push Not
  rw [hg.forall_lt_and_leftLim_lt_iff_exists_le hT]
  refine ⟨fun ⟨c, hc, hle⟩ => (csSup_le (nonempty_Iic.image g) ?_).trans_lt hc,
    fun h => ⟨sSup (g '' Iic T), h, fun t ht => le_csSup hbdd ⟨t, ht, rfl⟩⟩⟩
  rintro _ ⟨t, ht, rfl⟩
  exact hle t ht

/-- On a compact lower ray `(-∞, T]`, a càdlàg function into a complete linear order with closed
upper and lower rays reaches `ε` in value or left limit at some time `t ≤ T` if and only if the
supremum of its values up to `T` is at least `ε`. -/
theorem exists_le_or_le_leftLim_iff_le_biSup {X α : Type*}
    [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [CompleteLinearOrder α] [TopologicalSpace α] [ClosedIciTopology α] [ClosedIicTopology α]
    {g : X → α} (hg : IsCadlag g) {T : X} (hT : IsCompact (Iic T)) (ε : α) :
    (∃ t ≤ T, ε ≤ g t ∨ ε ≤ g.leftLim t) ↔ ε ≤ ⨆ t ≤ T, g t := by
  simpa only [sSup_image, mem_Iic] using
    hg.exists_le_or_le_leftLim_iff_le_sSup hT (OrderTop.bddAbove _) ε

end IsCadlag

/-- For a path into a regular space that is right-continuous at the infimum `s` of times at which
either the path or its strict left limit lies in a closed set `C`, `s` itself belongs to that entry
set whenever it is nonempty and bounded below. -/
theorem IsClosed.csInf_mem_or_leftLim_mem_of_continuousWithinAt {X Y : Type*}
    [ConditionallyCompleteLinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [TopologicalSpace Y] [RegularSpace Y] {C : Set Y} (hC : IsClosed C) {f : X → Y}
    (hf : ContinuousWithinAt f (Ioi (sInf {t | f t ∈ C ∨ f.leftLim t ∈ C}))
      (sInf {t | f t ∈ C ∨ f.leftLim t ∈ C}))
    (hne : {t | f t ∈ C ∨ f.leftLim t ∈ C}.Nonempty)
    (hbdd : BddBelow {t | f t ∈ C ∨ f.leftLim t ∈ C}) :
    f (sInf {t | f t ∈ C ∨ f.leftLim t ∈ C}) ∈ C ∨
      f.leftLim (sInf {t | f t ∈ C ∨ f.leftLim t ∈ C}) ∈ C := by
  let A := {t | f t ∈ C ∨ f.leftLim t ∈ C}
  let s := sInf A
  by_contra hs
  have hfs : f s ∈ Cᶜ := fun h => hs (Or.inl h)
  have hlt_all {x : X} (hx : x ∈ A) : s < x :=
    lt_of_le_of_ne (csInf_le hbdd hx) fun heq => hs (by rwa [← heq] at hx)
  have ⟨x₀, hx₀⟩ := hne
  have hsx₀ : s < x₀ := hlt_all hx₀
  rcases eq_or_neBot (𝓝[>] s) with hbot | _
  · have hemp : (∅ : Set X) ∈ 𝓝[>] s := by simp [hbot]
    obtain ⟨u, hsu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hsx₀).mp hemp
    have hub : ∀ x ∈ A, u ≤ x := fun x hx =>
      le_of_not_gt fun hxu => hu ⟨hlt_all hx, hxu⟩
    exact not_le_of_gt hsu (le_csInf hne hub)
  · have hmem : {r | r ∉ A} ∈ 𝓝[>] s := by
      have h1 := hf.eventually (hC.isOpen_compl.mem_nhds hfs)
      have h2 := hf.tendsto.leftLim_nhdsGT.eventually (hC.isOpen_compl.mem_nhds hfs)
      filter_upwards [h1, h2] with r hr1 hr2 hrA
      exact hrA.elim hr1 hr2
    obtain ⟨u, hsu, hu⟩ := (mem_nhdsGT_iff_exists_Ioo_subset' hsx₀).mp hmem
    have hub : ∀ x ∈ A, u ≤ x := fun x hx =>
      le_of_not_gt fun hxu => hu ⟨hlt_all hx, hxu⟩ hx
    exact not_le_of_gt hsu (le_csInf hne hub)
