/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.Order.WithTop
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.MonotoneConvergence
import TauCeti.Topology.Order.LeftRight

/-!
# Path properties and oscillation exits of càdlàg functions

A step function taking its right-hand value at its jump time is càdlàg (`TauCeti.isCadlag_ite_le`),
and stopping any càdlàg path at a deterministic horizon preserves the càdlàg property
(`IsCadlag.comp_min_const`).

If a function converges from the right at `x` in a regular space, its strict left limit
`Function.leftLim` also converges from the right to the same limit
(`Filter.Tendsto.leftLim_nhdsGT`), and in particular for a càdlàg path it converges to `f x`
(`IsCadlag.tendsto_nhdsGT_leftLim`). Consequently, the first time at which a path or its left
limit enters a closed set is attained whenever the path is right-continuous at that infimum and the
entry set is nonempty and bounded below
(`IsClosed.csInf_mem_or_leftLim_mem_of_continuousWithinAt`). In any preorder with closed lower
rays, upper bounds on `(-∞, t]` or `(-∞, T]` are preserved by strict left limits
(`TauCeti.leftLim_le_of_forall_le`, `TauCeti.upperBounds_image_Iic_subset_leftLim`). On a compact
lower ray `(-∞, T]`, no value or left limit of a càdlàg function into a linear order with the
order topology reaches `ε` if and only if its values on `(-∞, T]` admit a uniform upper bound
strictly below `ε` (`IsCadlag.forall_lt_and_leftLim_lt_iff_exists_le`), yielding the
complete-order supremum equivalence `IsCadlag.exists_le_or_le_leftLim_iff_le_biSup`.

For any path `f` into a pseudometric space and threshold `ε : ℝ`,
`TauCeti.oscillationExitAfter f ε u` takes the infimum of times strictly after `u` at which `f` or
its left limit deviates by at least `ε` from `f u.untopA` (or `⊤` when no such time exists), and
`TauCeti.oscillationExit f ε` iterates this operation from `⊥`. For a càdlàg path in an order
topology and `ε > 0`, each finite exit time lies strictly after the previous one and attains the
`ε`-deviation threshold; between consecutive times the path stays strictly within `ε` of the
left-endpoint value, and existence of left limits prevents infinitely many `ε`-exits from
accumulating below any finite horizon (`IsCadlag.tendsto_oscillationExit_top`).

## References

* P. Billingsley, *Convergence of Probability Measures*, second edition, Wiley, 1999, §12, Lemma 1.
* C. Dellacherie and P.-A. Meyer, *Probabilities and Potential*, Chapter IV, §64.
-/

public section

open Filter Function Set TopologicalSpace
open scoped ENNReal Topology

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

end TauCeti

/-- Along times approaching `x` strictly from the right, if `f` converges to `y` in a regular
space, then its strict left limit `f.leftLim` also converges to `y`. -/
theorem Filter.Tendsto.leftLim_nhdsGT {X Y : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [TopologicalSpace Y] [RegularSpace Y] {f : X → Y} {x : X} {y : Y}
    (h : Tendsto f (𝓝[>] x) (𝓝 y)) :
    Tendsto f.leftLim (𝓝[>] x) (𝓝 y) := by
  rcases eq_or_neBot (𝓝[>] x) with hbot | _
  · simp [hbot]
  apply (closed_nhds_basis y).tendsto_right_iff.2
  rintro V ⟨hV_mem, hV_closed⟩
  obtain ⟨b, hb⟩ : (Ioi x).Nonempty := nonempty_of_mem (self_mem_nhdsWithin (a := x))
  obtain ⟨u, hxu, hu⟩ : ∃ u, x < u ∧ Ioo x u ⊆ {t | f t ∈ V} := by
    have hpre := (closed_nhds_basis y).tendsto_right_iff.1 h V ⟨hV_mem, hV_closed⟩
    simpa using (mem_nhdsGT_iff_exists_Ioo_subset' hb).1 hpre
  filter_upwards [Ioo_mem_nhdsGT hxu] with r hr
  rcases eq_or_neBot (𝓝[<] r) with hr_bot | _
  · simpa [leftLim_eq_of_eq_bot f hr_bot] using hu hr
  by_cases hr_lim : ∃ l, Tendsto f (𝓝[<] r) (𝓝 l)
  · apply hV_closed.mem_of_tendsto (tendsto_leftLim_of_tendsto hr_lim)
    filter_upwards [Ioo_mem_nhdsLT hr.1] with s hs
    exact hu ⟨hs.1, hs.2.trans hr.2⟩
  · simpa [leftLim_eq_of_not_tendsto f hr_lim] using hu hr

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

end IsCadlag

namespace TauCeti

/-- An upper bound on `g` over `(-∞, t]` is preserved by its strict left limit at `t`, in any
preorder with closed lower rays. No càdlàg hypothesis is required. -/
theorem leftLim_le_of_forall_le {X α : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [Preorder α] [TopologicalSpace α] [ClosedIicTopology α]
    {g : X → α} {t : X} {c : α} (hg : ∀ s ≤ t, g s ≤ c) :
    g.leftLim t ≤ c :=
  isClosed_Iic.mem_of_mapClusterPt (mapClusterPt_leftLim g t) <|
    eventually_nhdsWithin_of_forall hg

/-- Every upper bound of `g` on `(-∞, T]` is also an upper bound of `g.leftLim` on `(-∞, T]`, in
any preorder with closed lower rays. No càdlàg hypothesis is required. -/
theorem upperBounds_image_Iic_subset_leftLim {X α : Type*} [LinearOrder X] [TopologicalSpace X]
    [OrderTopology X] [Preorder α] [TopologicalSpace α] [ClosedIicTopology α]
    (g : X → α) (T : X) :
    upperBounds (g '' Iic T) ⊆ upperBounds (g.leftLim '' Iic T) := by
  rintro c hc _ ⟨t, ht, rfl⟩
  exact leftLim_le_of_forall_le fun s hs => hc ⟨s, hs.trans ht, rfl⟩

end TauCeti

namespace IsCadlag

/-- On a compact lower ray `(-∞, T]`, no value or strict left limit of a càdlàg function into a
linear order with the order topology reaches `ε` if and only if its values on `(-∞, T]` admit a
uniform upper bound strictly below `ε`. -/
theorem forall_lt_and_leftLim_lt_iff_exists_le {X α : Type*}
    [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
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

/-- On a compact lower ray `(-∞, T]`, a càdlàg function into a complete linear order with the
order topology reaches `ε` in value or left limit at some time `t ≤ T` if and only if the supremum
of its values up to `T` is at least `ε`. -/
theorem exists_le_or_le_leftLim_iff_le_biSup {X α : Type*}
    [LinearOrder X] [TopologicalSpace X] [OrderTopology X]
    [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {g : X → α} (hg : IsCadlag g) {T : X} (hT : IsCompact (Iic T)) (ε : α) :
    (∃ t ≤ T, ε ≤ g t ∨ ε ≤ g.leftLim t) ↔ ε ≤ ⨆ t ≤ T, g t := by
  rw [← not_iff_not]
  push Not
  rw [hg.forall_lt_and_leftLim_lt_iff_exists_le hT]
  exact ⟨fun ⟨c, hc, hle⟩ => (iSup₂_le hle).trans_lt hc,
    fun h => ⟨⨆ t ≤ T, g t, h, fun t ht => le_iSup₂_of_le t ht le_rfl⟩⟩

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

namespace TauCeti

section OscillationExit

variable {X E : Type*} [ConditionallyCompleteLinearOrderBot X] [PseudoMetricSpace E]

/-- The infimum of times `t` strictly after `u` at which `f t` or its strict left limit
`f.leftLim t` lies at distance at least `ε` from `f u.untopA`, or `⊤` when no such time exists
(in particular when `u = ⊤`). For arbitrary `f` and `ε`, this infimum need neither lie strictly
after `u` nor attain the threshold; for a càdlàg path in an order topology with `ε > 0`, it
advances strictly whenever `u ≠ ⊤` (`IsCadlag.lt_oscillationExitAfter`), and any finite value
attains the `ε`-deviation threshold in value or strict left limit
(`IsCadlag.mem_of_oscillationExitAfter_eq_coe`). -/
noncomputable def oscillationExitAfter (f : X → E) (ε : ℝ) (u : WithTop X) : WithTop X :=
  open Classical in
  let A := {t : X | u < (t : WithTop X) ∧
    (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}
  if A.Nonempty then ↑(sInf A) else ⊤

/-- Iterated `ε`-oscillation exit times of a path `f`, obtained by iterating
`oscillationExitAfter f ε` starting from `⊥`. -/
noncomputable def oscillationExit (f : X → E) (ε : ℝ) : ℕ → WithTop X
  | 0 => (⊥ : X)
  | n + 1 => oscillationExitAfter f ε (oscillationExit f ε n)

@[simp]
theorem oscillationExit_zero (f : X → E) (ε : ℝ) :
    oscillationExit f ε 0 = ((⊥ : X) : WithTop X) :=
  (rfl)

@[simp]
theorem oscillationExit_succ (f : X → E) (ε : ℝ) (n : ℕ) :
    oscillationExit f ε (n + 1) = oscillationExitAfter f ε (oscillationExit f ε n) :=
  (rfl)

@[simp]
theorem oscillationExitAfter_top (f : X → E) (ε : ℝ) :
    oscillationExitAfter f ε ⊤ = ⊤ := by
  simp [oscillationExitAfter]

/-- The next oscillation exit time never precedes the starting time. -/
theorem le_oscillationExitAfter (f : X → E) (ε : ℝ) (u : WithTop X) :
    u ≤ oscillationExitAfter f ε u := by
  classical
  cases u with
  | top => simp
  | coe a =>
    dsimp only [oscillationExitAfter]
    split_ifs with hne
    · exact WithTop.coe_le_coe.mpr
        (le_csInf hne fun t ht => (WithTop.coe_lt_coe.mp ht.1).le)
    · exact le_top

/-- Iterated oscillation exit times form a nondecreasing sequence. -/
theorem oscillationExit_mono (f : X → E) (ε : ℝ) : Monotone (oscillationExit f ε) :=
  monotone_nat_of_le_succ fun n => le_oscillationExitAfter f ε (oscillationExit f ε n)

/-- `oscillationExitAfter f ε u` equals `⊤` if and only if no strictly later time reaches
distance `ε` from `f u.untopA` in value or strict left limit. -/
theorem oscillationExitAfter_eq_top_iff {f : X → E} {ε : ℝ} {u : WithTop X} :
    oscillationExitAfter f ε u = ⊤ ↔
      ∀ t : X, u < (t : WithTop X) →
        dist (f t) (f u.untopA) < ε ∧ dist (f.leftLim t) (f u.untopA) < ε := by
  classical
  dsimp only [oscillationExitAfter]
  split_ifs with hne
  · simp only [WithTop.coe_ne_top, false_iff, not_forall, not_and_or, not_lt]
    obtain ⟨t, ht1, ht2⟩ := hne
    exact ⟨t, ht1, ht2⟩
  · simp only [Set.not_nonempty_iff_eq_empty, Set.eq_empty_iff_forall_notMem,
      Set.mem_ofPred_eq, not_and, not_or, not_le] at hne
    exact ⟨fun _ => hne, fun _ => rfl⟩

/-- For `ε > 0`, at any time `t` with `u ≤ t` strictly before `oscillationExitAfter f ε u`,
the path remains within strict distance `ε` of `f u.untopA`. -/
theorem dist_lt_of_lt_oscillationExitAfter {f : X → E} {ε : ℝ} (hε : 0 < ε)
    {u : WithTop X} {t : X} (hut : u ≤ (t : WithTop X))
    (hlt : (t : WithTop X) < oscillationExitAfter f ε u) :
    dist (f t) (f u.untopA) < ε := by
  rcases eq_or_lt_of_le hut with rfl | hut'
  · simpa using hε
  · by_contra! hge
    classical
    have hmem : t ∈ {s : X | u < (s : WithTop X) ∧
        (ε ≤ dist (f s) (f u.untopA) ∨ ε ≤ dist (f.leftLim s) (f u.untopA))} :=
      ⟨hut', Or.inl hge⟩
    have hne : {s : X | u < (s : WithTop X) ∧
        (ε ≤ dist (f s) (f u.untopA) ∨ ε ≤ dist (f.leftLim s) (f u.untopA))}.Nonempty :=
      ⟨t, hmem⟩
    have hle : oscillationExitAfter f ε u ≤ (t : WithTop X) := by
      simp only [oscillationExitAfter, hne, ↓reduceIte, WithTop.coe_le_coe]
      exact csInf_le ⟨⊥, fun _ _ => bot_le⟩ hmem
    exact not_le_of_gt hlt hle

private noncomputable def stoppedEdist (f : X → E) (u : WithTop X) (t : X) : ℝ≥0∞ :=
  edist (f t) (f (min (t : WithTop X) u).untopA)

private theorem stoppedEdist_coe_apply (f : X → E) (a t : X) :
    stoppedEdist f a t = edist (f t) (f (min t a)) := by
  dsimp only [stoppedEdist]
  rw [← WithTop.coe_min]
  rfl

variable [TopologicalSpace X] [OrderTopology X]

private theorem isCadlag_stoppedEdist {f : X → E} (hf : IsCadlag f) (u : WithTop X) :
    IsCadlag (stoppedEdist f u) := by
  cases u with
  | top =>
    have heq : stoppedEdist f ⊤ = fun _ => (0 : ℝ≥0∞) := by
      ext t
      simp [stoppedEdist]
    rw [heq]
    exact IsCadlag.const
  | coe a =>
    have heq : stoppedEdist f a = fun t => edist (f t) (f (min t a)) :=
      funext (stoppedEdist_coe_apply f a)
    rw [heq]
    exact hf.continuous_comp₂ (hf.comp_min_const a) continuous_edist

private theorem setOf_oscillation_eq_stoppedEdist {f : X → E} (hf : IsCadlag f) {ε : ℝ}
    (hε : 0 < ε) (u : WithTop X) :
    {t : X | u < (t : WithTop X) ∧
        (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))} =
      {t : X | ENNReal.ofReal ε ≤ stoppedEdist f u t ∨
        ENNReal.ofReal ε ≤ (stoppedEdist f u).leftLim t} := by
  ext t
  simp only [mem_ofPred_eq]
  have hε_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
  cases u with
  | top =>
    have hzero : stoppedEdist f ⊤ = fun _ => (0 : ℝ≥0∞) := by
      ext s
      simp [stoppedEdist]
    simp [hzero, continuous_const.continuousWithinAt.leftLim_eq, not_le_of_gt hε_pos]
  | coe a =>
    rcases le_or_gt t a with hta | hat
    · have hval : stoppedEdist f a t = 0 := by
        rw [stoppedEdist_coe_apply, min_eq_left hta, edist_self]
      have hlim : (stoppedEdist f a).leftLim t = 0 := by
        rcases eq_or_neBot (𝓝[<] t) with hbot | _
        · rw [leftLim_eq_of_eq_bot _ hbot, hval]
        · refine leftLim_eq_of_tendsto (tendsto_const_nhds.congr' ?_)
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [stoppedEdist_coe_apply, min_eq_left ((le_of_lt hs).trans hta), edist_self]
      simp [not_lt_of_ge (WithTop.coe_le_coe.mpr hta), hval, hlim, not_le_of_gt hε_pos]
    · have hval : stoppedEdist f a t = edist (f t) (f a) := by
        rw [stoppedEdist_coe_apply, min_eq_right hat.le]
      have hlim : (stoppedEdist f a).leftLim t = edist (f.leftLim t) (f a) := by
        rcases eq_or_neBot (𝓝[<] t) with hbot | _
        · rw [leftLim_eq_of_eq_bot _ hbot, leftLim_eq_of_eq_bot _ hbot, hval]
        · refine leftLim_eq_of_tendsto
            ((((continuous_id.edist continuous_const).tendsto (f.leftLim t)).comp
              (hf.tendsto_nhdsLT_leftLim t)).congr' ?_)
          filter_upwards [Ioo_mem_nhdsLT hat] with s hs
          rw [stoppedEdist_coe_apply, min_eq_right hs.1.le]
          rfl
      simp [WithTop.coe_lt_coe.mpr hat, hval, hlim, edist_dist,
        ENNReal.ofReal_le_ofReal_iff dist_nonneg]

end OscillationExit

end TauCeti

namespace IsCadlag

section OscillationExit

variable {X E : Type*} [ConditionallyCompleteLinearOrderBot X] [TopologicalSpace X]
  [OrderTopology X] [PseudoMetricSpace E]

/-- When a càdlàg path has a finite `ε`-oscillation exit time `s` after `u` (`ε > 0`), `s` lies
strictly after `u` and attains the `ε`-deviation threshold in value or strict left limit. -/
theorem mem_of_oscillationExitAfter_eq_coe {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    {u : WithTop X} {s : X} (hs : TauCeti.oscillationExitAfter f ε u = s) :
    u < (s : WithTop X) ∧
      (ε ≤ dist (f s) (f u.untopA) ∨ ε ≤ dist (f.leftLim s) (f u.untopA)) := by
  classical
  let A := {t : X | u < (t : WithTop X) ∧
    (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA))}
  have hne : A.Nonempty := by
    by_contra h
    simp [TauCeti.oscillationExitAfter, A, h] at hs
  have hs_eq : s = sInf A := by
    simpa [TauCeti.oscillationExitAfter, A, hne] using hs.symm
  have hA_eq := TauCeti.setOf_oscillation_eq_stoppedEdist hf hε u
  have hmem : sInf A ∈ A := by
    dsimp only [A]
    rw [hA_eq]
    exact isClosed_Ici.csInf_mem_or_leftLim_mem_of_continuousWithinAt
      ((TauCeti.isCadlag_stoppedEdist hf u).isRightContinuous _) (hA_eq ▸ hne)
      ⟨⊥, fun _ _ => bot_le⟩
  exact hs_eq ▸ hmem

/-- After any finite time `u`, the next `ε`-oscillation exit (`ε > 0`) of a càdlàg path occurs
strictly later, including when it is `⊤`. -/
theorem lt_oscillationExitAfter {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    {u : WithTop X} (hu : u ≠ ⊤) : u < TauCeti.oscillationExitAfter f ε u := by
  cases h : TauCeti.oscillationExitAfter f ε u with
  | top => exact lt_top_iff_ne_top.mpr hu
  | coe s => exact (hf.mem_of_oscillationExitAfter_eq_coe hε h).1

/-- For a càdlàg path and `ε > 0`, the next `ε`-oscillation exit occurs by `T` if and only if an
actual `ε`-deviation in value or left limit occurs at some time in `(u, T]`. -/
theorem oscillationExitAfter_le_coe_iff {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    (u : WithTop X) (T : X) :
    TauCeti.oscillationExitAfter f ε u ≤ (T : WithTop X) ↔
      ∃ t ≤ T, u < (t : WithTop X) ∧
        (ε ≤ dist (f t) (f u.untopA) ∨ ε ≤ dist (f.leftLim t) (f u.untopA)) := by
  constructor
  · intro hle
    obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top hle)
    have hmem := hf.mem_of_oscillationExitAfter_eq_coe hε hs.symm
    exact ⟨s, WithTop.coe_le_coe.mp (hs ▸ hle), hmem⟩
  · rintro ⟨t, htT, hut, hdev⟩
    classical
    have hmem : t ∈ {s : X | u < (s : WithTop X) ∧
        (ε ≤ dist (f s) (f u.untopA) ∨ ε ≤ dist (f.leftLim s) (f u.untopA))} := ⟨hut, hdev⟩
    have hne : {s : X | u < (s : WithTop X) ∧
        (ε ≤ dist (f s) (f u.untopA) ∨ ε ≤ dist (f.leftLim s) (f u.untopA))}.Nonempty :=
      ⟨t, hmem⟩
    simp only [TauCeti.oscillationExitAfter, hne, ↓reduceIte, WithTop.coe_le_coe]
    exact (csInf_le ⟨⊥, fun _ _ => bot_le⟩ hmem).trans htT

/-- In a second-countable order topology with a conditionally complete linear order with bottom,
each horizon `T` admits a single countable subset `S ⊆ (-∞, T]` that characterizes the sublevel
event `oscillationExitAfter f ε u ≤ T` for every càdlàg path `f`, threshold `ε > 0`, and starting
time `u` via a countable supremum of extended distances. -/
theorem exists_countable_subset_Iic_oscillationExitAfter_le_coe_iff
    [SecondCountableTopology X] (T : X) :
    ∃ S : Set X, S.Countable ∧ S ⊆ Iic T ∧
      ∀ ⦃f : X → E⦄, IsCadlag f → ∀ ⦃ε : ℝ⦄, 0 < ε → ∀ (u : WithTop X),
        TauCeti.oscillationExitAfter f ε u ≤ (T : WithTop X) ↔
          ENNReal.ofReal ε ≤
            ⨆ s ∈ S, edist (f s) (f (min (s : WithTop X) u).untopA) := by
  obtain ⟨S, hSc, hST, hS⟩ :=
    TopologicalSpace.exists_countable_subset_Iic_biSup_eq (α := ℝ≥0∞) T
  refine ⟨S, hSc, hST, fun f hf ε hε u => ?_⟩
  have hT : IsCompact (Iic T) := by
    rw [← Icc_bot]
    exact isCompact_Icc
  have hset := Set.ext_iff.mp (TauCeti.setOf_oscillation_eq_stoppedEdist hf hε u)
  simp only [mem_ofPred_eq] at hset
  rw [hf.oscillationExitAfter_le_coe_iff hε u T]
  simp_rw [hset]
  rw [(TauCeti.isCadlag_stoppedEdist hf u).exists_le_or_le_leftLim_iff_le_biSup hT
      (ENNReal.ofReal ε),
    ← hS fun t _ => (TauCeti.isCadlag_stoppedEdist hf u).isRightContinuous t]
  rfl

/-- A càdlàg path has only finitely many `ε`-oscillation exits (`ε > 0`) on `[⊥, T]`: its iterated
exit times eventually lie strictly beyond `T`. -/
theorem eventually_lt_oscillationExit {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε)
    (T : X) : ∀ᶠ n in atTop, (T : WithTop X) < TauCeti.oscillationExit f ε n := by
  suffices ∃ N, (T : WithTop X) < TauCeti.oscillationExit f ε N by
    obtain ⟨N, hN⟩ := this
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans_le (TauCeti.oscillationExit_mono f ε hn)
  -- Otherwise all exit times are finite, strictly increasing, and bounded above by `T`.
  by_contra! hle
  have hne_top (n : ℕ) : TauCeti.oscillationExit f ε n ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top (hle n)
  choose t ht using fun n => WithTop.ne_top_iff_exists.mp (hne_top n)
  have ht_le (n : ℕ) : t n ≤ T := WithTop.coe_le_coe.mp (ht n ▸ hle n)
  have ht_strict : StrictMono t := strictMono_nat_of_lt_succ fun n => by
    have hlt := hf.lt_oscillationExitAfter hε (hne_top n)
    rw [← TauCeti.oscillationExit_succ, ← ht n, ← ht (n + 1)] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  -- Their supremum `s ≤ T` is approached strictly from the left, where `f` tends to `f.leftLim s`.
  have hbdd : BddAbove (range t) := ⟨T, forall_mem_range.mpr ht_le⟩
  let s : X := ⨆ n, t n
  have ht_lt_s (n : ℕ) : t n < s := (ht_strict (Nat.lt_succ_self n)).trans_le (le_ciSup hbdd _)
  have ht_nhds : Tendsto t atTop (𝓝 s) := tendsto_atTop_ciSup ht_strict.monotone hbdd
  have ht_nhdsLT : Tendsto t atTop (𝓝[<] s) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within t ht_nhds
      (Eventually.of_forall ht_lt_s)
  have : (𝓝[<] s).NeBot := neBot_of_le ht_nhdsLT
  have hball : {x | dist (f x) (f.leftLim s) < ε / 3} ∈ 𝓝[<] s :=
    (hf.tendsto_nhdsLT_leftLim s).eventually
      ((continuous_id.dist continuous_const).isOpen_preimage _ isOpen_Iio |>.mem_nhds
        (by simp [div_pos hε zero_lt_three]))
  obtain ⟨u, hus, hu⟩ :=
    (mem_nhdsLT_iff_exists_Ioo_subset' (ht_lt_s 0)).mp hball
  -- Once `t N ∈ (u, s)`, `f (t N)`, `f (t (N + 1))`, and `f.leftLim (t (N + 1))` all lie within
  -- `ε / 3` of `f.leftLim s`, contradicting the `ε`-threshold at `t (N + 1)`.
  obtain ⟨N, hN⟩ := (ht_nhds.eventually (Ioi_mem_nhds hus)).exists
  have hN_mem : t N ∈ Ioo u s := ⟨hN, ht_lt_s N⟩
  have hN1_mem : t (N + 1) ∈ Ioo u s := ⟨hN.trans (ht_strict (Nat.lt_succ_self N)), ht_lt_s _⟩
  have hd_N : dist (f (t N)) (f.leftLim s) < ε / 3 := hu hN_mem
  have hd_N1 : dist (f (t (N + 1))) (f.leftLim s) < ε / 3 := hu hN1_mem
  have hd_lim : dist (f.leftLim (t (N + 1))) (f.leftLim s) ≤ ε / 3 := by
    rcases eq_or_neBot (𝓝[<] (t (N + 1))) with hbot | _
    · rw [leftLim_eq_of_eq_bot f hbot]
      exact hd_N1.le
    · refine le_of_tendsto
        (((continuous_id.dist continuous_const).tendsto _).comp
          (hf.tendsto_nhdsLT_leftLim (t (N + 1)))) ?_
      filter_upwards [Ioo_mem_nhdsLT hN1_mem.1] with x hx
      exact (hu ⟨hx.1, hx.2.trans hN1_mem.2⟩).le
  have hexit : TauCeti.oscillationExitAfter f ε (t N) = t (N + 1) := by
    rw [ht N, ht (N + 1), TauCeti.oscillationExit_succ]
  rcases (hf.mem_of_oscillationExitAfter_eq_coe hε hexit).2 with hval | hleft
  · simp only [WithTop.untopD_coe] at hval
    have htri := dist_triangle_right (f (t (N + 1))) (f (t N)) (f.leftLim s)
    linarith
  · simp only [WithTop.untopD_coe] at hleft
    have htri := dist_triangle_right (f.leftLim (t (N + 1))) (f (t N)) (f.leftLim s)
    linarith

/-- Iterated `ε`-oscillation exit times (`ε > 0`) of a càdlàg path tend to `⊤`. -/
theorem tendsto_oscillationExit_top {f : X → E} (hf : IsCadlag f) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (TauCeti.oscillationExit f ε) atTop (𝓝 ⊤) :=
  (WithTop.tendsto_nhds_top_iff _).mpr (hf.eventually_lt_oscillationExit hε)

end OscillationExit

end IsCadlag
