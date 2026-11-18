/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Metrizable.Basic

/-!
# Lipschitz maps from extended metric spaces

This file gives a real-valued Lipschitz estimate for the extended distance from a fixed point,
shows that the inclusion of a subset into a larger subset is `1`-Lipschitz, records that a map
Lipschitz on a set is locally Lipschitz on that set (`LipschitzOnWith.locallyLipschitzOn`), covers
any separable set on which a map is locally Lipschitz by countably many open sets on whose
intersections with the set the map is Lipschitz
(`LocallyLipschitzOn.exists_open_cover_lipschitzOnWith`), and shows that composing a function
locally Lipschitz on a set with a locally Lipschitz map keeps it locally Lipschitz on that set.

`LipschitzOnWith.closure_of_continuousWithinAt` extends a Lipschitz bound to the closure when
continuity is supplied only at the added points. `LipschitzOnWith.Icc_of_Ico` specializes this
to a half-open real interval. `LipschitzOnWith.edist_apply_min_le` controls a backward time clamp.

The declaration `TauCeti.lipschitzWith_toReal_edist` and its proof follow
[Mathlib pull request #41839](https://github.com/leanprover-community/mathlib4/pull/41839),
available under Apache 2.0.
-/

public section

open Filter Set
open scoped ENNReal NNReal Topology

namespace TauCeti

/-- Distance from a fixed point, converted to a real number, is `1`-Lipschitz. -/
theorem lipschitzWith_toReal_edist {X : Type*} [PseudoEMetricSpace X] (a : X) :
    LipschitzWith 1 (fun x ↦ (edist a x).toReal) := by
  intro x y
  by_cases hxy : edist x y = ∞
  · simp [hxy]
  have hxy' : edist y x ≠ ∞ := by simpa only [edist_comm] using hxy
  by_cases hax : edist a x = ∞
  · have hay : edist a y = ∞ := by
      by_contra hay
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hay, hxy'⟩) (edist_triangle a y x) hax
    simp [hax, hay]
  have hay : edist a y ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hax, hxy⟩) (edist_triangle a x y)
  suffices ENNReal.ofReal (dist (edist a x).toReal (edist a y).toReal) ≤ edist x y by
    simpa only [edist_dist, ENNReal.coe_one, one_mul] using this
  rw [ENNReal.ofReal_le_iff_le_toReal hxy, Real.dist_eq, abs_le]
  have hforward := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hax, hxy⟩)
    (edist_triangle a x y)
  have hbackward := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hay, hxy'⟩)
    (edist_triangle a y x)
  rw [ENNReal.toReal_add hax hxy] at hforward
  rw [ENNReal.toReal_add hay hxy', edist_comm y x] at hbackward
  constructor <;> linarith

end TauCeti

/-- A Lipschitz bound extends to the closure if the prescribed values at the added points are
continuous limits from the original set. Continuity on the original set follows from the bound. -/
theorem LipschitzOnWith.closure_of_continuousWithinAt {X Y : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {f : X → Y} {s : Set X} {L : ℝ≥0}
    (hf : LipschitzOnWith L f s)
    (hc : ∀ x ∈ closure s \ s, ContinuousWithinAt f s x) :
    LipschitzOnWith L f (closure s) := by
  have hcont (x : X) (hx : x ∈ closure s) : ContinuousWithinAt f s x := by
    by_cases hxs : x ∈ s
    · exact hf.continuousOn x hxs
    · exact hc x ⟨hx, hxs⟩
  exact hf.closure (continuousOn_closure_inter_setOf.mono fun x hx ↦ ⟨hx, hcont x hx⟩)

/-- A Lipschitz bound on `[a, b)` extends to `[a, b]` when the value at `b` is its left limit.
The closed interval may be empty or a singleton. -/
theorem LipschitzOnWith.Icc_of_Ico {Y : Type*} [PseudoEMetricSpace Y] {f : ℝ → Y}
    {a b : ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Ico a b))
    (hb : ContinuousWithinAt f (Iio b) b) : LipschitzOnWith L f (Icc a b) := by
  by_cases hab : a < b
  · rw [← closure_Ico hab.ne]
    apply hf.closure_of_continuousWithinAt
    intro t ht
    have htb : t = b := by
      rw [closure_Ico hab.ne] at ht
      exact le_antisymm ht.1.2 (not_lt.mp fun h ↦ ht.2 ⟨ht.1.1, h⟩)
    subst t
    exact hb.mono Ico_subset_Iio_self
  · intro x hx y hy
    have hxy : x = y := by linarith [not_lt.mp hab, hx.1, hx.2, hy.1, hy.2]
    subst y
    simp

/-- A Lipschitz bound on `[a, b]` controls displacement under clamping a time at `a`.
If the time is already at most `a`, the displacement is zero. -/
theorem LipschitzOnWith.edist_apply_min_le {Y : Type*} [PseudoEMetricSpace Y]
    {f : ℝ → Y} {a b t : ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Icc a b)) (ht : t ≤ b) :
    edist (f t) (f (min t a)) ≤ L * edist a b := by
  by_cases hta : t ≤ a
  · simp only [min_eq_left hta, edist_self]
    exact zero_le
  · have hat : a ≤ t := le_of_not_ge hta
    have hab : a ≤ b := hat.trans ht
    rw [min_eq_right hat]
    refine (hf ⟨hat, ht⟩ ⟨le_rfl, hab⟩).trans (mul_le_mul' le_rfl ?_)
    rw [edist_dist, edist_dist]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.dist_eq, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hat),
      abs_of_nonpos (sub_nonpos.mpr hab)]
    linarith

/-- The inclusion of a subset into a larger subset is `1`-Lipschitz. -/
protected theorem LipschitzWith.inclusion {α : Type*} [PseudoEMetricSpace α] {s t : Set α}
    (h : s ⊆ t) : LipschitzWith 1 (Set.inclusion h) :=
  LipschitzWith.of_edist_le fun _ _ ↦ le_rfl

/-- A function that is Lipschitz on `s` is locally Lipschitz on `s`. -/
protected theorem LipschitzOnWith.locallyLipschitzOn {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] {K : ℝ≥0} {f : α → β} {s : Set α} (hf : LipschitzOnWith K f s) :
    LocallyLipschitzOn s f :=
  fun _ _ ↦ ⟨K, s, self_mem_nhdsWithin, hf⟩

/-- If `f` is locally Lipschitz on a separable set `s` in an extended pseudometric space (for
instance any set in a second-countable space, by `TopologicalSpace.IsSeparable.of_separableSpace`),
then `s` can be covered by countably many open sets `U n` such that `f` is Lipschitz on each
`s ∩ U n`. -/
theorem LocallyLipschitzOn.exists_open_cover_lipschitzOnWith {α β : Type*}
    [PseudoEMetricSpace α] [PseudoEMetricSpace β]
    {s : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) (hs : TopologicalSpace.IsSeparable s) :
    ∃ (U : ℕ → Set α) (K : ℕ → ℝ≥0),
      (∀ n, IsOpen (U n)) ∧ s ⊆ ⋃ n, U n ∧ ∀ n, LipschitzOnWith (K n) f (s ∩ U n) := by
  have hloc : ∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ K, LipschitzOnWith K f (s ∩ U) := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := hf hx
    obtain ⟨U, hU, hxU, hUt⟩ := mem_nhdsWithin.1 ht
    exact ⟨U, hU, hxU, K, hK.mono ((inter_comm s U).subset.trans hUt)⟩
  choose! U hU hxU K hK using hloc
  -- A separable set is Lindelöf, since its subtype is second countable.
  have : SecondCountableTopology s := hs.secondCountableTopology
  obtain ⟨c, hc, hcs, hcov⟩ := (isLindelof_iff_lindelofSpace.2 inferInstance).elim_nhds_subcover U
    fun x hx ↦ (hU x hx).mem_nhds (hxU x hx)
  rcases c.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ ↦ ∅, fun _ ↦ 0, fun _ ↦ isOpen_empty, ?_, fun _ ↦ by simp⟩
    simpa using hcov
  · obtain ⟨g, rfl⟩ := hc.exists_eq_range hne
    refine ⟨fun n ↦ U (g n), fun n ↦ K (g n), fun n ↦ hU _ (hcs _ (mem_range_self n)),
      fun x hx ↦ ?_, fun n ↦ hK _ (hcs _ (mem_range_self n))⟩
    obtain ⟨_, ⟨n, rfl⟩, hxU'⟩ := mem_iUnion₂.1 (hcov hx)
    exact mem_iUnion.2 ⟨n, hxU'⟩

/-- A locally Lipschitz map composed with a function locally Lipschitz on `s` is locally Lipschitz
on `s`. -/
theorem LocallyLipschitz.comp_locallyLipschitzOn {α β γ : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {g : β → γ} {f : α → β} {s : Set α}
    (hg : LocallyLipschitz g) (hf : LocallyLipschitzOn s f) : LocallyLipschitzOn s (g ∘ f) := by
  intro x hx
  obtain ⟨Kf, t, ht, hKf⟩ := hf hx
  obtain ⟨Kg, U, hU, hKg⟩ := hg (f x)
  refine ⟨Kg * Kf, t ∩ f ⁻¹' U, inter_mem ht (hf.continuousOn x hx hU), ?_⟩
  exact hKg.comp (hKf.mono inter_subset_left) fun _ hy => hy.2
