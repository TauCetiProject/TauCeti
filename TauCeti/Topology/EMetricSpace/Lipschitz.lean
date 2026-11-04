/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Lipschitz maps from extended metric spaces

This file gives a real-valued Lipschitz estimate for the extended distance from a fixed point,
records that a map Lipschitz on a set is locally Lipschitz on that set
(`LipschitzOnWith.locallyLipschitzOn`), covers any set in a second-countable space on which a map
is locally Lipschitz by countably many open sets on whose intersections with the set the map is
Lipschitz (`LocallyLipschitzOn.exists_open_cover_lipschitzOnWith`), and shows that composing a
function locally Lipschitz on a set with a locally Lipschitz map keeps it locally Lipschitz on
that set.

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

/-- A function that is Lipschitz on `s` is locally Lipschitz on `s`. -/
protected theorem LipschitzOnWith.locallyLipschitzOn {α β : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] {K : ℝ≥0} {f : α → β} {s : Set α} (hf : LipschitzOnWith K f s) :
    LocallyLipschitzOn s f :=
  fun _ _ ↦ ⟨K, s, self_mem_nhdsWithin, hf⟩

/-- If `f` is locally Lipschitz on a set `s` in a second-countable extended pseudometric space,
then `s` can be covered by countably many open sets `U n` such that `f` is Lipschitz on each
`s ∩ U n`. -/
theorem LocallyLipschitzOn.exists_open_cover_lipschitzOnWith {α β : Type*}
    [PseudoEMetricSpace α] [SecondCountableTopology α] [PseudoEMetricSpace β]
    {s : Set α} {f : α → β} (hf : LocallyLipschitzOn s f) :
    ∃ (U : ℕ → Set α) (K : ℕ → ℝ≥0),
      (∀ n, IsOpen (U n)) ∧ s ⊆ ⋃ n, U n ∧ ∀ n, LipschitzOnWith (K n) f (s ∩ U n) := by
  have hloc : ∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U ∧ ∃ K, LipschitzOnWith K f (s ∩ U) := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := hf hx
    obtain ⟨U, hU, hxU, hUt⟩ := mem_nhdsWithin.1 ht
    exact ⟨U, hU, hxU, K, hK.mono ((inter_comm s U).subset.trans hUt)⟩
  choose! U hU hxU K hK using hloc
  obtain ⟨c, hcs, hc, hcov⟩ := TopologicalSpace.countable_cover_nhdsWithin
    (f := fun x ↦ s ∩ U x) fun x hx ↦ inter_mem_nhdsWithin s ((hU x hx).mem_nhds (hxU x hx))
  rcases c.eq_empty_or_nonempty with rfl | hne
  · refine ⟨fun _ ↦ ∅, fun _ ↦ 0, fun _ ↦ isOpen_empty, ?_, fun _ ↦ by simp⟩
    simpa using hcov
  · obtain ⟨g, rfl⟩ := hc.exists_eq_range hne
    refine ⟨fun n ↦ U (g n), fun n ↦ K (g n), fun n ↦ hU _ (hcs (mem_range_self n)),
      fun x hx ↦ ?_, fun n ↦ hK _ (hcs (mem_range_self n))⟩
    obtain ⟨_, ⟨n, rfl⟩, -, hxU'⟩ := mem_iUnion₂.1 (hcov hx)
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
