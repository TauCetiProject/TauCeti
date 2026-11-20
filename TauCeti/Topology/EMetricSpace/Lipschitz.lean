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
import Mathlib.Topology.Metrizable.Basic

/-!
# Lipschitz maps from extended metric spaces

This file gives a real-valued Lipschitz estimate for the extended distance from a fixed point,
shows that the inclusion of a subset into a larger subset is `1`-Lipschitz, records that a map
Lipschitz on a set is locally Lipschitz on that set (`LipschitzOnWith.locallyLipschitzOn`), covers
any separable set on which a map is locally Lipschitz by countably many open sets on whose
intersections with the set the map is Lipschitz
(`LocallyLipschitzOn.exists_open_cover_lipschitzOnWith`), and shows (`LocallyLipschitzOn.comp`),
also for outer maps locally Lipschitz only on a set containing the image, that composing a function
locally Lipschitz on a set with a locally Lipschitz map keeps it locally Lipschitz on that set.

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
  -- At finite distance the triangle inequality transfers to real numbers, since then
  -- `edist a x = ∞` whenever `edist a y = ∞`.
  have key {x y : X} (hxy : edist x y ≠ ∞) :
      (edist a x).toReal - (edist a y).toReal ≤ (edist x y).toReal := by
    refine sub_le_iff_le_add'.2 (ENNReal.toReal_le_add_of_top_imp_top
      ((edist_triangle a y x).trans_eq (by rw [edist_comm y x])) (fun hay ↦ ?_) (absurd · hxy))
    simpa [hay, hxy] using edist_triangle a x y
  refine LipschitzWith.of_edist_le fun x y ↦ ?_
  rcases eq_or_ne (edist x y) ∞ with hxy | hxy
  · simp [hxy]
  rw [edist_dist, Real.dist_eq]
  refine ENNReal.ofReal_le_of_le_toReal (abs_sub_le_iff.2 ⟨key hxy, ?_⟩)
  simpa only [edist_comm y x] using key (x := y) (y := x) (by rwa [edist_comm])

end TauCeti

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
  -- The open sets on which `f` is Lipschitz on their intersection with `s`, each with a
  -- Lipschitz constant; the empty set shows that this index type is nonempty.
  let ι := {p : Set α × ℝ≥0 // IsOpen p.1 ∧ LipschitzOnWith p.2 f (s ∩ p.1)}
  have : Nonempty ι := ⟨⟨(∅, 0), isOpen_empty, by simp⟩⟩
  have hcov : s ⊆ ⋃ i : ι, i.val.1 := fun x hx ↦ by
    obtain ⟨K, t, ht, hK⟩ := hf hx
    obtain ⟨U, hU, hxU, hUt⟩ := mem_nhdsWithin.1 ht
    exact mem_iUnion.2 ⟨⟨(U, K), hU, hK.mono fun y hy ↦ hUt ⟨hy.2, hy.1⟩⟩, hxU⟩
  -- A separable set is Lindelöf, since its subtype is second countable.
  have : SecondCountableTopology s := hs.secondCountableTopology
  obtain ⟨g, hg⟩ := (isLindelof_iff_lindelofSpace.2 inferInstance).indexed_countable_subcover
    (fun i : ι ↦ i.val.1) (fun i ↦ i.property.1) hcov
  exact ⟨fun n ↦ (g n).val.1, fun n ↦ (g n).val.2, fun n ↦ (g n).property.1, hg,
    fun n ↦ (g n).property.2⟩

/-- Composing a function locally Lipschitz on `s` with a map locally Lipschitz on a set `t`
containing its image gives a function locally Lipschitz on `s`. -/
protected theorem LocallyLipschitzOn.comp {α β γ : Type*} [PseudoEMetricSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {g : β → γ} {f : α → β} {s : Set α}
    {t : Set β} (hg : LocallyLipschitzOn t g) (hf : LocallyLipschitzOn s f) (hst : MapsTo f s t) :
    LocallyLipschitzOn s (g ∘ f) := by
  intro x hx
  obtain ⟨Kf, u, hu, hKf⟩ := hf hx
  obtain ⟨Kg, v, hv, hKg⟩ := hg (hst hx)
  refine ⟨Kg * Kf, u ∩ f ⁻¹' v,
    inter_mem hu ((hf.continuousOn x hx).tendsto_nhdsWithin hst hv), ?_⟩
  exact hKg.comp (hKf.mono inter_subset_left) fun _ hy => hy.2
