/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.PlotOn

/-!
# Subductions

This file defines when a map to a target locally lifts through a map from a diffeological space,
and uses it to define subductions: smooth surjections through which every plot of the target
locally lifts to a plot of the source. A function out of the target of a subduction is
diffeologically smooth exactly when its composite with the subduction is smooth.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Articles 1.46--1.51.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Q Y : Type*} [DiffeologicalSpace X]

/-! ### Local lifts -/

/-- A map to the target locally lifts through a map on a subset if every point has an open
neighborhood in the subset on which the map agrees with the image of a source plot. -/
def LocallyLifts (q : X → Q) {n : ℕ} (u : Set (𝔼ⁿ)) (p : 𝔼ⁿ → Q) : Prop :=
  ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ v ⊆ u ∧
    ∃ lift : 𝔼ⁿ → X, IsPlotOn v lift ∧ EqOn (q ∘ lift) p v

/-- A map locally lifts on a subset exactly when every point has an open neighborhood in the
subset on which the map agrees with the image of a source plot. -/
theorem locallyLifts_iff {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q} :
    LocallyLifts q u p ↔ ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ v ⊆ u ∧
      ∃ lift : 𝔼ⁿ → X, IsPlotOn v lift ∧ EqOn (q ∘ lift) p v :=
  Iff.rfl

/-- The image of a plot on an open subset locally lifts through the map on that subset. -/
theorem IsPlotOn.locallyLifts_comp {n : ℕ} (q : X → Q) {u : Set (𝔼ⁿ)} {lift : 𝔼ⁿ → X}
    (hlift : IsPlotOn u lift) (hu : IsOpen u) : LocallyLifts q u (q ∘ lift) :=
  fun _ hz ↦ ⟨u, hu, hz, Subset.rfl, lift, hlift, eqOn_refl _ _⟩

/-- The constant map at an image point locally lifts through the map on every open subset. -/
theorem locallyLifts_const {n : ℕ} (q : X → Q) {u : Set (𝔼ⁿ)} (hu : IsOpen u) (x : X) :
    LocallyLifts q u (fun _ ↦ q x) :=
  (isPlotOn_const u x).locallyLifts_comp q hu

/-- The local lifting property depends only on the restriction of the map to its domain. -/
theorem LocallyLifts.congr {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p p' : 𝔼ⁿ → Q}
    (hp : LocallyLifts q u p) (hpp' : EqOn p p' u) : LocallyLifts q u p' := by
  intro z hz
  obtain ⟨v, hv, hzv, hvu, lift, hlift, hq⟩ := hp z hz
  exact ⟨v, hv, hzv, hvu, lift, hlift, hq.trans (hpp'.mono hvu)⟩

/-- The local lifting property passes to open subsets. -/
theorem LocallyLifts.mono {n : ℕ} {q : X → Q} {u v : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q}
    (hp : LocallyLifts q u p) (hv : IsOpen v) (hvu : v ⊆ u) : LocallyLifts q v p := by
  intro z hz
  obtain ⟨w, hw, hzw, _, lift, hlift, hq⟩ := hp z (hvu hz)
  exact ⟨w ∩ v, hw.inter hv, ⟨hzw, hz⟩, inter_subset_right, lift,
    hlift.mono inter_subset_left, hq.mono inter_subset_left⟩

/-- Locally liftable maps are stable under smooth reparametrization on open subsets. -/
theorem LocallyLifts.comp_contDiffOn {n m : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)}
    {v : Set (𝔼ᵐ)} {p : 𝔼ⁿ → Q} {f : 𝔼ᵐ → 𝔼ⁿ}
    (hp : LocallyLifts q u p) (hv : IsOpen v) (hf : ContDiffOn ℝ ∞ f v)
    (hfu : MapsTo f v u) : LocallyLifts q v (p ∘ f) := by
  intro z hz
  obtain ⟨w, hw, hfw, hwu, lift, hlift, hq⟩ := hp (f z) (hfu hz)
  have hfcont : ContinuousAt f z :=
    (hf z hz).continuousWithinAt.continuousAt (hv.mem_nhds hz)
  have hpre : f ⁻¹' w ∈ 𝓝 z := hfcont.preimage_mem_nhds (hw.mem_nhds hfw)
  obtain ⟨a, ha, haopen, hza⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem (hv.mem_nhds hz) hpre)
  have hav : a ⊆ v := fun y hy ↦ (ha hy).1
  have haw : MapsTo f a w := fun y hy ↦ (ha hy).2
  refine ⟨a, haopen, hza, hav, lift ∘ f, ?_, ?_⟩
  · exact hlift.comp_contDiffOn (hf.mono hav) haw
  · intro y hy
    exact hq (haw hy)

/-- A locally local lifting property glues to a local lifting property. -/
theorem locallyLifts_of_locally {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q}
    (hu : IsOpen u)
    (hp : ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ LocallyLifts q v p) :
    LocallyLifts q u p := by
  intro z hz
  obtain ⟨v, _, hzv, hpv⟩ := hp z hz
  obtain ⟨w, hw, hzw, hwv, lift, hlift, hq⟩ := hpv z hzv
  exact ⟨w ∩ u, hw.inter hu, ⟨hzw, hz⟩, inter_subset_right, lift,
    hlift.mono inter_subset_left, hq.mono inter_subset_left⟩

/-- Postcomposing both the map and the map lifted through with a function preserves the local
lifting property. -/
theorem LocallyLifts.comp_left {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → Q}
    (hp : LocallyLifts q u p) (f : Q → Y) : LocallyLifts (f ∘ q) u (f ∘ p) := by
  intro z hz
  obtain ⟨v, hv, hzv, hvu, lift, hlift, hq⟩ := hp z hz
  exact ⟨v, hv, hzv, hvu, lift, hlift, hq.comp_left (g := f)⟩

/-- A map that locally lifts through a smooth map is a plot on its domain. -/
theorem LocallyLifts.isPlotOn [DiffeologicalSpace Q] {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)}
    {p : 𝔼ⁿ → Q} (hp : LocallyLifts q u p) (hq : _root_.Diffeology.DSmooth q) :
    IsPlotOn u p := by
  refine isPlotOn_of_locally fun z hz ↦ ?_
  obtain ⟨v, hv, hzv, _, lift, hlift, hqlift⟩ := hp z hz
  exact ⟨v, hv, hzv, (hlift.dSmooth_comp hq).congr hqlift⟩

/-! ### Subductions -/

/-- A smooth surjection is a subduction if every target plot locally lifts to a source plot. -/
structure IsSubduction [DiffeologicalSpace Q] (q : X → Q) : Prop where
  /-- A subduction is surjective. -/
  surjective : Surjective q
  /-- A subduction is smooth. -/
  dSmooth : _root_.Diffeology.DSmooth q
  /-- Every plot of the target locally lifts through a subduction. -/
  locallyLifts {n : ℕ} {p : 𝔼ⁿ → Q} : _root_.Diffeology.IsPlot p → LocallyLifts q univ p

/-- The plots of the target of a subduction are exactly the maps that locally lift through it. -/
theorem IsSubduction.isPlot_iff [DiffeologicalSpace Q] {q : X → Q} (hq : IsSubduction q)
    {n : ℕ} {p : 𝔼ⁿ → Q} : _root_.Diffeology.IsPlot p ↔ LocallyLifts q univ p :=
  ⟨hq.locallyLifts, fun hp ↦ (hp.isPlotOn hq.dSmooth).isPlot⟩

/-- Descent along a subduction: a function from the target is smooth exactly when its composite
with the subduction is smooth. -/
theorem IsSubduction.dSmooth_iff [DiffeologicalSpace Q] [DiffeologicalSpace Y]
    {q : X → Q} (hq : IsSubduction q) (f : Q → Y) :
    _root_.Diffeology.DSmooth f ↔ _root_.Diffeology.DSmooth (f ∘ q) :=
  ⟨fun hf ↦ hf.comp hq.dSmooth,
    fun hf _ _ hp ↦ (((hq.locallyLifts hp).comp_left f).isPlotOn hf).isPlot⟩

end TauCeti.Diffeology
