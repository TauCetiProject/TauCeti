/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Diffeology.Basic

/-!
# Quotient diffeologies

This file constructs the quotient diffeology of a surjective map. A map from an open subset of a
Cartesian space to the quotient is a plot precisely when it locally lifts through the quotient map
to a plot of the source. Thus the quotient map is a subduction, and a function out of the quotient
is diffeologically smooth exactly when its composite with the quotient map is smooth.

The construction is phrased using plots on open subsets. This avoids requiring a local lift to
extend to a plot on the whole Cartesian space, which is not part of the definition of a
diffeology.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Q Y : Type*} [DiffeologicalSpace X]

/-! ### Plots on open subsets -/

/-- A map defined on a subset of a Cartesian space is a plot on that subset if its composite
with every smooth map having image in the subset is a globally defined plot.

For an open subset, this is the usual local notion of a diffeological plot. -/
def IsPlotOn {n : ℕ} (u : Set (𝔼ⁿ)) (p : 𝔼ⁿ → X) : Prop :=
  ∀ {m : ℕ} (f : 𝔼ᵐ → 𝔼ⁿ), MapsTo f univ u → ContDiff ℝ ∞ f →
    _root_.Diffeology.IsPlot (p ∘ f)

/-- Globally defined plots are plots on every subset. -/
theorem isPlotOn_of_isPlot {n : ℕ} {p : 𝔼ⁿ → X}
    (hp : _root_.Diffeology.IsPlot p) (u : Set (𝔼ⁿ)) : IsPlotOn u p := by
  intro m f _ hf
  exact _root_.Diffeology.isPlot_reparam hp hf

/-- Being a plot on a subset depends only on the restriction to that subset. -/
theorem IsPlotOn.congr {n : ℕ} {u : Set (𝔼ⁿ)} {p p' : 𝔼ⁿ → X}
    (hp : IsPlotOn u p) (hpp' : EqOn p p' u) : IsPlotOn u p' := by
  intro m f hf hfdiff
  have hplot := hp f hf hfdiff
  convert hplot using 1
  ext z
  exact (hpp' (hf (mem_univ z))).symm

/-- A plot on a set remains a plot on a smaller set. -/
theorem IsPlotOn.mono {n : ℕ} {u v : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X}
    (hp : IsPlotOn u p) (hvu : v ⊆ u) : IsPlotOn v p :=
  fun f hf ↦ hp f (fun _ hz ↦ hvu (hf hz))

/-- Constant maps are plots on every subset. -/
theorem isPlotOn_const {n : ℕ} (u : Set (𝔼ⁿ)) (x : X) :
    IsPlotOn u (fun _ ↦ x) :=
  isPlotOn_of_isPlot (_root_.Diffeology.isPlot_const (n := n) (x := x)) u

/-- A plot on all of Cartesian space is a plot. -/
theorem IsPlotOn.isPlot {n : ℕ} {p : 𝔼ⁿ → X} (hp : IsPlotOn univ p) :
    _root_.Diffeology.IsPlot p := by
  simpa only [Function.comp_id] using hp id (mapsTo_univ id univ) _root_.contDiff_id

/-- Being a plot on all of Cartesian space is equivalent to being a globally defined plot. -/
@[simp]
theorem isPlotOn_univ_iff {n : ℕ} {p : 𝔼ⁿ → X} :
    IsPlotOn univ p ↔ _root_.Diffeology.IsPlot p :=
  ⟨IsPlotOn.isPlot, fun hp ↦ isPlotOn_of_isPlot hp univ⟩

/-- Plots on subsets are stable under smooth reparametrization on subsets. -/
theorem IsPlotOn.comp_contDiffOn {n m : ℕ} {u : Set (𝔼ⁿ)} {v : Set (𝔼ᵐ)}
    {p : 𝔼ⁿ → X} {f : 𝔼ᵐ → 𝔼ⁿ} (hp : IsPlotOn u p)
    (hf : ContDiffOn ℝ ∞ f v) (hfu : MapsTo f v u) : IsPlotOn v (p ∘ f) := by
  intro k g hg hgdiff
  have hfg : ContDiff ℝ ∞ (f ∘ g) := hf.comp_contDiff hgdiff fun z ↦ hg (mem_univ z)
  simpa only [Function.comp_assoc] using hp (f ∘ g) (hfu.comp hg) hfg

/-! ### Local lifts -/

/-- A map to the target locally lifts through a map on a subset if every point has an open
neighborhood in the subset on which the map agrees with the image of a source plot. -/
def LocallyLifts (q : X → Q) {n : ℕ} (u : Set (𝔼ⁿ)) (p : 𝔼ⁿ → Q) : Prop :=
  ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ v ⊆ u ∧
    ∃ lift : 𝔼ⁿ → X, IsPlotOn v lift ∧ EqOn (q ∘ lift) p v

/-- The local lifting property depends only on the restriction of the map to its domain. -/
theorem LocallyLifts.congr {n : ℕ} {q : X → Q} {u : Set (𝔼ⁿ)} {p p' : 𝔼ⁿ → Q}
    (hp : LocallyLifts q u p) (hpp' : EqOn p p' u) : LocallyLifts q u p' := by
  intro z hz
  obtain ⟨v, hv, hzv, hvu, lift, hlift, hq⟩ := hp z hz
  exact ⟨v, hv, hzv, hvu, lift, hlift, hq.trans (hpp'.mono hvu)⟩

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

/-! ### The quotient diffeology -/

/-- The quotient diffeology of a surjection. Its plots are the maps that locally lift through
the surjection to plots of the source. -/
@[instance_reducible]
def quotientDiffeology (q : X → Q) (hq : Surjective q) : DiffeologicalSpace Q :=
  DiffeologicalSpace.ofCorePlotsOn {
    isPlotOn := fun _ p ↦ LocallyLifts q _ p
    isPlotOn_congr := fun _ _ _ h ↦ ⟨fun hp ↦ hp.congr h, fun hp ↦ hp.congr h.symm⟩
    isPlot_const := fun y ↦ by
      obtain ⟨x, rfl⟩ := hq y
      intro z _
      exact ⟨univ, isOpen_univ, mem_univ z, Subset.rfl, fun _ ↦ x,
        isPlotOn_const univ x, eqOn_refl _ _⟩
    isPlotOn_reparam := by
      intro n m u v hu hv p f h hp hf
      exact LocallyLifts.comp_contDiffOn hp hv hf h
    locality := by
      intro n u hu p hp
      apply locallyLifts_of_locally hu
      intro z hz
      obtain ⟨v, hv, hzv, hpv⟩ := hp z hz
      exact ⟨v, hv, hzv, hpv⟩ }

/-- A map is a plot of the quotient diffeology exactly when it locally lifts through the
quotient map. -/
theorem isPlot_quotientDiffeology_iff (q : X → Q) (hq : Surjective q) {n : ℕ}
    {p : 𝔼ⁿ → Q} :
    @_root_.Diffeology.IsPlot Q (quotientDiffeology q hq) n p ↔ LocallyLifts q univ p :=
  Iff.rfl

/-- A smooth surjection is a subduction if every target plot locally lifts to a source plot. -/
def IsSubduction [DiffeologicalSpace Q] (q : X → Q) : Prop :=
  Surjective q ∧ _root_.Diffeology.DSmooth q ∧
    ∀ {n : ℕ} {p : 𝔼ⁿ → Q}, _root_.Diffeology.IsPlot p → LocallyLifts q univ p

/-- The quotient map is smooth for the quotient diffeology. -/
theorem dSmooth_quotientMap (q : X → Q) (hq : Surjective q) :
    @_root_.Diffeology.DSmooth X Q inferInstance (quotientDiffeology q hq) q := by
  intro n p hp
  rw [isPlot_quotientDiffeology_iff]
  intro z _
  exact ⟨univ, isOpen_univ, mem_univ z, Subset.rfl, p, isPlotOn_of_isPlot hp univ,
    eqOn_refl _ _⟩

/-- The quotient map, equipped with the quotient diffeology, is a subduction. -/
theorem isSubduction_quotientMap (q : X → Q) (hq : Surjective q) :
    @IsSubduction X Q inferInstance (quotientDiffeology q hq) q :=
  ⟨hq, dSmooth_quotientMap q hq, fun hp ↦ (isPlot_quotientDiffeology_iff q hq).mp hp⟩

/-- Descent along a subduction: a function from the target is smooth exactly when its composite
with the subduction is smooth. -/
theorem IsSubduction.dSmooth_iff [DiffeologicalSpace Q] [DiffeologicalSpace Y]
    {q : X → Q} (hq : IsSubduction q) (f : Q → Y) :
    _root_.Diffeology.DSmooth f ↔ _root_.Diffeology.DSmooth (f ∘ q) := by
  refine ⟨fun hf ↦ hf.comp hq.2.1, fun hf n p hp ↦ ?_⟩
  apply DiffeologicalSpace.locality
  intro z
  obtain ⟨v, hv, hzv, _, lift, hlift, hqplift⟩ := hq.2.2 hp z (mem_univ z)
  refine ⟨v, hv, hzv, fun {m} g hgv hg ↦ ?_⟩
  have hliftg : _root_.Diffeology.IsPlot (lift ∘ g) :=
    hlift g (fun z _ ↦ hgv z) hg
  have hplot := hf m (lift ∘ g) hliftg
  rw [show (f ∘ p) ∘ g = (f ∘ q) ∘ (lift ∘ g) by
    funext y
    exact congrArg f (hqplift (hgv y)).symm]
  exact hplot

/-- A function from a quotient diffeology is smooth exactly when its composite with the quotient
map is smooth. -/
theorem dSmooth_quotientDiffeology_iff [DiffeologicalSpace Y] (q : X → Q)
    (hq : Surjective q) (f : Q → Y) :
    @_root_.Diffeology.DSmooth Q Y (quotientDiffeology q hq) inferInstance f ↔
      _root_.Diffeology.DSmooth (f ∘ q) :=
  letI := quotientDiffeology q hq
  (isSubduction_quotientMap q hq).dSmooth_iff f

end TauCeti.Diffeology
