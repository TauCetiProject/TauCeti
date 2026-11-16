/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Diffeology.Basic

/-!
# Plots on subsets of Cartesian spaces

This file defines when a map from a Cartesian space to a diffeological space is a plot on a
subset of its domain: its composite with every smooth map into the subset is a plot. On open
subsets this is the usual local notion of a plot, and it does not require the map to extend to a
plot on the whole Cartesian space.
-/

public noncomputable section

open Function Set
open scoped ContDiff Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {X Y : Type*} [DiffeologicalSpace X]

/-- A map defined on a subset of a Cartesian space is a plot on that subset if its composite
with every smooth map having image in the subset is a globally defined plot.

For an open subset, this is the usual local notion of a diffeological plot. -/
def IsPlotOn {n : ℕ} (u : Set (𝔼ⁿ)) (p : 𝔼ⁿ → X) : Prop :=
  ∀ {m : ℕ} (f : 𝔼ᵐ → 𝔼ⁿ), MapsTo f univ u → ContDiff ℝ ∞ f →
    _root_.Diffeology.IsPlot (p ∘ f)

/-- A map is a plot on a subset exactly when its composite with every smooth map having image in
the subset is a plot. -/
theorem isPlotOn_iff {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X} :
    IsPlotOn u p ↔ ∀ {m : ℕ} (f : 𝔼ᵐ → 𝔼ⁿ), MapsTo f univ u → ContDiff ℝ ∞ f →
      _root_.Diffeology.IsPlot (p ∘ f) :=
  Iff.rfl

/-- Composing a plot on a subset with a smooth map into that subset gives a plot. -/
theorem IsPlotOn.isPlot_comp {n m : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X} {f : 𝔼ᵐ → 𝔼ⁿ}
    (hp : IsPlotOn u p) (hfu : MapsTo f univ u) (hf : ContDiff ℝ ∞ f) :
    _root_.Diffeology.IsPlot (p ∘ f) :=
  hp f hfu hf

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

/-- Plots on subsets are stable under postcomposition with smooth maps. -/
theorem IsPlotOn.dSmooth_comp [DiffeologicalSpace Y] {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X}
    {f : X → Y} (hp : IsPlotOn u p) (hf : _root_.Diffeology.DSmooth f) :
    IsPlotOn u (f ∘ p) :=
  fun g hg hgdiff ↦ (hp g hg hgdiff).dSmooth_comp hf

/-- A map that is a plot on an open neighborhood of each point of a subset is a plot on that
subset. -/
theorem isPlotOn_of_locally {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X}
    (hp : ∀ z ∈ u, ∃ v : Set (𝔼ⁿ), IsOpen v ∧ z ∈ v ∧ IsPlotOn v p) : IsPlotOn u p := by
  intro m f hfu hf
  apply DiffeologicalSpace.locality
  intro y
  obtain ⟨v, hv, hfv, hpv⟩ := hp (f y) (hfu (mem_univ y))
  exact ⟨f ⁻¹' v, hv.preimage hf.continuous, hfv, fun {k} g hgv hg ↦
    hpv (f ∘ g) (fun x _ ↦ hgv x) (hf.comp hg)⟩

/-- A plot on an open subset is continuous on that subset for the D-topology. -/
theorem IsPlotOn.continuousOn {n : ℕ} {u : Set (𝔼ⁿ)} {p : 𝔼ⁿ → X} (hp : IsPlotOn u p)
    (hu : IsOpen u) : @ContinuousOn _ _ _ _root_.Diffeology.dTopology p u := by
  let : TopologicalSpace X := _root_.Diffeology.dTopology
  refine continuousOn_of_forall_continuousAt fun z hz ↦ ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hu z hz
  -- Reparametrize a ball around `z` by all of Cartesian space, where `p` becomes a plot.
  let φ := OpenPartialHomeomorph.univBall z ε
  have htarget : φ.target = Metric.ball z ε := OpenPartialHomeomorph.univBall_target z hε
  have hφu : MapsTo φ univ u := fun y _ ↦
    hball (htarget ▸ φ.map_source (by simp [φ, OpenPartialHomeomorph.univBall_source]))
  have hzt : z ∈ φ.target := htarget ▸ Metric.mem_ball_self hε
  have hcont : Continuous (p ∘ φ) :=
    (hp.isPlot_comp hφu OpenPartialHomeomorph.contDiff_univBall).continuous
  refine (hcont.continuousAt.comp (φ.continuousAt_symm hzt)).congr ?_
  filter_upwards [φ.open_target.mem_nhds hzt] with y hy
  simp [φ.right_inv hy]

end TauCeti.Diffeology
