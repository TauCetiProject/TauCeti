/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Geometry.Diffeology.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# The diffeology of a smooth manifold

This file equips a smooth manifold, modelled on a real normed space via a model with corners `I`,
with its manifold diffeology `TauCeti.Diffeology.manifoldDiffeology I M`: a map from a Cartesian
space to `M` is a plot exactly when it is smooth in the sense of `ContMDiff`. As for Mathlib's
`NormedSpace.toDiffeology`, this is a definition rather than an instance; a diffeology on a
manifold that has these plots is recorded by the class `TauCeti.Diffeology.IsContMDiffCompatible`,
the manifold analogue of `Diffeology.IsContDiffCompatible`. Every finite-dimensional normed space
with its smooth diffeology is compatible with its manifold structure as a model space.

Plots can be tested in charts: a map is a plot exactly when it is continuous and its expression in
every chart of the maximal atlas is smooth where defined, so the diffeology does not depend on the
chosen atlas. Smooth maps between manifolds are smooth for the manifold diffeologies.

For a finite-dimensional manifold without boundary the converse holds as well, and the D-topology
of the manifold diffeology is the manifold topology. Both follow from the fact that every point
has a neighbourhood on which the inverse of a chart, reparametrised by a diffeomorphism from a
Euclidean space onto a ball, is a plot admitting a smooth section.

## Main declarations

* `TauCeti.Diffeology.manifoldDiffeology`: the diffeology whose plots are the smooth maps.
* `TauCeti.Diffeology.IsContMDiffCompatible`: a diffeology on a manifold whose plots are the
  smooth maps.
* `TauCeti.Diffeology.isPlot_iff_contDiffOn_extend`: plots are detected in arbitrary charts of
  the maximal atlas.
* `TauCeti.Diffeology.dSmooth_iff_contMDiff`: on finite-dimensional manifolds without boundary, a
  map is diffeologically smooth exactly when it is smooth.
* `TauCeti.Diffeology.IsContMDiffCompatible.dTopology_eq`: on finite-dimensional manifolds without
  boundary, the D-topology is the manifold topology.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), Chapter 4 for manifolds as diffeological spaces and Chapter 2 for
  the D-topology.
-/

public noncomputable section

open Function Set
open scoped ContDiff Manifold Topology

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-! ### The manifold diffeology -/

/-- The diffeology of a manifold: a map from a Cartesian space is a plot exactly when it is
smooth. This is a definition rather than an instance, since the model with corners `I` is not
determined by `M`. -/
@[instance_reducible]
def manifoldDiffeology : DiffeologicalSpace M :=
  .ofCorePlotsOn {
    isPlotOn := fun {n u} _ p ↦ ContMDiffOn 𝓘(ℝ, 𝔼ⁿ) I ∞ p u
    isPlotOn_congr := fun _ _ _ h ↦ contMDiffOn_congr fun z hz ↦ h hz
    isPlot := fun {n} p ↦ ContMDiff 𝓘(ℝ, 𝔼ⁿ) I ∞ p
    isPlotOn_univ := contMDiffOn_univ
    isPlot_const := fun _ ↦ contMDiff_const
    isPlotOn_reparam := fun _ _ _ h hp hf ↦
      hp.comp (contMDiffOn_iff_contDiffOn.mpr hf) h.subset_preimage
    locality := fun _ _ h ↦ contMDiffOn_of_locally_contMDiffOn fun z hz ↦
      let ⟨v, hv, hzv, hv'⟩ := h z hz
      ⟨v, hv, hzv, hv'.mono inter_subset_right⟩ }

/-- A diffeology on a manifold is compatible with the manifold structure if its plots are exactly
the smooth maps from Cartesian spaces. -/
class IsContMDiffCompatible [DiffeologicalSpace M] : Prop where
  isPlot_iff {n : ℕ} {p : 𝔼ⁿ → M} : _root_.Diffeology.IsPlot p ↔ ContMDiff 𝓘(ℝ, 𝔼ⁿ) I ∞ p

/-- The manifold diffeology is compatible with the manifold structure. -/
instance instIsContMDiffCompatibleManifoldDiffeology :
    @IsContMDiffCompatible _ _ _ _ _ I M _ _ (manifoldDiffeology I M) :=
  @IsContMDiffCompatible.mk _ _ _ _ _ I M _ _ (manifoldDiffeology I M) Iff.rfl

/-- A diffeology on a manifold is compatible with the manifold structure exactly when it is the
manifold diffeology. -/
theorem isContMDiffCompatible_iff_eq_manifoldDiffeology [d : DiffeologicalSpace M] :
    IsContMDiffCompatible I M ↔ d = manifoldDiffeology I M :=
  ⟨fun _ ↦ by ext n p; exact IsContMDiffCompatible.isPlot_iff,
    fun h ↦ h ▸ instIsContMDiffCompatibleManifoldDiffeology I M⟩

/-- The smooth diffeology of a normed space is compatible with its structure as a manifold modelled
on itself. -/
instance instIsContMDiffCompatibleSelf {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [DiffeologicalSpace X] [_root_.Diffeology.IsContDiffCompatible X] :
    IsContMDiffCompatible 𝓘(ℝ, X) X where
  isPlot_iff := _root_.Diffeology.isPlot_iff_contDiff.trans contMDiff_iff_contDiff.symm

variable {I M} [DiffeologicalSpace M] [IsContMDiffCompatible I M]

/-! ### Plots and smooth maps -/

variable (I) in
/-- On a manifold with a compatible diffeology, the plots are exactly the smooth maps. -/
theorem isPlot_iff_contMDiff {n : ℕ} {p : 𝔼ⁿ → M} :
    _root_.Diffeology.IsPlot p ↔ ContMDiff 𝓘(ℝ, 𝔼ⁿ) I ∞ p :=
  IsContMDiffCompatible.isPlot_iff

/-- A smooth map from a Cartesian space to a manifold is a plot. -/
theorem _root_.ContMDiff.isPlot {n : ℕ} {p : 𝔼ⁿ → M} (hp : ContMDiff 𝓘(ℝ, 𝔼ⁿ) I ∞ p) :
    _root_.Diffeology.IsPlot p :=
  (isPlot_iff_contMDiff I).mpr hp

variable (I) in
/-- A plot of a manifold is a smooth map. -/
theorem _root_.Diffeology.IsPlot.contMDiff {n : ℕ} {p : 𝔼ⁿ → M}
    (hp : _root_.Diffeology.IsPlot p) : ContMDiff 𝓘(ℝ, 𝔼ⁿ) I ∞ p :=
  (isPlot_iff_contMDiff I).mp hp

/-- Plots of a manifold can be tested in charts: a map is a plot exactly when it is continuous
and its expression in every chart of the maximal atlas is smooth on the preimage of the chart
domain. In particular the diffeology does not depend on the choice of atlas. -/
theorem isPlot_iff_contDiffOn_extend [IsManifold I ∞ M] {n : ℕ} {p : 𝔼ⁿ → M} :
    _root_.Diffeology.IsPlot p ↔ Continuous p ∧
      ∀ e ∈ IsManifold.maximalAtlas I ∞ M, ContDiffOn ℝ ∞ (e.extend I ∘ p) (p ⁻¹' e.source) := by
  refine ⟨fun hp ↦ ⟨(hp.contMDiff I).continuous, fun e he ↦ contMDiffOn_iff_contDiffOn.mp <|
    (e.contMDiffOn_extend he).comp (hp.contMDiff I).contMDiffOn subset_rfl⟩, ?_⟩
  rintro ⟨hc, h⟩
  refine (isPlot_iff_contMDiff I).mpr <| contMDiff_of_locally_contMDiffOn fun z ↦ ?_
  set e := chartAt H (p z)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (p z)
  refine ⟨p ⁻¹' e.source, e.open_source.preimage hc, mem_chart_source H (p z), ?_⟩
  refine ((contMDiffOn_extend_symm he).comp (contMDiffOn_iff_contDiffOn.mpr (h e he))
    fun w hw ↦ ⟨e (p w), e.map_source hw, rfl⟩).congr fun w hw ↦ ?_
  exact (e.extend_left_inv hw).symm

/-- A smooth map between manifolds is smooth for compatible diffeologies. -/
theorem _root_.ContMDiff.dSmooth {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [DiffeologicalSpace N] [IsContMDiffCompatible J N]
    {f : M → N} (hf : ContMDiff I J ∞ f) : _root_.Diffeology.DSmooth f :=
  fun _ _ hp ↦ (hf.comp (hp.contMDiff I)).isPlot

variable (I) in
include I in
/-- The D-topology of a manifold with a compatible diffeology is finer than the manifold
topology. -/
theorem IsContMDiffCompatible.dTopology_le :
    _root_.Diffeology.dTopology ≤ ‹TopologicalSpace M› := fun _ hu ↦
  _root_.Diffeology.isOpen_iff_preimages_plots.mpr fun _ _ hp ↦
    hu.preimage (hp.contMDiff I).continuous

/-! ### Finite-dimensional manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless] [FiniteDimensional ℝ E] [IsManifold I ∞ M]

variable (I) in
/-- Every point of a finite-dimensional manifold without boundary has an open neighbourhood `U`
together with a plot `p` and a map `σ` that is smooth on `U` and satisfies `p (σ y) = y` on `U`.
-/
theorem exists_isPlot_leftInvOn (x : M) :
    ∃ (n : ℕ) (p : 𝔼ⁿ → M) (σ : M → 𝔼ⁿ) (U : Set M), _root_.Diffeology.IsPlot p ∧ IsOpen U ∧
      x ∈ U ∧ ContMDiffOn I 𝓘(ℝ, 𝔼ⁿ) ∞ σ U ∧ LeftInvOn p σ U := by
  set e := extChartAt I x
  set L := toEuclidean (E := E)
  have hT : L.symm ⁻¹' e.target ∈ 𝓝 (L (e x)) := by
    refine L.symm.continuous.continuousAt.preimage_mem_nhds ?_
    rw [L.symm_apply_apply]
    exact extChartAt_target_mem_nhds x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hT
  set B := OpenPartialHomeomorph.univBall (L (e x)) r
  have hB : B.target = Metric.ball (L (e x)) r := OpenPartialHomeomorph.univBall_target _ hr
  refine ⟨Module.finrank ℝ E, e.symm ∘ L.symm ∘ B, B.symm ∘ L ∘ e,
    e.source ∩ e ⁻¹' (L ⁻¹' Metric.ball (L (e x)) r), ?_,
    isOpen_extChartAt_preimage' x (Metric.isOpen_ball.preimage L.continuous),
    ⟨mem_extChartAt_source x, Metric.mem_ball_self hr⟩, ?_, fun y hy ↦ ?_⟩
  · refine ContMDiff.isPlot <| (contMDiffOn_extChartAt_symm x).comp_contMDiff
      (contMDiff_iff_contDiff.mpr (L.symm.contDiff.comp OpenPartialHomeomorph.contDiff_univBall))
      fun z ↦ hball ?_
    rw [← hB]
    exact B.map_source (by simp [B])
  · refine (contMDiffOn_iff_contDiffOn.mpr OpenPartialHomeomorph.contDiffOn_univBall_symm).comp
      ((contMDiff_iff_contDiff.mpr L.contDiff).comp_contMDiffOn
        (contMDiffOn_extChartAt.mono ?_)) fun y hy ↦ hy.2
    rw [← extChartAt_source I]
    exact inter_subset_left
  · have hyB : L (e y) ∈ B.target := hB ▸ hy.2
    simp only [comp_apply, B.right_inv hyB, ContinuousLinearEquiv.symm_apply_apply]
    exact e.left_inv hy.1

variable (I) in
include I in
/-- On a finite-dimensional manifold without boundary, the D-topology of a compatible diffeology
is the manifold topology. -/
theorem IsContMDiffCompatible.dTopology_eq :
    _root_.Diffeology.dTopology = ‹TopologicalSpace M› := by
  refine le_antisymm (IsContMDiffCompatible.dTopology_le I) fun u hu ↦
    isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨n, p, σ, U, hp, hU, hxU, hσ, hpσ⟩ := exists_isPlot_leftInvOn I x
  refine ⟨U ∩ σ ⁻¹' (p ⁻¹' u), fun y hy ↦ hpσ hy.1 ▸ hy.2,
    hσ.continuousOn.isOpen_inter_preimage hU
      (_root_.Diffeology.isOpen_iff_preimages_plots.mp hu n p hp), hxU, ?_⟩
  rw [mem_preimage, mem_preimage, hpσ hxU]
  exact hx

variable (I) in
include I in
/-- On a finite-dimensional manifold without boundary, a compatible diffeology has the manifold
topology as its D-topology. -/
theorem IsContMDiffCompatible.isDTopologyCompatible :
    _root_.Diffeology.IsDTopologyCompatible M :=
  ⟨IsContMDiffCompatible.dTopology_eq I⟩

variable (I) in
/-- A diffeologically smooth map out of a finite-dimensional manifold without boundary into a
manifold is smooth, for compatible diffeologies. -/
theorem _root_.Diffeology.DSmooth.contMDiff {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H')
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [DiffeologicalSpace N]
    [IsContMDiffCompatible J N] {f : M → N} (hf : _root_.Diffeology.DSmooth f) :
    ContMDiff I J ∞ f := by
  refine contMDiff_of_locally_contMDiffOn fun x ↦ ?_
  obtain ⟨n, p, σ, U, hp, hU, hxU, hσ, hpσ⟩ := exists_isPlot_leftInvOn I x
  exact ⟨U, hU, hxU, (((hf n p hp).contMDiff J).comp_contMDiffOn hσ).congr fun y hy ↦
    (congrArg f (hpσ hy)).symm⟩

variable (I) in
/-- On a finite-dimensional manifold without boundary, a map into a manifold is diffeologically
smooth exactly when it is smooth, for compatible diffeologies. -/
theorem dSmooth_iff_contMDiff {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {H' : Type*} [TopologicalSpace H'] (J : ModelWithCorners ℝ E' H') {N : Type*}
    [TopologicalSpace N] [ChartedSpace H' N] [DiffeologicalSpace N] [IsContMDiffCompatible J N]
    {f : M → N} : _root_.Diffeology.DSmooth f ↔ ContMDiff I J ∞ f :=
  ⟨fun hf ↦ hf.contMDiff I J, ContMDiff.dSmooth⟩

end Boundaryless

end TauCeti.Diffeology
