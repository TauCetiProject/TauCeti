/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
public import TauCeti.Analysis.Distribution.TestFunction.DualEquiv
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Distributions on bundle tests

Let `V` be a smooth real vector bundle with fibre model `F` over a manifold `M`. Its *bundle tests*
are the compactly supported `C^n` sections of `V`. We equip them with the final locally convex
topology of the chart extensions of native test functions
(`ContMDiffSection.ChartTestData.chartTestSection`). It is defined without choosing frames; on a
boundaryless Hausdorff `σ`-compact manifold with finite-dimensional model it is the topology
`ContMDiffSection.compactlySupportedTopology` of every covering frame system
(`ContMDiffSection.topologicalSpace_compactlySupported_eq_compactlySupportedTopology`).

A **bundle distribution** with values in `G` is a continuous linear map from the bundle tests to
`G`, with the topology of uniform convergence on compact sets of tests
(`TauCeti.BundleDistribution`). This mirrors Mathlib's `Distribution Ω G n`, whose tests are
the real test functions on an open set `Ω` of a normed space.

The bundle `V` is the bundle of *tests*, so `BundleDistribution I F V n G` is dual to `V`. Taking
for `V` the bundle `E* ⊗ |Λ|` of `E*`-valued densities and `G = ℝ` or `ℂ` gives the distributional
sections of a bundle `E`; taking for `V` the density bundle gives the `G`-valued distributions
on `M`.

A bundle distribution is read in a chart through its **chart localization**: for chart data `p`
(a bundle trivialization and a smooth chart on part of its base set), composing `u` with the chart
extension of `F`-valued tests and applying `TestFunction.dualEquivDistribution` gives Mathlib's
native distribution

`ψ ↦ (v ↦ u (chart extension of ψ • v))`

with values in `F →L[ℝ] G` on the chart target (`TauCeti.BundleDistribution.chartDistribution`).
Since bundle tests are finite sums of chart extensions
(`ContMDiffSection.span_iUnion_range_chartTestSection`), a bundle distribution is determined by
its chart localizations (`TauCeti.BundleDistribution.ext_chartDistribution`).

The basic example is the **delta distribution** `s ↦ l (s x)` at a point `x`, for a continuous
linear map `l : V x →L[ℝ] G` (`TauCeti.BundleDistribution.delta`). In a chart around `x` its
localization is the native delta distribution at the image of `x`, with the coefficient
`l ∘ t⁻¹ₓ` that reads `l` in the frame `t` of the chart
(`TauCeti.BundleDistribution.chartDistribution_delta_of_mem`); in a chart missing `x` it is zero.

## Main declarations

* `ContMDiffSection.instTopologicalSpaceCompactlySupported`: the test topology on compactly
  supported sections.
* `ContMDiffSection.continuous_iff_continuous_comp_chartTestSection`: its universal property.
* `TauCeti.BundleDistribution`: distributions on bundle tests.
* `TauCeti.BundleDistribution.chartDistribution`: the chart localization, a continuous linear map
  into Mathlib's native distributions.
* `TauCeti.BundleDistribution.ext_chartDistribution`: bundle distributions are determined by their
  chart localizations.
* `TauCeti.BundleDistribution.delta`: delta distributions at points, with their chart
  localizations.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, 2nd ed., §6.3:
  distributions on manifolds through their localizations in charts.
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology ContinuousLinearMap
open scoped ContDiff Manifold Distributions CompactConvergenceCLM

namespace ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]

/-- The **test topology** on compactly supported sections: the final locally convex topology of
the chart extensions of native test functions, over all chart data. It needs no choice of frames.
On a boundaryless Hausdorff `σ`-compact manifold with finite-dimensional model it agrees with
`ContMDiffSection.compactlySupportedTopology` for every covering frame system
(`topologicalSpace_compactlySupported_eq_compactlySupportedTopology`). -/
instance instTopologicalSpaceCompactlySupported :
    TopologicalSpace (compactlySupported I F n V) :=
  TauCeti.finalLocallyConvexTopology
    (ChartTestData.chartTestSection (I := I) (F := F) (V := V) (n := n))

instance instIsTopologicalAddGroupCompactlySupported :
    IsTopologicalAddGroup (compactlySupported I F n V) :=
  inferInstanceAs (@IsTopologicalAddGroup _ (TauCeti.finalLocallyConvexTopology
    (ChartTestData.chartTestSection (I := I) (F := F) (V := V) (n := n))) _)

instance instContinuousSMulCompactlySupported :
    ContinuousSMul ℝ (compactlySupported I F n V) :=
  inferInstanceAs (@ContinuousSMul ℝ _ _ _ (TauCeti.finalLocallyConvexTopology
    (ChartTestData.chartTestSection (I := I) (F := F) (V := V) (n := n))))

instance instLocallyConvexSpaceCompactlySupported :
    LocallyConvexSpace ℝ (compactlySupported I F n V) :=
  inferInstanceAs (@LocallyConvexSpace ℝ _ _ _ _ _ (TauCeti.finalLocallyConvexTopology
    (ChartTestData.chartTestSection (I := I) (F := F) (V := V) (n := n))))

/-- The chart extension of native test functions given by chart data, as a continuous linear
map into the bundle tests. -/
def ChartTestData.chartTestSectionCLM (p : ChartTestData I F V n) :
    𝓓^{n}(⟨p.chart.target, p.chart.open_target⟩, F) →L[ℝ] compactlySupported I F n V :=
  ⟨p.chartTestSection, TauCeti.FinalLocallyConvexTopology.continuous
    (ChartTestData.chartTestSection (I := I) (F := F) (V := V) (n := n)) p⟩

@[simp]
theorem ChartTestData.coe_chartTestSectionCLM (p : ChartTestData I F V n) :
    ⇑p.chartTestSectionCLM = p.chartTestSection :=
  (rfl)

/-- **The universal property of bundle tests.** A linear map from the bundle tests into a locally
convex space is continuous exactly when its composite with the chart extension of native test
functions is continuous for all chart data. -/
theorem continuous_iff_continuous_comp_chartTestSection {G : Type*} [AddCommGroup G]
    [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G]
    [LocallyConvexSpace ℝ G] (g : compactlySupported I F n V →ₗ[ℝ] G) :
    Continuous g ↔ ∀ p : ChartTestData I F V n, Continuous (g ∘ p.chartTestSection) :=
  TauCeti.FinalLocallyConvexTopology.continuous_iff_continuous_comp _ g

section Manifold

variable [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- The test topology is the fixed-compact inductive topology
`ContMDiffSection.compactlySupportedTopology` of any covering frame system. -/
theorem topologicalSpace_compactlySupported_eq_compactlySupportedTopology {ι : Type*}
    (e : ι → Trivialization F (π F V)) [∀ i, MemTrivializationAtlas (e i)]
    (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)
    (hcover : ∀ x : M, ∃ i, x ∈ U i) :
    instTopologicalSpaceCompactlySupported = compactlySupportedTopology (I := I) (n := n) e U hU :=
  (compactlySupportedTopology_eq_finalLocallyConvexTopology_chartTestSection e U hU hcover).symm

/-- The bundle tests form a Hausdorff space. -/
instance instT2SpaceCompactlySupported : T2Space (compactlySupported I F n V) := by
  let U : M → Opens M := fun x ↦ ⟨(trivializationAt F V x).baseSet,
    (trivializationAt F V x).open_baseSet⟩
  have hcover : ∀ x : M, ∃ y, x ∈ U y := fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x⟩
  rw [topologicalSpace_compactlySupported_eq_compactlySupportedTopology
    (fun x ↦ trivializationAt F V x) U (fun _ ↦ subset_rfl) hcover]
  exact t2Space_compactlySupportedTopology _ U (fun _ ↦ subset_rfl) hcover

end Manifold

end ContMDiffSection

namespace TauCeti

open ContMDiffSection

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞} [ContMDiffVectorBundle n F V I]

variable (I F V n) in
/-- `G`-valued **bundle distributions** of order at most `n` on the test bundle `V`: continuous
real-linear maps from the compactly supported `C^n` sections of `V`, with their test topology, to
`G`, carrying the topology of uniform convergence on compact sets of tests. For the density
bundle these are the `G`-valued distributions on `M`; for the bundle of `E*`-valued densities and
`G = ℝ` they are the distributional sections of `E`. -/
abbrev BundleDistribution (G : Type*) [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] :=
  compactlySupported I F n V →L_c[ℝ] G

namespace BundleDistribution

section Localization

variable [FiniteDimensional ℝ F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

variable (G) in
/-- The **chart localization** of bundle distributions: for chart data `p`, a bundle distribution
`u` gives the native `F →L[ℝ] G`-valued distribution `ψ ↦ (v ↦ u (chart extension of ψ • v))` on
the chart target (`TestFunction.dualEquivDistribution` of `u` composed with the chart extension). -/
def chartDistribution (p : ChartTestData I F V n) :
    BundleDistribution I F V n G →L[ℝ] 𝓓'^{n}(⟨p.chart.target, p.chart.open_target⟩, F →L[ℝ] G) :=
  (TestFunction.dualEquivDistribution : _ ≃L[ℝ] 𝓓'^{n}(_, F →L[ℝ] G)).toContinuousLinearMap ∘L
    p.chartTestSectionCLM.precompCompactConvergenceCLM G

@[simp]
theorem chartDistribution_apply_apply (p : ChartTestData I F V n) (u : BundleDistribution I F V n G)
    (ψ : 𝓓^{n}(⟨p.chart.target, p.chart.open_target⟩, ℝ)) (v : F) :
    chartDistribution G p u ψ v =
      u (p.chartTestSection (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ)) :=
  TestFunction.dualEquivDistribution_apply_apply _ ψ v

section Manifold

variable [FiniteDimensional ℝ E] [I.Boundaryless] [SigmaCompactSpace M] [IsManifold I ∞ M]

/-- **Bundle distributions are determined by their chart localizations.** -/
theorem ext_chartDistribution {u u' : BundleDistribution I F V n G}
    (h : ∀ p : ChartTestData I F V n, chartDistribution G p u = chartDistribution G p u') :
    u = u' := by
  -- On the tests `u` and `u'` agree on every chart extension, and these span all bundle tests.
  refine ContinuousLinearMap.coe_injective (LinearMap.ext_on
    span_iUnion_range_chartTestSection ?_)
  rintro _ ⟨_, ⟨p, rfl⟩, φ, rfl⟩
  have hp := congrArg (TestFunction.dualEquivDistribution (n := n)
    (Ω := ⟨p.chart.target, p.chart.open_target⟩) (F := F) (V := G)).symm (h p)
  simp only [chartDistribution, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] at hp
  exact DFunLike.congr_fun hp φ

/-- Bundle distributions agree exactly when all their chart localizations agree. -/
theorem ext_chartDistribution_iff {u u' : BundleDistribution I F V n G} :
    u = u' ↔ ∀ p : ChartTestData I F V n, chartDistribution G p u = chartDistribution G p u' :=
  ⟨fun h _ ↦ h ▸ rfl, ext_chartDistribution⟩

end Manifold

end Localization

section Delta

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]

/-- The value at `x` of a chart extension of a test function, paired with `l`, is continuous in
the test function: it is the test function's value at the image of `x`, read through the frame,
when `x` lies in the chart source, and zero otherwise. -/
private theorem continuous_apply_chartTestSection (x : M) (l : V x →L[ℝ] G)
    (p : ChartTestData I F V n) :
    Continuous fun φ ↦ l ((p.chartTestSection φ : Cₛ^n⟮I; F, V⟯) x) := by
  let := p.memTrivializationAtlas
  by_cases hx : x ∈ p.chart.source
  · refine ((l ∘L p.trivialization.symmL ℝ x).continuous.comp
      (continuous_eval_const (p.chart x))).congr fun φ ↦ ?_
    simp [ChartTestData.chartTestSection_def,
      Bundle.Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hx]
  · refine (continuous_const (y := (0 : G))).congr fun φ ↦ ?_
    simp [ChartTestData.chartTestSection_def, hx]

variable [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] [LocallyConvexSpace ℝ G]

/-- The **delta distribution** `s ↦ l (s x)` at the point `x`, for a continuous linear map
`l : V x →L[ℝ] G` on the fibre. -/
def delta (x : M) (l : V x →L[ℝ] G) : BundleDistribution I F V n G :=
  ⟨l.toLinearMap ∘ₗ evalLinearMap I F n V x ∘ₗ
      (compactlySupported I F n V).subtype,
    (continuous_iff_continuous_comp_chartTestSection _).2 fun p ↦
      (continuous_apply_chartTestSection x l p).congr fun φ ↦ by simp⟩

@[simp]
theorem delta_apply (x : M) (l : V x →L[ℝ] G) (s : compactlySupported I F n V) :
    delta x l s = l ((s : Cₛ^n⟮I; F, V⟯) x) := by
  -- Evaluation through the `→L_c` type synonym is evaluation of the underlying composite of
  -- linear maps, whose middle factor is evaluation at `x`.
  change l (evalLinearMap I F n V x (s : Cₛ^n⟮I; F, V⟯)) = _
  rw [evalLinearMap_apply]

@[simp]
theorem delta_zero (x : M) : (delta x 0 : BundleDistribution I F V n G) = 0 := by
  ext s
  simp

theorem delta_add (x : M) (l l' : V x →L[ℝ] G) :
    (delta x (l + l') : BundleDistribution I F V n G) = delta x l + delta x l' := by
  ext s
  simp

theorem delta_smul (x : M) (a : ℝ) (l : V x →L[ℝ] G) :
    (delta x (a • l) : BundleDistribution I F V n G) = a • delta x l := by
  ext s
  simp

/-- The delta distribution at `x` with coefficient `l` vanishes only for `l = 0`: every vector of
the fibre over `x` is the value at `x` of a bundle test. -/
@[simp]
theorem delta_eq_zero_iff [FiniteDimensional ℝ E] [IsManifold I n M] {x : M}
    {l : V x →L[ℝ] G} : (delta x l : BundleDistribution I F V n G) = 0 ↔ l = 0 := by
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ h ▸ delta_zero x⟩
  obtain ⟨s, hsx, hs, -⟩ := exists_apply_eq_isCompact_tsupport_subset (I := I) (F := F) (n := n) x v
    Filter.univ_mem
  simpa [hsx] using DFunLike.congr_fun h ⟨s, mem_compactlySupported.2 hs⟩

end Delta

section DeltaLocalization

variable [FiniteDimensional ℝ F] {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- In a chart whose source contains `x`, the localization of the delta distribution at `x` is the
native delta distribution at the image of `x`, with the coefficient `l ∘ t⁻¹ₓ` reading `l` in the
frame `t` of the chart. -/
theorem chartDistribution_delta_of_mem (p : ChartTestData I F V n) {x : M}
    (hx : x ∈ p.chart.source) (l : V x →L[ℝ] G) :
    letI := p.memTrivializationAtlas
    chartDistribution G p (delta x l) =
      Distribution.mapCLM (toSpanSingleton ℝ (l ∘L p.trivialization.symmL ℝ x))
        (Distribution.delta (p.chart x)) := by
  let := p.memTrivializationAtlas
  ext ψ v
  simp [ChartTestData.chartTestSection_def,
    Bundle.Trivialization.chartTestSection_apply_of_mem _ _ _ _ _ hx]

/-- In a chart whose source misses `x`, the localization of the delta distribution at `x`
vanishes. -/
theorem chartDistribution_delta_of_notMem (p : ChartTestData I F V n) {x : M}
    (hx : x ∉ p.chart.source) (l : V x →L[ℝ] G) :
    chartDistribution G p (delta x l) = 0 := by
  ext ψ v
  simp [ChartTestData.chartTestSection_def, hx]

end DeltaLocalization

end BundleDistribution

end TauCeti
