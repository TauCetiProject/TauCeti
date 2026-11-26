/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
public import TauCeti.Geometry.Manifold.Measure.SmoothDensity
public import Mathlib.Geometry.Manifold.Immersion
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Conormal.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivialization
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Geometry.Manifold.Immersion.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Set

/-!
# The wave front set of a submanifold delta

Let `V → M` be a smooth real vector bundle over a smooth manifold, let `ι : N → M` be a proper
continuous map, `μ` a measure on `N` finite on compact sets, and `ℓ` a continuous family of
covectors `ℓ y` on the fibres `V (ι y)`. The functional

`δ_{ι, μ, ℓ} : s ↦ ∫ ℓ y (s (ι y)) dμ(y)`

on the bundle tests `TauCeti.BundleTest I F V` (`TauCeti.BundleTest.deltaAlong`) is a continuous
linear functional. Along the point mass at `y` it is the point mass
`TauCeti.BundleTest.delta (ι y) (ℓ y)` (`TauCeti.BundleTest.deltaAlong_dirac`). When `ι` is the
inclusion of a closed embedded submanifold `S` and `μ` a smooth positive density on `S`, it is the
**delta distribution of `S`**. Taking for
`V` the bundle `V' →L[ℝ] |Λ|` of `V'`-dual densities, whose bundle tests are the tests of the
distributional sections of `V'` (`TauCeti.BundleDistribution`), it is a distributional section of
`V'` supported on `S`, paired with the density-valued tests.

The main theorem computes its wave front set
(`TauCeti.BundleTest.waveFrontSet_deltaAlong`): if `ι` is a closed embedding and an immersion, `μ`
has a smooth positive density with respect to Lebesgue measure in every chart
(`TauCeti.HasSmoothPositiveDensity`) and `ℓ` is smooth and vanishes nowhere, then

`WF(δ_{ι, μ, ℓ}) = {(ι y, ξ) | ξ ≠ 0, ξ ∘ dι_y = 0}`,

the **conormal bundle** `TauCeti.CotangentBundle.conormal` of the submanifold `ι(N)` with its zero
section removed.

## The argument

Away from the closed set `ι(N)` the functional vanishes. Near a point `x = ι y`, Mathlib's
definition of an immersion (`Manifold.IsImmersionAt`) supplies charts `φ` of `N` at `y` and `ψ` of
`M` at `x` in which `ι` reads `u ↦ L u`, for an injective linear map `L = A ∘ (·, 0)`. In a chart
`c` of `M` agreeing with `ψ`, a test function `θ v` supported close to `c x` only sees the part of
`N` inside the source of `φ`, since `ι` is an embedding. There `μ` has a smooth positive density
`w` in the chart `φ` (`TauCeti.HasSmoothPositiveDensity`), so the component
along `v` of the local representative of `δ_{ι, μ, ℓ}` is

`θ ↦ ∫ θ (L u) w(u) ℓ (φ⁻¹ u) (t⁻¹ v) du`,

a smooth multiple `ρ` of Haar measure carried by the subspace `range L`, with `ρ (c x)` a nonzero
multiple of `ℓ y (t⁻¹ v)`. The wave front set of that measure is the conormal set of `range L`
(`Distribution.waveFrontSet_ofFun_one_map_of_injective`), and multiplying by `ρ` does not change it
where `ρ ≠ 0`. Finally `ι = c⁻¹ ∘ L ∘ φ` near `y`, so by the chain rule a covector `ξ` at `x`
annihilates the image of `dι_y` exactly when, read in the chart `c`, it is orthogonal to `range L`
(`TauCeti.comp_mfderiv_eq_zero_iff_of_eq_linearMap`).

## Main definitions

* `TauCeti.BundleTest.deltaAlong`: the functional `s ↦ ∫ ℓ y (s (ι y)) dμ(y)` on bundle tests.

## Main results

* `TauCeti.BundleTest.deltaAlong_apply`: its values.
* `TauCeti.BundleTest.deltaAlong_dirac`: along a point mass it is a point mass.
* `TauCeti.BundleTest.dsupport_deltaAlong_subset`: it is supported in the range of `ι`.
* `TauCeti.BundleTest.waveFrontSet_deltaAlong`: the wave front set of the delta distribution of a
  closed embedded submanifold with a smooth positive density is its conormal bundle.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Example 8.2.5 (the wave front set of a smooth density on a submanifold is its
  conormal bundle) and §8.2 (the wave front set on a manifold).
* J. J. Duistermaat, J. A. C. Kolk, *Distributions: Theory and Applications*, Birkhäuser, 2010,
  §16 (distributions on manifolds and densities).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace MeasureTheory Bundle
open scoped Manifold ContDiff Topology InnerProduct CompactConvergenceCLM Distributions

namespace TauCeti.BundleTest

section Functional

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {N : Type*} {ι : N → M}

/-- The pairing `y ↦ ℓ y (s (ι y))` vanishes outside the preimage under `ι` of a closed set `K`
containing the support of `s`. -/
private theorem apply_apply_eq_zero_of_notMem {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ}
    {s : BundleTest I F V} {K : Set M} (hK : closure {x | s x ≠ 0} ⊆ K) {y : N} (hy : ι y ∉ K) :
    ℓ y (s (ι y)) = 0 := by
  rw [Bundle.apply_eq_zero_of_notMem_closure fun h ↦ hy (hK h), map_zero]

variable [FiniteDimensional ℝ E] [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  [TopologicalSpace N]

/-! ### The functional -/

/-- Evaluating a bundle test at `ι y` and pairing with a covector `ℓ y` that depends continuously
on `y` in the frames is jointly continuous in the test and the point. -/
private theorem continuous_apply_apply {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ} (hι : Continuous ι)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀) :
    Continuous fun p : BundleTest I F V × N ↦ ℓ p.2 (p.1 (ι p.2)) := by
  let := ContMDiffSection.frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
    (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
  -- Evaluation of tests is jointly continuous with values in the total space.
  have hval : Continuous fun s : BundleTest I F V ↦ ((ofCompactlySupported I F V).symm s).val :=
    ContMDiffSection.continuous_val_compactlySupportedTopology (I := I) (n := ∞) _ _ _
  have hev : Continuous fun p : BundleTest I F V × N ↦ TotalSpace.mk' F (ι p.2) (p.1 (ι p.2)) :=
    (ContMDiffSection.continuous_totalSpace_eval _ _ _
      (fun x ↦ ⟨x, FiberBundle.mem_baseSet_trivializationAt' x⟩)).comp
      ((hval.comp continuous_fst).prodMk (hι.comp continuous_snd))
  refine continuous_iff_continuousAt.2 fun p₀ ↦ ?_
  set t := trivializationAt F V (ι p₀.2)
  have hbase : ∀ᶠ p : BundleTest I F V × N in 𝓝 p₀, ι p.2 ∈ t.baseSet :=
    (hι.comp continuous_snd).continuousAt.preimage_mem_nhds
      (t.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))
  -- Near `p₀` the pairing is `ℓ y ∘ t⁻¹` applied to the coordinates of the value in `t`.
  have hcoord : ContinuousAt (fun p : BundleTest I F V × N ↦
      (t (TotalSpace.mk' F (ι p.2) (p.1 (ι p.2)))).2) p₀ :=
    continuous_snd.continuousAt.comp ((t.continuousOn.continuousAt (t.open_source.mem_nhds
      (t.mem_source.2 (FiberBundle.mem_baseSet_trivializationAt' _)))).comp hev.continuousAt)
  refine ((((hℓ p₀.2).comp continuous_snd.continuousAt).clm_apply hcoord)).congr ?_
  filter_upwards [hbase] with p hp
  simp only [comp_apply, ContinuousLinearMap.coe_comp]
  rw [← t.continuousLinearMapAt_apply_of_mem (R := ℝ) hp, t.symmL_continuousLinearMapAt hp]

/-- For a fixed bundle test `s`, the pairing `y ↦ ℓ y (s (ι y))` is continuous. -/
private theorem continuous_apply_apply_right {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ} (hι : Continuous ι)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀)
    (s : BundleTest I F V) : Continuous fun y ↦ ℓ y (s (ι y)) :=
  (continuous_apply_apply hι hℓ).comp (continuous_const.prodMk continuous_id)

variable [MeasurableSpace N] [OpensMeasurableSpace N]

/-- The linear functional underlying `TauCeti.BundleTest.deltaAlong`. -/
private def deltaAlongₗ (hι : IsProperMap ι) (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (ℓ : (y : N) → V (ι y) →L[ℝ] ℝ)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀) :
    BundleTest I F V →ₗ[ℝ] ℝ where
  toFun s := ∫ y, ℓ y (s (ι y)) ∂μ
  map_add' s s' := by
    -- The pairing with a test is continuous with compact support, hence integrable.
    have h (s : BundleTest I F V) : Integrable (fun y ↦ ℓ y (s (ι y))) μ :=
      (continuous_apply_apply_right hι.continuous hℓ s).integrable_of_hasCompactSupport <|
        HasCompactSupport.intro'
          (hι.isCompact_preimage s.isCompact_tsupport) (isClosed_closure.preimage hι.continuous)
          fun y hy ↦ apply_apply_eq_zero_of_notMem subset_rfl hy
    refine (integral_congr_ae (Eventually.of_forall fun y ↦ ?_)).trans (integral_add (h s) (h s'))
    rw [add_apply, map_add]
  map_smul' a s := by
    refine (integral_congr_ae (Eventually.of_forall fun y ↦ ?_)).trans (integral_const_mul a _)
    rw [smul_apply, map_smul, smul_eq_mul]

/-- The **delta distribution along a proper map** `ι : N → M`, with a measure `μ` on `N` finite on
compact sets and a family of covectors `ℓ y` on the fibres `V (ι y)` depending continuously on `y`
in the frames: the functional `s ↦ ∫ ℓ y (s (ι y)) dμ(y)` on the bundle tests of `V`. For the
inclusion of a closed embedded submanifold and a smooth positive density `μ` it is the delta
distribution of the submanifold. -/
def deltaAlong (hι : IsProperMap ι) (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (ℓ : (y : N) → V (ι y) →L[ℝ] ℝ)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀) :
    BundleTest I F V →L_c[ℝ] ℝ where
  toLinearMap := deltaAlongₗ hι μ ℓ hℓ
  cont := by
    let := ContMDiffSection.frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    -- On the tests supported in a compact set `K`, the integrand vanishes off the compact set
    -- `ι⁻¹ K`, and it is jointly continuous in the test and the point.
    refine (continuous_iff_continuous_comp (deltaAlongₗ hι μ ℓ hℓ)).2 fun K ↦ ?_
    refine continuous_integral_of_compact_support μ (hι.isCompact_preimage K.isCompact)
      ((continuous_apply_apply hι.continuous hℓ).comp
        ((continuous_ofSupportedIn K).prodMap continuous_id)) fun s y h ↦ by_contra fun hy ↦ ?_
    refine h (apply_apply_eq_zero_of_notMem ?_ hy)
    have hs (x : M) : ((ofCompactlySupported I F V ∘ ContMDiffSection.ofSupportedIn K) s) x =
        (s : Cₛ^∞⟮I; F, V⟯) x := by
      simp
    simp_rw [hs]
    exact (ContMDiffSection.tsupport_def _).symm.subset.trans
      (ContMDiffSection.mem_supportedIn.1 s.property)

@[simp]
theorem deltaAlong_apply (hι : IsProperMap ι) (μ : Measure N) [IsFiniteMeasureOnCompacts μ]
    (ℓ : (y : N) → V (ι y) →L[ℝ] ℝ)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀)
    (s : BundleTest I F V) :
    deltaAlong (I := I) hι μ ℓ hℓ s = ∫ y, ℓ y (s (ι y)) ∂μ :=
  (rfl)

/-- Along the point mass at `y`, the delta along `ι` is the point mass `δ_{ι y} (ℓ y)`. -/
theorem deltaAlong_dirac (hι : IsProperMap ι) (y : N) (ℓ : (y : N) → V (ι y) →L[ℝ] ℝ)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀) :
    deltaAlong (I := I) hι (Measure.dirac y) ℓ hℓ = delta (ι y) (ℓ y) := by
  ext s
  rw [deltaAlong_apply, delta_apply,
    integral_dirac' _ _ (continuous_apply_apply_right hι.continuous hℓ s).stronglyMeasurable]

/-- **The support of the delta along `ι`.** The delta along a proper map `ι` is supported in the
range of `ι`, a closed set. -/
theorem dsupport_deltaAlong_subset (hι : IsProperMap ι) (μ : Measure N)
    [IsFiniteMeasureOnCompacts μ] (ℓ : (y : N) → V (ι y) →L[ℝ] ℝ)
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀) :
    dsupport (deltaAlong (I := I) hι μ ℓ hℓ) ⊆ range ι := fun x hx ↦ by
  by_contra hxι
  refine (notMem_dsupport_iff.2 ⟨(range ι)ᶜ, hι.isClosedMap.isClosed_range.isOpen_compl, hxι,
    isVanishingOn_iff.2 fun s hs ↦ ?_⟩) hx
  rw [deltaAlong_apply]
  exact integral_eq_zero_of_ae (Eventually.of_forall fun y ↦
    apply_apply_eq_zero_of_notMem hs (not_not.2 (mem_range_self y)))

end Functional

/-! ### A cutoff seen through a chart -/

section Cutoff

variable {E M N E' : Type*} [TopologicalSpace E] [TopologicalSpace M] [TopologicalSpace N]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {ι : N → M}

/-- **A cutoff and a neighbourhood seeing only the chart.** Let `ι` be an embedding with
`ι y₀` in the source of `c`, and let `O ⊆ φ.source` be an open neighbourhood of `y₀`. There are a
smooth cutoff `χ` equal to `1` at `φ y₀` and supported in `φ '' O`, and an open neighbourhood `B`
of `c (ι y₀)` in the target of `c` such that every `y` with `ι y` in the source of `c` and
`c (ι y) ∈ B` lies in `O` and has `χ (φ y) = 1`. -/
private theorem exists_cutoff_and_nhds (hι : Topology.IsEmbedding ι) {c : OpenPartialHomeomorph M E}
    {φ : OpenPartialHomeomorph N E'} {y₀ : N} (hy₀c : ι y₀ ∈ c.source) {O : Set N}
    (hO : IsOpen O) (hy₀O : y₀ ∈ O) (hOφ : O ⊆ φ.source) :
    ∃ χ : E' → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ φ '' O ∧ χ (φ y₀) = 1 ∧
      ∃ B : Opens E, B ≤ ⟨c.target, c.open_target⟩ ∧ c (ι y₀) ∈ B ∧
        ∀ y, ι y ∈ c.source → c (ι y) ∈ B → y ∈ O ∧ χ (φ y) = 1 := by
  -- A bump around `φ y₀`, equal to `1` on the ball of radius `ε / 4`.
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 (φ.isOpen_image_of_subset_source hO hOφ) (φ y₀)
    ⟨y₀, hy₀O, rfl⟩
  let b : ContDiffBump (φ y₀) := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have h₁ {u : E'} (hu : u ∈ Metric.ball (φ y₀) (ε / 4)) : b u = 1 :=
    b.one_of_mem_closedBall (Metric.ball_subset_closedBall hu)
  -- The points of `O` sent into that ball are `ι⁻¹ W` for an open set `W` of `M`.
  obtain ⟨W, hW, hWO⟩ := hι.isInducing.isOpen_iff.1
    (hO.inter (φ.isOpen_inter_preimage (Metric.isOpen_ball (x := φ y₀) (ε := ε / 4))))
  have hy₀W : y₀ ∈ ι ⁻¹' W := hWO ▸ ⟨hy₀O, hOφ hy₀O, Metric.mem_ball_self (by positivity)⟩
  refine ⟨b, b.contDiff, ?_, h₁ (Metric.mem_ball_self (by positivity)),
    ⟨c.target ∩ c.symm ⁻¹' W, c.isOpen_inter_preimage_symm hW⟩, inter_subset_left,
    ⟨c.map_source hy₀c, by rwa [mem_preimage, c.left_inv hy₀c, ← mem_preimage]⟩,
    fun y hy hyB ↦ ?_⟩
  · rw [b.tsupport_eq]
    exact (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  · have hyW : y ∈ ι ⁻¹' W := by
      have := hyB.2
      rwa [mem_preimage, c.left_inv hy] at this
    rw [hWO] at hyW
    exact ⟨hyW.1, h₁ hyW.2.2⟩

end Cutoff

/-! ### The wave front set -/

section WaveFrontSet

open InnerProductSpace
open ContinuousLinearMap (toSpanSingleton)
open scoped RealInnerProductSpace

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {E' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace N] [ChartedSpace E' N] {ι : N → M}

variable [MeasurableSpace N] [BorelSpace N] [MeasureSpace E'] [BorelSpace E']

omit [I.Boundaryless] [FiniteDimensional ℝ F] in
/-- On the source of a chart `c`, a covector `ℓ` at `x` pairs with a test function `ψ v` extended
through `c` and a frame `t` as `ψ (c x) ℓ (t⁻¹ v)`. -/
private theorem apply_chartTestCLM_postcompCLM_of_mem {t : Trivialization F (π F V)}
    [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    (ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (v : F) {x : M} (hx : x ∈ c.source)
    (ℓ : V x →L[ℝ] ℝ) :
    ℓ (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ) x) =
      ψ (c x) * ℓ (t.symmL ℝ x v) := by
  simp [t.chartTestCLM_apply_of_mem _ _ _ _ hx, map_smul]

omit [I.Boundaryless] [FiniteDimensional ℝ F] in
/-- A covector `ℓ` at `x` pairs nontrivially with a test function `ψ v` extended through a chart
`c` and a frame `t` only if `x` lies in the source of `c` and `c x` in the support of `ψ`. -/
private theorem mem_source_and_mem_tsupport_of_apply_chartTestCLM_postcompCLM_ne_zero
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    (ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (v : F) {x : M} {ℓ : V x →L[ℝ] ℝ}
    (h : ℓ (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ) x) ≠ 0) :
    x ∈ c.source ∧ c x ∈ tsupport ψ := by
  by_cases hx : x ∈ c.source
  · rw [apply_chartTestCLM_postcompCLM_of_mem hc hct ψ v hx] at h
    exact ⟨hx, subset_tsupport _ (left_ne_zero_of_mul h)⟩
  · simp [t.chartTestCLM_apply_of_notMem _ _ _ _ hx] at h

omit [I.Boundaryless] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E'] [ChartedSpace E' N]
  [MeasurableSpace N] [BorelSpace N] [MeasureSpace E'] [BorelSpace E'] in
/-- For a proper map `ι`, the pairing `y ↦ ℓ y (s (ι y))` with a test function `ψ v` extended
through a chart `c` and a frame `t` has compact support, contained in `O` when every point `y` with
`c (ι y)` in a set `B` containing the support of `ψ` lies in `O`. -/
private theorem hasCompactSupport_apply_chartTestCLM (hι : IsProperMap ι)
    {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ} {t : Trivialization F (π F V)} [MemTrivializationAtlas t]
    {c : OpenPartialHomeomorph M E} (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hct : c.source ⊆ t.baseSet) {O : Set N} {B : Set E}
    (hB : ∀ y, ι y ∈ c.source → c (ι y) ∈ B → y ∈ O)
    (ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (hψ : tsupport ψ ⊆ B) (v : F) :
    HasCompactSupport (fun y ↦
        ℓ y (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ) (ι y))) ∧
      tsupport (fun y ↦
        ℓ y (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ) (ι y))) ⊆
        O := by
  set s := t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ)
  -- The pairing vanishes off the compact set `K = ι⁻¹ (c⁻¹ (supp ψ))`, which lies in `O`.
  set K := ι ⁻¹' (c.symm '' tsupport ψ)
  have hψc : IsCompact (c.symm '' tsupport ψ) :=
    ψ.hasCompactSupport.isCompact.image_of_continuousOn (c.continuousOn_symm.mono ψ.tsupport_subset)
  have hKcl : IsClosed K := hψc.isClosed.preimage hι.continuous
  have hKO : K ⊆ O := by
    rintro y ⟨z, hz, hzy⟩
    have hzt : z ∈ c.target := ψ.tsupport_subset hz
    have hy : ι y ∈ c.source := hzy ▸ c.map_target hzt
    refine hB y hy ?_
    rw [← hzy, c.right_inv hzt]
    exact hψ hz
  have hgK (y : N) (hyK : y ∉ K) : ℓ y (s (ι y)) = 0 := by
    by_contra h
    obtain ⟨hyc, hψy⟩ := mem_source_and_mem_tsupport_of_apply_chartTestCLM_postcompCLM_ne_zero
      hc hct ψ v h
    exact hyK ⟨c (ι y), hψy, c.left_inv hyc⟩
  exact ⟨HasCompactSupport.intro' (hι.isCompact_preimage hψc) hKcl hgK,
    (closure_minimal (fun y hy ↦ by_contra fun h ↦ Function.mem_support.1 hy (hgK y h)) hKcl).trans
      hKO⟩

omit [I.Boundaryless] [FiniteDimensional ℝ F] [FiniteDimensional ℝ E'] [ChartedSpace E' N]
  [BorelSpace N] in
/-- **The delta along `ι` read in a chart.** In the setting of
`Manifold.IsImmersionAt.exists_chart_eq_linearMap`, let integrals against `μ` of continuous
compactly supported functions with support in `O ⊆ φ.source` be integrals over `φ '' O` against
`w ν`, and let `χ` be a cutoff supported in `φ '' O`. If every point `y` with `c (ι y) ∈ B` lies
in `O` and has `χ (φ y) = 1`, then pairing the delta along `ι` with a test function `ψ v`
supported in `B`, read in `c` and the frame `t`, gives
`∫ χ(u) w(u) ℓ (φ⁻¹ u) (t⁻¹ v) ψ (L u) dν(u)`. -/
private theorem integral_apply_chartTestCLM_eq (hι : IsProperMap ι) {μ : Measure N}
    {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ}
    (hℓ : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    {φ : OpenPartialHomeomorph N E'} {L : E' →L[ℝ] E} (hmaps : MapsTo ι φ.source c.source)
    (hcL : ∀ y ∈ φ.source, c (ι y) = L (φ y)) {ν : Measure E'} {O : Set N} (hO : IsOpen O)
    (hOφ : O ⊆ φ.source) {w : E' → ℝ}
    (hint : ∀ g : N → ℝ, Continuous g → HasCompactSupport g → tsupport g ⊆ O →
      ∫ y, g y ∂μ = ∫ u in φ '' O, w u * g (φ.symm u) ∂ν)
    {χ : E' → ℝ} (hχ : tsupport χ ⊆ φ '' O) {B : Set E}
    (hB : ∀ y, ι y ∈ c.source → c (ι y) ∈ B → y ∈ O ∧ χ (φ y) = 1)
    (ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (hψ : tsupport ψ ⊆ B) (v : F) :
    ∫ y, ℓ y (t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ) (ι y)) ∂μ =
      ∫ u, χ u * (w u * ℓ (φ.symm u) (t.symmL ℝ (ι (φ.symm u)) v)) * ψ (L u) ∂ν := by
  set s := t.chartTestCLM c hc hct (TestFunction.postcompCLM (toSpanSingleton ℝ v) ψ)
  have hsupp (y : N) (hy : ℓ y (s (ι y)) ≠ 0) : y ∈ O ∧ χ (φ y) = 1 := by
    obtain ⟨hyc, hψy⟩ := mem_source_and_mem_tsupport_of_apply_chartTestCLM_postcompCLM_ne_zero
      hc hct ψ v hy
    exact hB y hyc (hψ hψy)
  obtain ⟨hgcs, hgO⟩ := hasCompactSupport_apply_chartTestCLM (ℓ := ℓ) hι hc hct
    (fun y hy hyB ↦ (hB y hy hyB).1) ψ hψ v
  rw [hint (fun y ↦ ℓ y (s (ι y))) (continuous_apply_apply_right hι.continuous hℓ s) hgcs hgO]
  refine (setIntegral_congr_fun ((φ.isOpen_image_of_subset_source hO hOφ).measurableSet) ?_).trans
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu ↦ ?_)
  swap
  · rw [image_eq_zero_of_notMem_tsupport fun h ↦ hu (hχ h), zero_mul, zero_mul]
  rintro u ⟨y, hyO, rfl⟩
  have hy := hOφ hyO
  beta_reduce
  rw [φ.left_inv hy]
  rw [show χ (φ y) * (w (φ y) * ℓ y (t.symmL ℝ (ι y) v)) * ψ (L (φ y)) =
    χ (φ y) * (w (φ y) * ℓ y (s (ι y))) by
      rw [show ℓ y (s (ι y)) = _ from
        apply_chartTestCLM_postcompCLM_of_mem hc hct ψ v (hmaps hy) (ℓ y), hcL y hy]
      ring]
  by_cases h : ℓ y (s (ι y)) = 0
  · simp [h]
  · rw [(hsupp y h).2, one_mul]

section LocalModel

variable [MeasurableSpace E] [BorelSpace E] [(volume : Measure E').IsAddHaarMeasure]

omit [I.Boundaryless] in
/-- **The local model of the delta along an immersion.** In the charts of
`Manifold.IsImmersionAt.exists_chart_eq_linearMap`, near `c (ι y₀)` every component of the local
representative of the delta along `ι` is a smooth multiple `ρ` of the pushforward along `L` of the
Lebesgue measure `volume` of `E'`, with `ρ (c (ι y₀))` vanishing exactly when `ℓ y₀ (t⁻¹ v)`
does. -/
private theorem exists_restrictCLM_chartComponent_deltaAlong_eq
    (hι : Topology.IsClosedEmbedding ι)
    {μ : Measure N} [IsFiniteMeasureOnCompacts μ] (hμ : HasSmoothPositiveDensity E' μ)
    {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ}
    (hℓ : ∀ y₀, ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, F →L[ℝ] ℝ) ∞
      (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y))
      (ι ⁻¹' (trivializationAt F V (ι y₀)).baseSet))
    {y₀ : N} {c : OpenPartialHomeomorph M E} (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hct : c.source ⊆ (trivializationAt F V (ι y₀)).baseSet) {φ : OpenPartialHomeomorph N E'}
    {L : E' →L[ℝ] E} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E') ∞ N) (hy₀ : y₀ ∈ φ.source)
    (hL : Injective L) (hmaps : MapsTo ι φ.source c.source)
    (hcL : ∀ y ∈ φ.source, c (ι y) = L (φ y)) (v : F) :
    ∃ (B : Opens E) (_ : B ≤ ⟨c.target, c.open_target⟩) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ),
      c (ι y₀) ∈ B ∧
      (ρ (c (ι y₀)) = 0 ↔ ℓ y₀ ((trivializationAt F V (ι y₀)).symmL ℝ (ι y₀) v) = 0) ∧
      (Distribution.restrictCLM ((trivializationAt F V (ι y₀)).chartComponent c hc hct
        (deltaAlong hι.isProperMap μ ℓ (continuousAt_comp_symmL_of_contMDiffOn hι.continuous hℓ))
        v) : 𝓓'(B, ℂ)) =
        Distribution.restrictCLM (Distribution.smulLeftCLM hρ
          (Distribution.ofFun ⟨c.target, c.open_target⟩ (1 : E → ℂ)
            ((volume : Measure E').map L) ⊤)) := by
  set ν : Measure E' := volume
  -- In the chart `φ`, `μ` is `w(u) du` for a smooth positive `w`.
  obtain ⟨w, hw, hwpos, hint⟩ := hμ.exists_integral_real_eq hφ
  -- The weight `u ↦ ℓ (φ⁻¹ u) (t⁻¹ v)` is smooth on the chart target.
  have ha : ContDiffOn ℝ ∞
      (fun u ↦ ℓ (φ.symm u) ((trivializationAt F V (ι y₀)).symmL ℝ (ι (φ.symm u)) v)) φ.target :=
    (contMDiffOn_iff_contDiffOn.1 ((hℓ y₀).comp (contMDiffOn_symm_of_mem_maximalAtlas hφ)
      fun u hu ↦ hct (hmaps (φ.map_target hu)))).clm_apply contDiffOn_const
  rw [← φ.image_source_eq_target] at hw hwpos hint ha
  obtain ⟨χ, hχ, hχU, hχ₀, B, hBc, hB, hBO⟩ :=
    exists_cutoff_and_nhds hι.isEmbedding (hmaps hy₀) φ.open_source hy₀ subset_rfl
  have hH : ContDiff ℝ ∞ fun u ↦
      χ u • (w u * ℓ (φ.symm u) ((trivializationAt F V (ι y₀)).symmL ℝ (ι (φ.symm u)) v)) :=
    (hw.mul ha).contDiff_smul_of_tsupport_subset
      (φ.isOpen_image_of_subset_source φ.open_source subset_rfl) hχ.contDiffOn hχU
  -- A left inverse `P` of `L` carries the weight to `E`.
  obtain ⟨P, hP⟩ := (L : E' →ₗ[ℝ] E).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hL)
  have hPL (u : E') : P (L u) = u := congr($hP u)
  have hPc : ContDiff ℝ ∞ P := (LinearMap.toContinuousLinearMap P).contDiff
  refine ⟨B, hBc, _, hH.comp hPc, hB, ?_, ?_⟩
  · rw [hcL y₀ hy₀, comp_apply, hPL, hχ₀, one_smul, φ.left_inv hy₀]
    exact ⟨fun h ↦ (mul_eq_zero.1 h).resolve_left (hwpos _ ⟨y₀, hy₀, rfl⟩).ne',
      fun h ↦ by rw [h, mul_zero]⟩
  · have hLc := (L : E' →ₗ[ℝ] E).isClosedEmbedding_of_injective (LinearMap.ker_eq_bot.2 hL)
    have := Measure.isFiniteMeasureOnCompacts_map_of_isProperMap ν hLc.isProperMap
    ext ψ
    -- Both sides pair with the test function `ψ` extended by zero to the chart target.
    have hψ : tsupport (TestFunction.monoCLM ℝ ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) ⊆ B := by
      rw [TestFunction.coe_monoCLM_of_le le_rfl hBc]
      exact ψ.tsupport_subset
    -- Read in the chart, the delta pairs with `ψ v` as an integral against `ν`.
    have hpair := integral_apply_chartTestCLM_eq hι.isProperMap
      (continuousAt_comp_symmL_of_contMDiffOn hι.continuous hℓ) hc hct hmaps hcL φ.open_source
      subset_rfl hint hχU hBO _ hψ v
    simp only [Distribution.restrictCLM_apply, Bundle.Trivialization.chartComponent_apply,
      deltaAlong_apply, Distribution.smulLeftCLM_apply]
    rw [hpair,
      Distribution.ofFun_apply (f := 1) ((locallyIntegrable_const 1).locallyIntegrableOn _)]
    simp only [Pi.one_apply]
    rw [integral_map L.continuous.aemeasurable (Continuous.aestronglyMeasurable ?_),
      ← integral_complex_ofReal]
    · refine integral_congr_ae (Eventually.of_forall fun u ↦ ?_)
      simp only [TestFunction.smulLeftCLM_apply, comp_apply]
      rw [hPL]
      simp only [smul_eq_mul, Complex.real_smul, mul_one]
    · have := TestFunction.continuous
        (TestFunction.smulLeftCLM (hH.comp hPc) (TestFunction.monoCLM ℝ ψ :
          𝓓(⟨c.target, c.open_target⟩, ℝ)))
      fun_prop

omit [I.Boundaryless] in
/-- **Microlocal smoothness of the components.** In the charts of
`Manifold.IsImmersionAt.exists_chart_eq_linearMap`, the component along `v` of the local
representative of the delta along `ι` is microlocally smooth at `c (ι y₀)` in every direction `ξ`
not orthogonal to the range of `L`, and it is not microlocally smooth in the nonzero directions
orthogonal to it when `ℓ y₀ (t⁻¹ v) ≠ 0`. -/
private theorem isMicrolocallySmoothAt_chartComponent_deltaAlong
    (hι : Topology.IsClosedEmbedding ι)
    {μ : Measure N} [IsFiniteMeasureOnCompacts μ] (hμ : HasSmoothPositiveDensity E' μ)
    {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ}
    (hℓ : ∀ y₀, ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, F →L[ℝ] ℝ) ∞
      (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y))
      (ι ⁻¹' (trivializationAt F V (ι y₀)).baseSet))
    {y₀ : N} {c : OpenPartialHomeomorph M E} (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hct : c.source ⊆ (trivializationAt F V (ι y₀)).baseSet) {φ : OpenPartialHomeomorph N E'}
    {L : E' →L[ℝ] E} (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E') ∞ N) (hy₀ : y₀ ∈ φ.source)
    (hL : Injective L) (hmaps : MapsTo ι φ.source c.source)
    (hcL : ∀ y ∈ φ.source, c (ι y) = L (φ y)) (v : F) (ξ : E) :
    ((∃ u, ⟪ξ, L u⟫ ≠ 0) → ((trivializationAt F V (ι y₀)).chartComponent c hc hct
        (deltaAlong hι.isProperMap μ ℓ (continuousAt_comp_symmL_of_contMDiffOn hι.continuous hℓ))
        v).IsMicrolocallySmoothAt (c (ι y₀)) ξ) ∧
      (ℓ y₀ ((trivializationAt F V (ι y₀)).symmL ℝ (ι y₀) v) ≠ 0 → ξ ≠ 0 →
        (∀ u, ⟪ξ, L u⟫ = 0) → ¬ ((trivializationAt F V (ι y₀)).chartComponent c hc hct
          (deltaAlong hι.isProperMap μ ℓ (continuousAt_comp_symmL_of_contMDiffOn hι.continuous hℓ))
          v).IsMicrolocallySmoothAt (c (ι y₀)) ξ) := by
  obtain ⟨B, hB, ρ, hρ, hxB, hρ₀, heq⟩ := exists_restrictCLM_chartComponent_deltaAlong_eq hι hμ
    hℓ hc hct hφ hy₀ hL hmaps hcL v
  rw [← Distribution.isMicrolocallySmoothAt_restrictCLM_iff hB hxB, heq,
    Distribution.isMicrolocallySmoothAt_restrictCLM_iff hB hxB]
  -- The wave front set of the measure carried by `range L` is the conormal set of `range L`.
  have hS := Distribution.waveFrontSet_ofFun_one_map_of_injective (volume : Measure E') hL
    ⟨c.target, c.open_target⟩
  refine ⟨fun ⟨u, hu⟩ ↦ Distribution.IsMicrolocallySmoothAt.smulLeftCLM (by_contra fun hns ↦ ?_)
    hρ, fun hv hξ h ↦ ?_⟩
  · have hmem : (c (ι y₀), ξ) ∈ _ := Distribution.mem_waveFrontSet_iff.2
      ⟨c.map_source (hmaps hy₀), fun h0 ↦ hu (by rw [h0, inner_zero_left]), hns⟩
    rw [hS] at hmem
    exact hu (hmem.2.2.2 u)
  · rw [Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff hρ (mt hρ₀.1 hv)]
    have hmem : (c (ι y₀), ξ) ∈ (Distribution.ofFun ⟨c.target, c.open_target⟩ (1 : E → ℂ)
        ((volume : Measure E').map L) ⊤).waveFrontSet := by
      rw [hS]
      exact ⟨c.map_source (hmaps hy₀), ⟨φ y₀, (hcL y₀ hy₀).symm⟩, hξ, h⟩
    exact (Distribution.mem_waveFrontSet_iff.1 hmem).2.2

end LocalModel

/-- Away from the closed set `ι(N)`, the delta along `ι` is microlocally smooth in every
direction: it vanishes near every point outside `ι(N)`. -/
private theorem isMicrolocallySmoothAt_deltaAlong_of_notMem (hι : Topology.IsClosedEmbedding ι)
    {μ : Measure N} [IsFiniteMeasureOnCompacts μ] {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ}
    (hℓc : ∀ y₀, ContinuousAt (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y)) y₀)
    {x : M} (hx : x ∉ range ι) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt (deltaAlong hι.isProperMap μ ℓ hℓc) x ξ := by
  obtain ⟨c, hc, hcs, hct, hxc⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine (isMicrolocallySmoothAt_iff _ hc hcs hct hxc ξ).2 fun v ↦ ?_
  -- The component vanishes on the image under `c` of the complement of `ι(N)` in `c.source`.
  set B : Opens E := ⟨c.target ∩ c.symm ⁻¹' (range ι)ᶜ,
    c.isOpen_inter_preimage_symm hι.isClosed_range.isOpen_compl⟩
  have hxB : c x ∈ B := ⟨c.map_source hxc, by rwa [mem_preimage, c.left_inv hxc]⟩
  have hB : B ≤ ⟨c.target, c.open_target⟩ := inter_subset_left
  rw [← Distribution.isMicrolocallySmoothAt_restrictCLM_iff (Ω' := B) hB hxB]
  convert Distribution.isMicrolocallySmoothAt_zero hxB _
  ext ψ
  rw [Distribution.restrictCLM_apply, Bundle.Trivialization.chartComponent_apply,
    deltaAlong_apply, _root_.zero_apply, Complex.ofReal_eq_zero]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y ↦ ?_)
  beta_reduce
  by_cases hy : ι y ∈ c.source
  · rw [Bundle.Trivialization.chartTestCLM_apply_of_mem _ _ _ _ _ hy]
    have : (TestFunction.monoCLM ℝ ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (c (ι y)) = 0 := by
      rw [TestFunction.coe_monoCLM_of_le le_rfl hB]
      refine ψ.zero_on_compl fun h ↦ h.2 ?_
      rw [c.left_inv hy]
      exact mem_range_self y
    simp only [TestFunction.postcompCLM_apply, comp_apply, this, map_zero, Pi.zero_apply]
  · rw [Bundle.Trivialization.chartTestCLM_apply_of_notMem _ _ _ _ _ hy, map_zero, Pi.zero_apply]

/-- **The wave front set of a submanifold delta.** Let `ι : N → M` be a closed embedding and an
immersion of a smooth manifold `N` modelled on `E'`, let `μ` be a measure on `N` with a smooth
positive density with respect to Lebesgue measure in every chart, and let `ℓ y` be covectors on
the fibres `V (ι y)` that are smooth in `y` in the frames and vanish nowhere (hence continuous in
the frames, as the definition of the delta needs:
`TauCeti.continuousAt_comp_symmL_of_contMDiffOn`). The delta distribution
`s ↦ ∫ ℓ y (s (ι y)) dμ(y)` of the submanifold `ι(N)` has wave front set the conormal bundle of
`ι(N)` (`TauCeti.CotangentBundle.conormal`) without its zero section: the nonzero covectors `ξ` at
points `ι y` with `ξ ∘ dι_y = 0`. -/
theorem waveFrontSet_deltaAlong (hι : Topology.IsClosedEmbedding ι)
    (hιi : ∀ y, Manifold.IsImmersionAt 𝓘(ℝ, E') I ∞ ι y) {μ : Measure N}
    [IsFiniteMeasureOnCompacts μ] [(volume : Measure E').IsAddHaarMeasure]
    (hμ : HasSmoothPositiveDensity E' μ) {ℓ : (y : N) → V (ι y) →L[ℝ] ℝ}
    (hℓ : ∀ y₀, ContMDiffOn 𝓘(ℝ, E') 𝓘(ℝ, F →L[ℝ] ℝ) ∞
      (fun y ↦ ℓ y ∘L (trivializationAt F V (ι y₀)).symmL ℝ (ι y))
      (ι ⁻¹' (trivializationAt F V (ι y₀)).baseSet))
    (hℓ₀ : ∀ y, ℓ y ≠ 0) :
    waveFrontSet I
        (deltaAlong hι.isProperMap μ ℓ (continuousAt_comp_symmL_of_contMDiffOn hι.continuous hℓ)) =
      {p | p ∈ CotangentBundle.conormal 𝓘(ℝ, E') I ι ∧ p.snd ≠ 0} := by
  borelize E
  ext ⟨x, ξ⟩
  simp only [mem_waveFrontSet_iff, mem_ofPred_eq, CotangentBundle.mem_conormal_iff]
  by_cases hx : x ∈ range ι
  swap
  · exact ⟨fun h ↦ (h.2 (isMicrolocallySmoothAt_deltaAlong_of_notMem hι _ hx ξ)).elim,
      fun ⟨⟨y, hy, _⟩, _⟩ ↦ (hx ⟨y, hy⟩).elim⟩
  obtain ⟨y₀, rfl⟩ := hx
  obtain ⟨c, hc, hcs, hct, φ, L, hy₀c, hφ, hy₀, hL, hmaps, hcL⟩ :=
    (hιi y₀).exists_chart_eq_linearMap hι.continuous (trivializationAt F V (ι y₀)).open_baseSet
      (FiberBundle.mem_baseSet_trivializationAt' _)
  rw [isMicrolocallySmoothAt_iff _ hc hcs hct hy₀c]
  set ξc := (InnerProductSpace.toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c (ι y₀)))
  have hξc : ξc = 0 ↔ ξ = 0 :=
    OpenPartialHomeomorph.MDifferentiable.toDual_symm_comp_mfderiv_symm_eq_zero_iff
      ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hy₀c
  -- By the chain rule, `ξ` is conormal exactly when `ξc` is orthogonal to the range of `L`.
  have hconormal : ξ ∘L mfderiv 𝓘(ℝ, E') I ι y₀ = 0 ↔ ∀ u, ⟪ξc, L u⟫ = 0 := by
    rw [comp_mfderiv_eq_zero_iff_of_eq_linearMap
      ((hιi y₀).contMDiffAt.mdifferentiableAt (by simp))
      ((hcs.contMDiffAt (c.open_target.mem_nhds (c.map_source hy₀c))).mdifferentiableAt (by simp))
      ((contMDiffAt_of_mem_maximalAtlas hφ hy₀).mdifferentiableAt (by simp))
      ((contMDiffAt_symm_of_mem_maximalAtlas hφ (φ.map_source hy₀)).mdifferentiableAt (by simp))
      hy₀ hmaps hcL ξ]
    refine forall_congr' fun u ↦ ?_
    rw [toDual_symm_apply]
    exact (congrArg (· = 0) (ContinuousLinearMap.comp_apply _ _ _)).to_iff.symm
  have hcomp := isMicrolocallySmoothAt_chartComponent_deltaAlong hι hμ hℓ hc hct hφ hy₀ hL
    hmaps hcL (ξ := ξc)
  constructor
  · rintro ⟨hξ, hns⟩
    exact ⟨⟨y₀, rfl, hconormal.2 fun u ↦ by_contra fun hu ↦ hns fun v ↦ (hcomp v).1 ⟨u, hu⟩⟩, hξ⟩
  · rintro ⟨⟨y, hy, hcon⟩, hξ⟩
    obtain rfl := hι.injective hy
    refine ⟨hξ, fun hall ↦ ?_⟩
    -- A vector `v` on which `ℓ y₀ ∘ t⁻¹` does not vanish detects the singularity.
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 (hℓ₀ y)
    have hbase := hct hy₀c
    refine (hcomp ((trivializationAt F V (ι y)).continuousLinearMapAt ℝ (ι y) w)).2 ?_
      (mt hξc.1 hξ) (hconormal.1 hcon) (hall _)
    rwa [(trivializationAt F V (ι y)).symmL_continuousLinearMapAt hbase]

end WaveFrontSet

end TauCeti.BundleTest
