/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
public import TauCeti.Geometry.Manifold.DifferentialOperator.ChartCompression.Section
public import TauCeti.Geometry.Manifold.DifferentialOperator.Section
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalOperator
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalSobolev
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SobolevWaveFrontSet
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.DifferentialOperator
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.LinearAlgebra.Basis.Basic

/-!
# Differential operators on bundles and wave front sets

Let `E` be a finite-dimensional real inner product space. On a manifold `M` modelled on `E`, a
differential operator `P : Γ(V) → Γ(W)` between smooth sections of finite-rank vector bundles acts
on bundle tests (`TauCeti.BundleTest.localOperatorCLM`), and its transpose `T ↦ T ∘ P`
(`TauCeti.BundleTest.localOperatorDualCLM`) acts on functionals on bundle tests, for instance on
distributional sections of a bundle. This file proves that the transpose does not enlarge wave
front sets (Hörmander I, §8.1 and §8.2): if `T` is microlocally smooth at a covector, so is `T ∘ P`
(`TauCeti.BundleTest.IsMicrolocallySmoothAt.localOperatorDualCLM`), hence
`WF(T ∘ P) ⊆ WF(T)` (`TauCeti.BundleTest.waveFrontSet_localOperatorDualCLM_subset`) and the
singular support of `T ∘ P` lies in that of `T`
(`TauCeti.BundleTest.singularSupport_localOperatorDualCLM_subset`). This is the case of
differential operators of the microlocality of properly supported pseudodifferential operators on
bundles.

Conversely, when `W` has rank one, `T` is as regular as `T ∘ P` at the covectors where `P` is
elliptic: if the principal symbol `σ(P)(ξ) : V_x → W_x` (`TauCeti.sectionPrincipalSymbol`) does
not vanish and `T ∘ P` is microlocally smooth at `ξ`, then so is `T`
(`TauCeti.BundleTest.IsMicrolocallySmoothAt.of_localOperatorDualCLM`), and
`WF(T) ⊆ WF(T ∘ P) ∪ Char(P)`
(`TauCeti.BundleTest.waveFrontSet_subset_waveFrontSet_localOperatorDualCLM_union`). This covers
scalar operators, acting on the sections of the trivial line bundle. For a bundle `W` of higher
rank the same statement for systems needs the matrix-valued form of the Euclidean theorem.

A differential operator of order at most `r` costs at most `r` orders of Sobolev regularity: if `T`
is microlocally `H^s` at a covector, then `T ∘ P` is microlocally `H^(s - r)` there
(`TauCeti.BundleTest.IsMicrolocallySobolevAt.localOperatorDualCLM`), so that
`WF_(s - r)(T ∘ P) ⊆ WF_s(T)`
(`TauCeti.BundleTest.sobolevWaveFrontSet_localOperatorDualCLM_subset`), and if `T` is `H^s` near a
point, then `T ∘ P` is `H^(s - r)` near it
(`TauCeti.BundleTest.IsLocallySobolevAt.localOperatorDualCLM`), so that the `H^(s - r)` singular
support of `T ∘ P` lies in the `H^s` singular support of `T`
(`TauCeti.BundleTest.sobolevSingularSupport_localOperatorDualCLM_subset`).

## The argument

Fix a chart `c` of the maximal atlas at `x` over which both bundles are trivial, frames `tV`, `tW`
of `V` and `W` over its source, and a cutoff `χ` equal to `1` on a neighbourhood `B` of `c x`. For a
test function `φ` supported in `B` and a vector `v` of the model fibre of `V`, `P` sends the test
`φ • v`, extended through the chart and the frame `tV`, to the extension through `tW` of the test
function whose coefficient along a basis vector `bᵢ` of the model fibre of `W` is `Dᵢ φ`, for the
`(bᵢ*, v)` entry `Dᵢ` of the chart compression of `P` by `χ` and `χ`
(`OpenPartialHomeomorph.sectionChartCompression`,
`TauCeti.BundleTest.localOperatorCLM_chartTestCLM`). So over `B`, the component of `T ∘ P` along
`v` is `∑ᵢ (φ ↦ Sᵢ (Dᵢ φ))`, where `Sᵢ` is the component of `T` along `bᵢ`. Each `Dᵢ` is a
differential operator on `C^∞(E)`
(`OpenPartialHomeomorph.sectionChartCompression_mem_differentialOperators`), so the Euclidean
statements
`Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators` and
`Distribution.exists_forall_apply_eq_and_isMicrolocallySobolevAt_of_mem_differentialOperators`
apply to every term (`TauCeti.BundleTest.chartComponent_localOperatorDualCLM_apply`).

When the model fibre of `W` is a line with basis `b₀`, the sum has one term: over `B` the component
of `T ∘ P` along `v` is `φ ↦ S (D φ)` for the component `S` of `T` along `b₀`
(`TauCeti.BundleTest.restrictCLM_chartComponent_localOperatorDualCLM_apply`). The principal symbol
of `D` at `c x` is the `b₀` coordinate of `σ(P)(ξ)` applied to the vector of `V_x` with coefficients
`v` (`OpenPartialHomeomorph.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators`),
nonzero for a suitable `v` when `σ(P)(ξ) ≠ 0`. So the Euclidean elliptic regularity
`Distribution.IsMicrolocallySmoothAt.of_mem_differentialOperators` applies to `S`.

## Main results

* `TauCeti.BundleTest.localOperatorCLM_chartTestCLM`: a local operator between bundles in a chart,
  in terms of the entries of its chart compression.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.localOperatorDualCLM`: the transpose of a
  differential operator between bundles preserves microlocal smoothness.
* `TauCeti.BundleTest.waveFrontSet_localOperatorDualCLM_subset`,
  `TauCeti.BundleTest.singularSupport_localOperatorDualCLM_subset`: it does not enlarge wave front
  sets or singular supports.
* `TauCeti.BundleTest.chartComponent_localOperatorDualCLM_apply`: the components of the transpose
  in a chart, in terms of the entries of the chart compression.
* `TauCeti.BundleTest.restrictCLM_chartComponent_localOperatorDualCLM_apply`: for a bundle `W` of
  rank one, near a point of a chart, the component of the transpose is the transpose of a component
  by one entry of the chart compression.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.of_localOperatorDualCLM`,
  `TauCeti.BundleTest.waveFrontSet_subset_waveFrontSet_localOperatorDualCLM_union`: microlocal
  elliptic regularity for differential operators into a bundle of rank one.
* `TauCeti.BundleTest.IsMicrolocallySobolevAt.localOperatorDualCLM`,
  `TauCeti.BundleTest.sobolevWaveFrontSet_localOperatorDualCLM_subset`: a differential operator of
  order at most `r` costs at most `r` orders of microlocal Sobolev regularity.
* `TauCeti.BundleTest.IsLocallySobolevAt.localOperatorDualCLM`,
  `TauCeti.BundleTest.sobolevSingularSupport_localOperatorDualCLM_subset`: it costs at most `r`
  orders of local Sobolev regularity.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (differential operators with smooth coefficients do not enlarge wave front
  sets), Theorem 8.3.1 (microlocal elliptic regularity) and §8.2 (wave front sets on manifolds and
  bundles).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997,
  §11.1 (the `H^s` wave front set and its behaviour under differential operators).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7.
-/

public section

noncomputable section

open Set Function TopologicalSpace LineDeriv
open scoped ContDiff Manifold Distributions Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization Filter InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M]
  [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F'] [FiniteDimensional ℝ F']
  {W : M → Type*} [TopologicalSpace (TotalSpace F' W)]
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [FiberBundle F' W] [VectorBundle ℝ F' W] [ContMDiffVectorBundle ∞ F' W 𝓘(ℝ, E)]
  {P : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯ →ₗ[ℝ] Cₛ^∞⟮𝓘(ℝ, E); F', W⟯}

/-- **A local operator in a chart.** Let `c` be a chart of the maximal atlas, with frames `tV` and
`tW` over its source, `v` a vector of the model fibre of `V` and `φ` a test function on the chart
target. If a cutoff `χ` equals `1` on the support of `φ`, then `P` sends the extension of `φ • v`
through the chart and the frame `tV` to the extension through `tW` of the test function whose
coefficient along `b i` is the `(b i)*, v` entry of the chart compression of `P` by `χ` and `χ`,
applied to `φ`. -/
theorem localOperatorCLM_chartTestCLM
    (hP : ∀ (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {χ φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport φ, χ y = 1)
    {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : ⇑f = φ) (v : F) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F') (ψ : ι → 𝓓(⟨c.target, c.open_target⟩, ℝ))
    (hψ : ∀ i, ⇑(ψ i) = c.sectionChartCompression he tV hV tW hW χ χ
      (LinearMap.toContinuousLinearMap (b.coord i)) v P f) :
    localOperatorCLM P hP (tV.chartTestCLM c (contMDiffOn_of_mem_maximalAtlas he) hV
        (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ)) =
      ∑ i, tW.chartTestCLM c (contMDiffOn_of_mem_maximalAtlas he) hW
        (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (b i)) (ψ i)) := by
  have hc := contMDiffOn_of_mem_maximalAtlas he
  let φv := TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ v) φ
  -- The section of `V` extending `φ • v`.
  let σ := ((ofCompactlySupported 𝓘(ℝ, E) F V).symm (tV.chartTestCLM c hc hV φv)).val
  have hσ : σ = (tV.chartTestSection (n := ⊤) c hc hV φv).val :=
    ContMDiffSection.ext fun y ↦ congr_fun (tV.coe_chartTestCLM c hc hV φv) y
  have hφv : tsupport φv ⊆ tsupport φ := by
    rw [show ⇑φv = ContinuousLinearMap.toSpanSingleton ℝ v ∘ ⇑φ from
      TestFunction.postcompCLM_apply _ _]
    exact tsupport_comp_subset (map_zero _) φ
  -- Cut off by `χ`, which is `1` on the support of `φ`, it is still `σ`.
  have hpull : c.sectionCutoffPullback he tV hV χ v f = σ := by
    ext y
    rw [hσ]
    by_cases hy : y ∈ c.source
    · rw [c.sectionCutoffPullback_apply_of_mem he tV hV _ _ _ hy,
        tV.chartTestSection_apply_of_mem c hc hV _ hy]
      congr 1
      by_cases h0 : φ (c y) = 0
      · simp [φv, hf, h0]
      · simp [φv, hf, hχ _ (subset_tsupport _ h0)]
    · rw [c.sectionCutoffPullback_apply_of_notMem he tV hV _ _ _ hy,
        tV.chartTestSection_apply_of_notMem c hc hV _ hy]
  have hsupp : (P σ).tsupport ⊆ c.symm '' tsupport φ :=
    (tsupport_apply_subset_of_local hP σ).trans <| by
      rw [hσ, tV.tsupport_chartTestSection c hc hV]
      exact image_mono hφv
  ext x
  rw [localOperatorCLM_apply, BundleTest.sum_apply]
  by_cases hx : x ∈ c.source
  · -- The left side is `P σ x` with the `let`-bound section `σ` unfolded; `change` folds it back.
    change P σ x = _
    -- The coefficients of the right side are `χ (c x)` times those of `P σ x` in the frame `tW`.
    have hframe : ∑ i, ψ i (c x) • b i = χ (c x) • tW.continuousLinearMapAt ℝ x (P σ x) := by
      rw [← b.sum_repr (tW.continuousLinearMapAt ℝ x (P σ x)), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, hψ i, c.sectionChartCompression_apply, c.left_inv hx, hpull]
      simp [LinearMap.coe_toContinuousLinearMap']
    simp only [chartTestCLM_apply_of_mem _ _ _ _ _ hx, TestFunction.postcompCLM_apply,
      Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply]
    rw [← map_sum, hframe, map_smul, tW.symmL_continuousLinearMapAt (hW hx)]
    by_cases h0 : P σ x = 0
    · simp [h0]
    · obtain ⟨y, hy, rfl⟩ :=
        hsupp (by_contra fun hmem ↦ h0 ((P σ).eq_zero_of_notMem_tsupport hmem))
      rw [c.right_inv (φ.tsupport_subset hy), hχ y hy, one_smul]
  · simp only [chartTestCLM_apply_of_notMem _ _ _ _ _ hx, Finset.sum_const_zero]
    refine (P σ).eq_zero_of_notMem_tsupport fun h ↦ hx ?_
    obtain ⟨y, hy, rfl⟩ := hsupp h
    exact c.map_target (φ.tsupport_subset hy)

/-- **The transpose by a local operator in a chart.** Let `c` be a chart of the maximal atlas with
frames `tV` and `tW` over its source, and `φ` a test function on the chart target on whose support a
cutoff `χ` equals `1`. The component along `v` of the transpose `T ∘ P` pairs with `φ` as the sum,
over a basis `b` of the model fibre of `W`, of the components of `T` along `b i` paired with the
`(b i)*, v` entries of the chart compression of `P` by `χ` and `χ` applied to `φ`. -/
theorem chartComponent_localOperatorDualCLM_apply
    (hP : ∀ (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {χ φ : 𝓓(⟨c.target, c.open_target⟩, ℝ)} (hχ : ∀ y ∈ tsupport φ, χ y = 1)
    {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : ⇑f = φ) (v : F) {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ F') (ψ : ι → 𝓓(⟨c.target, c.open_target⟩, ℝ))
    (hψ : ∀ i, ⇑(ψ i) = c.sectionChartCompression he tV hV tW hW χ χ
      (LinearMap.toContinuousLinearMap (b.coord i)) v P f)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV (localOperatorDualCLM P hP T) v
        φ =
      ∑ i, tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T (b i) (ψ i) := by
  rw [chartComponent_apply, localOperatorDualCLM_apply,
    localOperatorCLM_chartTestCLM hP he hV hW hχ hf v b ψ hψ]
  simp [chartComponent_apply]

/-- **A differential operator in a chart.** Let `c` be a chart of the maximal atlas with frames `tV`
and `tW` over its source, and `y` a point of its target. Over some open neighbourhood `B` of `y`,
the component along `v` of the local representative of the transpose `T ∘ P` by a differential
operator `P` of order at most `r` is a sum of transposes of the components of `T` along the basis
vectors `b i` of the model fibre of `W`, by differential operators `D i` of order at most `r` on
`C^∞(E)`: those of any distributions `R i` with `R i φ = S_{b i} (D i φ)` agree over `B` with it. -/
private theorem exists_restrictCLM_chartComponent_localOperatorDualCLM_eq_sum {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target) (v : F) :
    ∃ B : Opens E, B ≤ ⟨c.target, c.open_target⟩ ∧ y ∈ B ∧
      ∃ D : Fin (Module.finrank ℝ F') → C^∞⟮𝓘(ℝ, E), E; ℝ⟯ →ₗ[ℝ] C^∞⟮𝓘(ℝ, E), E; ℝ⟯,
        (∀ i, D i ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), E; ℝ⟯ C^∞⟮𝓘(ℝ, E), E; ℝ⟯
          C^∞⟮𝓘(ℝ, E), E; ℝ⟯ r) ∧
        ∀ R : Fin (Module.finrank ℝ F') → 𝓓'(⟨c.target, c.open_target⟩, ℂ),
          (∀ i (φ ψ : 𝓓(⟨c.target, c.open_target⟩, ℝ)) (f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯), ⇑f = φ →
            ⇑ψ = D i f → R i φ = tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T
              (Module.finBasis ℝ F' i) ψ) →
          (Distribution.restrictCLM (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
            (localOperatorDualCLM P
              (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) v) :
              𝓓'(B, ℂ)) = ∑ i, Distribution.restrictCLM (R i) := by
  have hloc : ∀ (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0 :=
    fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP
  -- A cutoff `χ` equal to `1` on a neighbourhood `B` of `y` in the chart target.
  obtain ⟨χ, B, hBt, hyB, hB1⟩ :=
    TestFunction.exists_opens_le_forall_eq_one (n := ⊤) (Ω := ⟨c.target, c.open_target⟩) hy
  -- The entries of the chart compression of `P` by `χ` act on the components of `T`.
  let b := Module.finBasis ℝ F'
  let D (i : Fin (Module.finrank ℝ F')) := c.sectionChartCompression he tV hV tW hW χ χ
    (LinearMap.toContinuousLinearMap (b.coord i)) v P
  refine ⟨B, hBt, hyB, D, fun i ↦ c.sectionChartCompression_mem_differentialOperators he tV
    hV tW hW χ χ (LinearMap.toContinuousLinearMap (b.coord i)) v hP, fun R hR ↦ ?_⟩
  -- Over `B`, the component of `T ∘ P` along `v` is the sum of the `R i`.
  ext φ'
  let φ : 𝓓(⟨c.target, c.open_target⟩, ℝ) := TestFunction.monoCLM ℝ φ'
  let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨φ, contMDiff_iff_contDiff.2 φ.contDiff⟩
  have hφχ : ∀ z ∈ tsupport φ, χ z = 1 := fun z hz ↦
    hB1 z (φ'.tsupport_subset (by simpa [φ, hBt] using hz))
  have hD (i) : tsupport (D i f) ⊆ tsupport χ := by
    rw [show ⇑(D i f) = fun z ↦ χ z * _ from
      funext (c.sectionChartCompression_apply he tV hV tW hW χ χ _ v P _)]
    exact tsupport_mul_subset_left
  choose ψ hψ using fun i ↦ TestFunction.exists_coe_eq_of_tsupport_subset
    (contMDiff_iff_contDiff.1 (D i f).contMDiff) (hD i)
  rw [Distribution.restrictCLM_apply,
    chartComponent_localOperatorDualCLM_apply hloc he hV hW hφχ rfl v b ψ hψ T]
  simp only [_root_.sum_apply, Distribution.restrictCLM_apply]
  exact Finset.sum_congr rfl fun i _ ↦ (hR i φ (ψ i) _ rfl (hψ i)).symm

/-- **A differential operator in a chart.** In a chart `c` of the maximal atlas with frames `tV` and
`tW` over its source, if every component of the local representative of `T` is microlocally smooth
at `(y, η)`, then so is every component of that of its transpose `T ∘ P` by a differential
operator `P`. -/
private theorem isMicrolocallySmoothAt_chartComponent_localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {y η : E} (hy : y ∈ c.target)
    (hT : ∀ w, (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T w)
      |>.IsMicrolocallySmoothAt y η) (v : F) :
    (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
      (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) v)
      |>.IsMicrolocallySmoothAt y η := by
  obtain ⟨B, hBt, hyB, D, hD, hsum⟩ :=
    exists_restrictCLM_chartComponent_localOperatorDualCLM_eq_sum hP he hV hW T hy v
  choose R hR hR' using fun i ↦
    Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators
      (hD i) (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T
        (Module.finBasis ℝ F' i))
  rw [← Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB, hsum R hR]
  exact Distribution.IsMicrolocallySmoothAt.sum _ hyB fun i _ ↦
    (Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB).2 (hR' i _ _ (hT _))

/-- **Differential operators do not enlarge wave front sets.** If a functional `T` on the bundle
tests of `W` is microlocally smooth at a covector `ξ`, then so is its transpose `T ∘ P` by a
differential operator `P : Γ(V) → Γ(W)`. -/
theorem IsMicrolocallySmoothAt.localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ}
    (h : IsMicrolocallySmoothAt T x ξ) :
    IsMicrolocallySmoothAt (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x ξ := by
  -- A chart of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨c, he, hxc, hV, hW⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet F 𝓘(ℝ, E) (n := ∞) V F' W x
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  -- Microlocal smoothness is read on the components in this chart and these frames.
  exact (isMicrolocallySmoothAt_iff _ hc hcs hV hxc ξ).2
    (isMicrolocallySmoothAt_chartComponent_localOperatorDualCLM hP he hV hW
      (c.map_source hxc) ((isMicrolocallySmoothAt_iff T hc hcs hW hxc ξ).1 h))

/-- **Differential operators do not enlarge wave front sets** (Hörmander I, §8.1 and §8.2). The
wave front set of the transpose `T ∘ P` of a functional `T` on the bundle tests of `W` by a
differential operator `P : Γ(V) → Γ(W)` lies in the wave front set of `T`. -/
theorem waveFrontSet_localOperatorDualCLM_subset {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    waveFrontSet 𝓘(ℝ, E) (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) ⊆
      waveFrontSet 𝓘(ℝ, E) T :=
  fun _ hp ↦ mem_waveFrontSet_iff.2 ⟨(mem_waveFrontSet_iff.1 hp).1,
    fun h ↦ (mem_waveFrontSet_iff.1 hp).2 (h.localOperatorDualCLM hP)⟩

/-- **Differential operators do not enlarge singular supports.** The singular support of the
transpose `T ∘ P` of a functional `T` on the bundle tests of `W` by a differential operator
`P : Γ(V) → Γ(W)` lies in the singular support of `T`. -/
theorem singularSupport_localOperatorDualCLM_subset [MeasurableSpace E] [BorelSpace E] {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    singularSupport 𝓘(ℝ, E) (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) ⊆
      singularSupport 𝓘(ℝ, E) T := by
  rw [← proj_image_waveFrontSet, ← proj_image_waveFrontSet]
  exact image_mono (waveFrontSet_localOperatorDualCLM_subset hP T)

/-! ### Microlocal elliptic regularity -/

/-- **The transpose by an operator into a line in a chart, near a point.** Let `c` be a chart of
the maximal atlas with frames `tV` and `tW` over its source, `b` a basis of the model fibre of `W`
indexed by a type with at most one element, and `χ` a cutoff on the chart target equal to `1` on an
open set `U`. Restricted to `U`, the component along `v` of the transpose `T ∘ P` by a differential
operator `P` is the transpose `φ ↦ S (D φ)` of the component `S` of `T` along `b i` by the
`(b i)*, v` entry `D` of the chart compression of `P` by `χ` and `χ`. -/
theorem restrictCLM_chartComponent_localOperatorDualCLM_apply {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {χ : 𝓓(⟨c.target, c.open_target⟩, ℝ)} {U : Opens E} (hU : U ≤ ⟨c.target, c.open_target⟩)
    (hχ : ∀ y ∈ U, χ y = 1) (v : F) {ι : Type*} [Finite ι] [Subsingleton ι]
    (b : Module.Basis ι ℝ F') (i : ι) {φ ψ : 𝓓(U, ℝ)} {f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯} (hf : ⇑f = φ)
    (hψ : ⇑ψ = (c.sectionChartCompressionDifferentialOperators he tV hV tW hW χ χ
      (LinearMap.toContinuousLinearMap (b.coord i)) v r ⟨P, hP⟩).val f)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    Distribution.restrictCLM (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
      (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) v) φ =
      Distribution.restrictCLM
        (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T (b i)) ψ := by
  have := Fintype.ofFinite ι
  let φ' : 𝓓(⟨c.target, c.open_target⟩, ℝ) := TestFunction.monoCLM ℝ φ
  have hφχ : ∀ z ∈ tsupport φ', χ z = 1 := fun z hz ↦
    hχ z (φ.tsupport_subset (by simpa [φ', hU] using hz))
  rw [Distribution.restrictCLM_apply, Distribution.restrictCLM_apply,
    chartComponent_localOperatorDualCLM_apply _ he hV hW hφχ (φ := φ') (by simpa [φ', hU] using hf)
      v b (fun _ ↦ TestFunction.monoCLM ℝ ψ) fun j ↦ by
        rw [Subsingleton.elim j i]
        simpa [hU] using hψ, Fintype.sum_subsingleton _ i]

/-- **Microlocal elliptic regularity in a chart.** Let `P : Γ(V) → Γ(W)` be a differential operator
into a bundle `W` of rank one, and `c` a chart of the maximal atlas at `x` with frames `tV` and `tW`
over its source. If the principal symbol of `P` at a covector `ξ` at `x` does not kill the vector
of `V_x` with coefficients `v` in the frame `tV`, and the component along `v` of the transpose
`T ∘ P` is microlocally smooth at `c x` in the direction of `ξ` read in the chart, then so is every
component of `T`. -/
private theorem isMicrolocallySmoothAt_chartComponent_of_localOperatorDualCLM {r : ℕ}
    (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} (hx : x ∈ c.source)
    {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ} {v : F}
    (hσ : sectionPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ
      (tV.symmL ℝ x v) ≠ 0)
    (h : (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
      (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) v)
      |>.IsMicrolocallySmoothAt (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))))
    (w : F') :
    (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T w).IsMicrolocallySmoothAt (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) := by
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  have hy : c x ∈ c.target := c.map_source hx
  -- A cutoff `χ` equal to `1` on a neighbourhood `B` of `c x` in the chart target.
  obtain ⟨χ, B, hBt, hyB, hB1⟩ :=
    TestFunction.exists_opens_le_forall_eq_one (n := ⊤) (Ω := ⟨c.target, c.open_target⟩) hy
  -- The model fibre of `W` is a line, with basis `b 0`, so the coordinate along `b 0` is injective.
  let b := Module.finBasisOfFinrankEq ℝ F' hF'
  have hℓ : Injective (LinearMap.toContinuousLinearMap (b.coord 0)) := by
    simpa only [LinearMap.coe_toContinuousLinearMap'] using b.coord_injective_of_subsingleton 0
  -- Read at `x`, the covector `⟪η, ·⟫ ∘ dc` is `ξ`, for the vector `η` of `ξ ∘ dc⁻¹`.
  have hcov : (innerSL ℝ ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) :
      E →L[ℝ] ℝ).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x) = ξ := by
    ext u
    have hd := congr($((OpenPartialHomeomorph.MDifferentiable.symm_comp_deriv
      ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hx)) u)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hd
    -- `⟪η, dc u⟫ = ξ (dc⁻¹ (dc u)) = ξ u`. Rewriting cannot see through the identification of the
    -- tangent spaces of the chart target with `E`, so the two equalities are composed as terms.
    exact (toDual_symm_apply (𝕜 := ℝ) (E := E) (x := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x u)).trans
      (congrArg ξ hd)
  -- Over `B`, the component of `T ∘ P` along `v` is the transpose of the component of `T` along
  -- `b 0` by the `(b 0)*, v` entry of the chart compression of `P`, which is elliptic at `c x`.
  have hS : (tW.chartComponent c hc hW T (b 0)).IsMicrolocallySmoothAt (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) := by
    rw [← Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB]
    exact Distribution.IsMicrolocallySmoothAt.of_mem_differentialOperators
      (c.sectionChartCompressionDifferentialOperators he tV hV tW hW χ χ
        (LinearMap.toContinuousLinearMap (b.coord 0)) v r ⟨P, hP⟩).property
      (fun _ _ _ hf hψ ↦
        restrictCLM_chartComponent_localOperatorDualCLM_apply hP he hV hW hBt hB1 v b 0 hf hψ T)
      (c.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators_ne_zero he tV hV tW hW
        hℓ hx (by simp [hB1 _ hyB]) (by simp [hB1 _ hyB]) (by convert hσ using 3; exact hcov))
      ((Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB).2 h)
  rw [chartComponent_eq_sum tW c hc hW b T w]
  exact Distribution.IsMicrolocallySmoothAt.sum _ hy fun i _ ↦ by
    rw [Subsingleton.elim i 0]
    exact hS.smul _

/-- **Microlocal elliptic regularity for differential operators into a line bundle** (Hörmander I,
Theorem 8.3.1 and §8.2). Let `P : Γ(V) → Γ(W)` be a differential operator of order at most `r` into
a bundle `W` of rank one, and `ξ` a covector at `x` at which the principal symbol
`σ(P)(ξ) : V_x → W_x` does not vanish. If the transpose `T ∘ P` of a functional `T` on the bundle
tests of `W` is microlocally smooth at `ξ`, then so is `T`. -/
theorem IsMicrolocallySmoothAt.of_localOperatorDualCLM {r : ℕ} (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ}
    (hσ : sectionPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ ≠ 0)
    (h : IsMicrolocallySmoothAt (BundleTest.localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x ξ) :
    IsMicrolocallySmoothAt T x ξ := by
  -- A chart of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨c, he, hxc, hV, hW⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet F 𝓘(ℝ, E) (n := ∞) V F' W x
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  -- A vector `u ∈ V_x` with `σ(P)(ξ) u ≠ 0`, whose coefficients in the frame `tV` are `v`.
  obtain ⟨u, hu⟩ : ∃ u, sectionPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint
      ⟨P, hP⟩ ξ u ≠ 0 := by
    by_contra! h0
    exact hσ (LinearMap.ext h0)
  rw [← (trivializationAt F V x).symmL_continuousLinearMapAt (R := ℝ) (hV hxc) u] at hu
  exact (isMicrolocallySmoothAt_iff T hc hcs hW hxc ξ).2
    (isMicrolocallySmoothAt_chartComponent_of_localOperatorDualCLM hF' hP he hV hW hxc hu
      ((isMicrolocallySmoothAt_iff _ hc hcs hV hxc ξ).1 h _))

/-- **Microlocal elliptic regularity for differential operators into a line bundle**: if
`P : Γ(V) → Γ(W)` is a differential operator into a bundle `W` of rank one, then
`WF(T) ⊆ WF(T ∘ P) ∪ Char(P)` for every functional `T` on the bundle tests of `W`, where `Char(P)`
is the set of covectors at which the principal symbol of `P` vanishes. -/
theorem waveFrontSet_subset_waveFrontSet_localOperatorDualCLM_union {r : ℕ}
    (hF' : Module.finrank ℝ F' = 1)
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    waveFrontSet 𝓘(ℝ, E) T ⊆ waveFrontSet 𝓘(ℝ, E) (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) ∪
      {p | sectionPrincipalSymbol 𝓘(ℝ, E) (x := p.proj) BoundarylessManifold.isInteriorPoint
        ⟨P, hP⟩ p.snd = 0} := by
  intro p hp
  obtain ⟨hp0, hpT⟩ := mem_waveFrontSet_iff.1 hp
  refine or_iff_not_imp_right.2 fun hσ ↦ mem_waveFrontSet_iff.2 ⟨hp0, fun h ↦ hpT ?_⟩
  exact IsMicrolocallySmoothAt.of_localOperatorDualCLM hF' hP hσ h

/-! ### Sobolev regularity -/

section Sobolev

variable [MeasurableSpace E] [BorelSpace E]

/-- **A differential operator in a chart costs its order in microlocal Sobolev regularity.** In a
chart `c` of the maximal atlas with frames `tV` and `tW` over its source, if every component of the
local representative of `T` is microlocally `H^s` at `(y, η)`, then every component of that of its
transpose `T ∘ P` by a differential operator `P` of order at most `r` is microlocally `H^(s - r)`
there. -/
private theorem isMicrolocallySobolevAt_chartComponent_localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {s : ℝ} {y η : E} (hy : y ∈ c.target)
    (hT : ∀ w, (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T w)
      |>.IsMicrolocallySobolevAt s y η) (v : F) :
    (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
      (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) v)
      |>.IsMicrolocallySobolevAt (s - r) y η := by
  obtain ⟨B, hBt, hyB, D, hD, hsum⟩ :=
    exists_restrictCLM_chartComponent_localOperatorDualCLM_eq_sum hP he hV hW T hy v
  choose R hR hR' _ using fun i ↦
    Distribution.exists_forall_apply_eq_and_isMicrolocallySobolevAt_of_mem_differentialOperators
      (hD i) (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T
        (Module.finBasis ℝ F' i))
  rw [← Distribution.isMicrolocallySobolevAt_restrictCLM_iff hBt hyB, hsum R hR]
  exact Distribution.IsMicrolocallySobolevAt.sum _ hyB fun i _ ↦
    (Distribution.isMicrolocallySobolevAt_restrictCLM_iff hBt hyB).2 (hR' i s y η (hT _))

/-- **A differential operator in a chart costs its order in local Sobolev regularity.** In a chart
`c` of the maximal atlas with frames `tV` and `tW` over its source, if every component of the local
representative of `T` is `H^s` near `y`, then every component of that of its transpose `T ∘ P` by a
differential operator `P` of order at most `r` is `H^(s - r)` near `y`. -/
private theorem isLocallySobolevAt_chartComponent_localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {s : ℝ} {y : E} (hy : y ∈ c.target)
    (hT : ∀ w, (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T w)
      |>.IsLocallySobolevAt s y) (v : F) :
    (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
      (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) v)
      |>.IsLocallySobolevAt (s - r) y := by
  obtain ⟨B, hBt, hyB, D, hD, hsum⟩ :=
    exists_restrictCLM_chartComponent_localOperatorDualCLM_eq_sum hP he hV hW T hy v
  choose R hR _ hR' using fun i ↦
    Distribution.exists_forall_apply_eq_and_isMicrolocallySobolevAt_of_mem_differentialOperators
      (hD i) (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T
        (Module.finBasis ℝ F' i))
  rw [← Distribution.isLocallySobolevAt_restrictCLM_iff hBt hyB, hsum R hR]
  exact Distribution.IsLocallySobolevAt.sum hyB fun i _ ↦
    (Distribution.isLocallySobolevAt_restrictCLM_iff hBt hyB).2 (hR' i s y (hT _))

/-- **Differential operators cost their order in microlocal Sobolev regularity.** If a functional
`T` on the bundle tests of `W` is microlocally `H^s` at a covector `ξ`, then its transpose `T ∘ P`
by a differential operator `P : Γ(V) → Γ(W)` of order at most `r` is microlocally `H^(s - r)`
there. -/
theorem IsMicrolocallySobolevAt.localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {s : ℝ} {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ} (h : IsMicrolocallySobolevAt s T x ξ) :
    IsMicrolocallySobolevAt (s - r) (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x ξ := by
  -- A chart of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨c, he, hxc, hV, hW⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet F 𝓘(ℝ, E) (n := ∞) V F' W x
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  -- Microlocal Sobolev regularity is read on the components in this chart and these frames.
  exact (isMicrolocallySobolevAt_iff _ hc hcs hV hxc ξ).2
    (isMicrolocallySobolevAt_chartComponent_localOperatorDualCLM hP he hV hW
      (c.map_source hxc) ((isMicrolocallySobolevAt_iff T hc hcs hW hxc ξ).1 h))

/-- **Differential operators shift the Sobolev wave front set by their order** (Hörmander,
*Lectures on Nonlinear Hyperbolic Differential Equations*, §11.1). The `H^(s - r)` wave front set
of the transpose `T ∘ P` of a functional `T` on the bundle tests of `W` by a differential operator
`P : Γ(V) → Γ(W)` of order at most `r` lies in the `H^s` wave front set of `T`. -/
theorem sobolevWaveFrontSet_localOperatorDualCLM_subset {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    (s : ℝ) (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet 𝓘(ℝ, E) (s - r) (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) ⊆
      sobolevWaveFrontSet 𝓘(ℝ, E) s T :=
  fun _ hp ↦ mem_sobolevWaveFrontSet_iff.2 ⟨(mem_sobolevWaveFrontSet_iff.1 hp).1,
    fun h ↦ (mem_sobolevWaveFrontSet_iff.1 hp).2 (h.localOperatorDualCLM hP)⟩

/-- **Differential operators cost their order in local Sobolev regularity.** If a functional `T` on
the bundle tests of `W` is `H^s` near `x`, then its transpose `T ∘ P` by a differential operator
`P : Γ(V) → Γ(W)` of order at most `r` is `H^(s - r)` near `x`. -/
theorem IsLocallySobolevAt.localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {s : ℝ} {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} (h : IsLocallySobolevAt s T x) :
    IsLocallySobolevAt (s - r) (localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x := by
  -- A chart of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨c, he, hxc, hV, hW⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet F 𝓘(ℝ, E) (n := ∞) V F' W x
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  -- Local Sobolev regularity is read on the components in this chart and these frames.
  exact (isLocallySobolevAt_iff _ hc hcs hV hxc).2
    (isLocallySobolevAt_chartComponent_localOperatorDualCLM hP he hV hW
      (c.map_source hxc) ((isLocallySobolevAt_iff T hc hcs hW hxc).1 h))

/-- **Differential operators shift the Sobolev singular support by their order.** The
`H^(s - r)` singular support of the transpose `T ∘ P` of a functional `T` on the bundle tests of
`W` by a differential operator `P : Γ(V) → Γ(W)` of order at most `r` lies in the `H^s` singular
support of `T`. -/
theorem sobolevSingularSupport_localOperatorDualCLM_subset {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    (s : ℝ) (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    sobolevSingularSupport 𝓘(ℝ, E) (s - r) (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) ⊆
      sobolevSingularSupport 𝓘(ℝ, E) s T :=
  fun _ hx ↦ mem_sobolevSingularSupport_iff.2 fun h ↦
    mem_sobolevSingularSupport_iff.1 hx (h.localOperatorDualCLM hP)

end Sobolev

end TauCeti.BundleTest
