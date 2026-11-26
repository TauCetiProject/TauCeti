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
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Distribution.WaveFrontSet.DifferentialOperator
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization

/-!
# Differential operators on bundles do not enlarge wave front sets

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
statement
`Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators`
applies to every term.

## Main results

* `TauCeti.BundleTest.localOperatorCLM_chartTestCLM`: a local operator between bundles in a chart,
  in terms of the entries of its chart compression.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.localOperatorDualCLM`: the transpose of a
  differential operator between bundles preserves microlocal smoothness.
* `TauCeti.BundleTest.waveFrontSet_localOperatorDualCLM_subset`,
  `TauCeti.BundleTest.singularSupport_localOperatorDualCLM_subset`: it does not enlarge wave front
  sets or singular supports.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (differential operators with smooth coefficients do not enlarge wave front
  sets) and §8.2 (wave front sets on manifolds and bundles).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §7.
-/

public section

noncomputable section

open Set Function TopologicalSpace LineDeriv
open scoped ContDiff Manifold Distributions Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization Filter

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
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hloc : ∀ (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0 :=
    fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP
  -- A cutoff `χ` equal to `1` on a neighbourhood `B` of `y` in the chart target.
  obtain ⟨χ, hχ⟩ := TestFunction.exists_eventually_eq_one_nhds (n := ⊤)
    (Ω := ⟨c.target, c.open_target⟩) hy
  obtain ⟨U, hU1, hU, hyU⟩ := eventually_nhds_iff.1 hχ
  let B : Opens E := ⟨U ∩ c.target, hU.inter c.open_target⟩
  have hBt : B ≤ ⟨c.target, c.open_target⟩ := fun _ hz ↦ hz.2
  have hyB : y ∈ B := ⟨hyU, hy⟩
  -- The entries of the chart compression of `P` by `χ` act on the components of `T`.
  let b := Module.finBasis ℝ F'
  let D (i : Fin (Module.finrank ℝ F')) := c.sectionChartCompression he tV hV tW hW χ χ
    (LinearMap.toContinuousLinearMap (b.coord i)) v P
  choose R hR hR' using fun i ↦
    Distribution.exists_forall_apply_eq_and_isMicrolocallySmoothAt_of_mem_differentialOperators
      (c.sectionChartCompression_mem_differentialOperators he tV hV tW hW χ χ
        (LinearMap.toContinuousLinearMap (b.coord i)) v hP) (tW.chartComponent c hc hW T (b i))
  -- Over `B`, the component of `T ∘ P` along `v` is the sum of the `R i`.
  have hsum : (Distribution.restrictCLM
      (tV.chartComponent c hc hV (localOperatorDualCLM P hloc T) v) : 𝓓'(B, ℂ)) =
        ∑ i, Distribution.restrictCLM (R i) := by
    ext φ'
    let φ : 𝓓(⟨c.target, c.open_target⟩, ℝ) := TestFunction.monoCLM ℝ φ'
    let f : C^∞⟮𝓘(ℝ, E), E; ℝ⟯ := ⟨φ, contMDiff_iff_contDiff.2 φ.contDiff⟩
    have hφχ : ∀ z ∈ tsupport φ, χ z = 1 := fun z hz ↦
      hU1 z (φ'.tsupport_subset (by simpa [φ, hBt] using hz)).1
    have hD (i) : tsupport (D i f) ⊆ tsupport χ := by
      rw [show ⇑(D i f) = fun z ↦ χ z * _ from
        funext (c.sectionChartCompression_apply he tV hV tW hW χ χ _ v P _)]
      exact tsupport_mul_subset_left
    choose ψ hψ using fun i ↦ TestFunction.exists_coe_eq_of_tsupport_subset
      (contMDiff_iff_contDiff.1 (D i f).contMDiff) (hD i)
    rw [Distribution.restrictCLM_apply, chartComponent_apply, localOperatorDualCLM_apply,
      localOperatorCLM_chartTestCLM hloc he hV hW hφχ rfl v b ψ hψ]
    simp only [map_sum, Complex.ofReal_sum, _root_.sum_apply, Distribution.restrictCLM_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hR i φ (ψ i) _ rfl (hψ i), chartComponent_apply]
  rw [← Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB, hsum]
  exact Distribution.IsMicrolocallySmoothAt.sum _ hyB fun i _ ↦
    (Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB).2 (hR' i _ _ (hT (b i)))

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
  let tV := trivializationAt F V x
  let tW := trivializationAt F' W x
  have hopen : IsOpen (tV.baseSet ∩ tW.baseSet) := tV.open_baseSet.inter tW.open_baseSet
  obtain ⟨c, he, hxc, hV, hW⟩ : ∃ c : OpenPartialHomeomorph M E,
      c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧ x ∈ c.source ∧ c.source ⊆ tV.baseSet ∧
        c.source ⊆ tW.baseSet := by
    refine ⟨_, restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) hopen, ?_⟩
    rw [OpenPartialHomeomorph.restr_source' _ _ hopen]
    exact ⟨⟨mem_chart_source E x, FiberBundle.mem_baseSet_trivializationAt' x,
      FiberBundle.mem_baseSet_trivializationAt' x⟩, fun _ hy ↦ hy.2.1, fun _ hy ↦ hy.2.2⟩
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

end TauCeti.BundleTest
