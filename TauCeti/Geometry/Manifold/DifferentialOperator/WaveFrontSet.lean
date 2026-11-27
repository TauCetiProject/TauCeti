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
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

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

Conversely, `T` is as regular as `T ∘ P` at the covectors where `P` is elliptic for this action:
if the principal symbol `σ(P)(ξ) : V_x → W_x` (`TauCeti.sectionPrincipalSymbol`) is surjective
and `T ∘ P` is microlocally smooth at `ξ`, then so is `T`
(`TauCeti.BundleTest.IsMicrolocallySmoothAt.of_localOperatorDualCLM`), and
`WF(T) ⊆ WF(T ∘ P) ∪ Char(P)`, where `Char(P)` is the set of covectors at which `σ(P)(ξ)` is not
surjective (`TauCeti.BundleTest.waveFrontSet_subset_waveFrontSet_localOperatorDualCLM_union`).
Since `T ∘ P` is the transpose of `P` applied to `T`, surjectivity of `σ(P)(ξ)` is injectivity of
the principal symbol of the transpose. When `V` and `W` have the same rank this is invertibility of
`σ(P)(ξ)`, the usual ellipticity of `P`, and when `W` has rank one it says that `σ(P)(ξ)` does not
vanish; scalar operators act on the sections of the trivial line bundle.

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
applies to every term (`TauCeti.BundleTest.chartComponent_localOperatorDualCLM_apply`).

If `σ(P)(ξ)` is surjective, choose vectors `v k` of the model fibre of `V` such that `σ(P)(ξ)`
sends the vector of `V_x` with coefficients `v k` to the vector of `W_x` with coefficients `b k`.
Over `B`, the components of `T ∘ P` along the `v k` form the square system
`φ ↦ ∑ᵢ Sᵢ (D i k φ)`, for the `(bᵢ*, v k)` entries `D i k` of the chart compression. The
principal symbol of `D i k` at `c x` is the `bᵢ` coordinate of `σ(P)(ξ)` applied to the vector of
`V_x` with coefficients `v k`
(`OpenPartialHomeomorph.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators`), so
the principal symbol matrix of the system is the identity, and microlocal elliptic regularity for
systems (`Distribution.IsMicrolocallySmoothAt.of_forall_mem_differentialOperators`) applies to
the components `Sᵢ` of `T`.

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
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.of_localOperatorDualCLM`,
  `TauCeti.BundleTest.waveFrontSet_subset_waveFrontSet_localOperatorDualCLM_union`: microlocal
  elliptic regularity for differential operators between bundles, at the covectors where the
  principal symbol is surjective.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1 (differential operators with smooth coefficients do not enlarge wave front
  sets), Theorem 8.3.1 (microlocal elliptic regularity) and §8.2 (wave front sets on manifolds and
  bundles).
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
  obtain ⟨χ, B, hBt, hyB, hB1⟩ :=
    TestFunction.exists_opens_le_forall_eq_one (n := ⊤) (Ω := ⟨c.target, c.open_target⟩) hy
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

omit [LindelofSpace M] in
/-- **The principal symbols of the entries of the chart compression.** Let `P : Γ(V) → Γ(W)` be a
differential operator and `c` a chart of the maximal atlas at `x` with frames `tV` and `tW` over
its source. The `(b i)*, v` entry of the chart compression of `P` by a cutoff `χ` with
`χ (c x) = 1` has principal symbol at `c x`, at a covector `ξ` at `x` read in the chart, the
`b i` coordinate in the frame `tW` of `σ(P)(ξ)` applied to the vector of `V_x` with coefficients
`v` in the frame `tV`. -/
private theorem smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators_eq {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {x : M} (hx : x ∈ c.source) (ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ)
    {χ : 𝓓(⟨c.target, c.open_target⟩, ℝ)} (hχ : χ (c x) = 1) {ι : Type*}
    (b : Module.Basis ι ℝ F') (i : ι) (v : F) :
    smoothPrincipalSymbol 𝓘(ℝ, E) (x := c x) BoundarylessManifold.isInteriorPoint
      (c.sectionChartCompressionDifferentialOperators he tV hV tW hW χ χ
        (LinearMap.toContinuousLinearMap (b.coord i)) v r ⟨P, hP⟩)
      (innerSL ℝ ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) :
        E →L[ℝ] ℝ) =
      b.coord i (tW.continuousLinearMapAt ℝ x (sectionPrincipalSymbol 𝓘(ℝ, E)
        BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ (tV.symmL ℝ x v))) := by
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  have hy : c x ∈ c.target := c.map_source hx
  set η := (toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))
  have h1 :=
    OpenPartialHomeomorph.smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators
      he tV hV tW hW χ χ (LinearMap.toContinuousLinearMap (b.coord i)) v ⟨P, hP⟩ hy
      (innerSL ℝ η : E →L[ℝ] ℝ)
  simp only [hχ, one_mul, LinearMap.coe_toContinuousLinearMap'] at h1
  -- Read at `x`, the covector `⟪η, ·⟫ ∘ dc` is `ξ`.
  rw [c.left_inv hx] at h1
  have hcov : (innerSL ℝ η : E →L[ℝ] ℝ).comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x) = ξ := by
    ext u
    have hd := congr($((OpenPartialHomeomorph.MDifferentiable.symm_comp_deriv
      ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hx)) u)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hd
    -- `⟪η, dc u⟫ = ξ (dc⁻¹ (dc u)) = ξ u`. Rewriting cannot see through the identification of the
    -- tangent spaces of the chart target with `E`, so the two equalities are composed as terms.
    exact (toDual_symm_apply (𝕜 := ℝ) (E := E) (x := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c x u)).trans
      (congrArg ξ hd)
  exact hcov ▸ h1

/-- **Microlocal elliptic regularity in a chart.** Let `P : Γ(V) → Γ(W)` be a differential
operator, `c` a chart of the maximal atlas at `x` with frames `tV` and `tW` over its source, and
`b` the basis `Module.finBasis` of the model fibre of `W`. Let `v k` be vectors of the model fibre
of `V` such that the principal symbol of `P` at a covector `ξ` at `x` sends the vector of `V_x`
with coefficients `v k` to the vector of `W_x` with coefficients `b k`. If the components along
every `v k` of the
transpose `T ∘ P` are microlocally smooth at `c x` in the direction of `ξ` read in the chart, then
so is every component of `T`: the chart compression of `P` is a square system of differential
operators whose principal symbol matrix at `c x` is the identity. -/
private theorem isMicrolocallySmoothAt_chartComponent_of_localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {c : OpenPartialHomeomorph M E} (he : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {tV : Trivialization F (π F V)} [MemTrivializationAtlas tV] (hV : c.source ⊆ tV.baseSet)
    {tW : Trivialization F' (π F' W)} [MemTrivializationAtlas tW] (hW : c.source ⊆ tW.baseSet)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} (hx : x ∈ c.source)
    {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ} (v : Fin (Module.finrank ℝ F') → F)
    (hσ : ∀ k, sectionPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ
      (tV.symmL ℝ x (v k)) = tW.symmL ℝ x (Module.finBasis ℝ F' k))
    (h : ∀ k, (tV.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hV
      (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) (v k))
      |>.IsMicrolocallySmoothAt (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))))
    (w : F') :
    (tW.chartComponent c (contMDiffOn_of_mem_maximalAtlas he) hW T w).IsMicrolocallySmoothAt (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) := by
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hy : c x ∈ c.target := c.map_source hx
  let b := Module.finBasis ℝ F'
  have hloc : ∀ (s : Cₛ^∞⟮𝓘(ℝ, E); F, V⟯) (x : M), (∀ᶠ y in 𝓝 x, s y = 0) → P s x = 0 :=
    fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP
  -- A cutoff `χ` equal to `1` on a neighbourhood `B` of `c x` in the chart target.
  obtain ⟨χ, B, hBt, hyB, hB1⟩ :=
    TestFunction.exists_opens_le_forall_eq_one (n := ⊤) (Ω := ⟨c.target, c.open_target⟩) hy
  -- Over `B`, the component of `T ∘ P` along `v k` is `φ ↦ ∑ i, S i (D i k φ)`, for the
  -- components `S i` of `T` along `b i` and the `(b i)*, v k` entries `D i k` of the chart
  -- compression of `P`, whose principal symbol matrix at `c x` is the identity.
  have hS (i : Fin (Module.finrank ℝ F')) :
      (tW.chartComponent c hc hW T (b i)).IsMicrolocallySmoothAt (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) := by
    rw [← Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB]
    refine Distribution.IsMicrolocallySmoothAt.of_forall_mem_differentialOperators
      (fun i k ↦ (c.sectionChartCompressionDifferentialOperators he tV hV tW hW χ χ
        (LinearMap.toContinuousLinearMap (b.coord i)) (v k) r ⟨P, hP⟩).property)
      (S := fun i ↦ Distribution.restrictCLM (tW.chartComponent c hc hW T (b i)))
      (R := fun k ↦ Distribution.restrictCLM (tV.chartComponent c hc hV
        (localOperatorDualCLM P hloc T) (v k))) (fun k φ' ψ' f hf hψ' ↦ ?_) ?_
      (fun k ↦ (Distribution.isMicrolocallySmoothAt_restrictCLM_iff hBt hyB).2 (h k)) i
    · let φ : 𝓓(⟨c.target, c.open_target⟩, ℝ) := TestFunction.monoCLM ℝ φ'
      have hφχ : ∀ z ∈ tsupport φ, χ z = 1 := fun z hz ↦
        hB1 z (φ'.tsupport_subset (by simpa [φ, hBt] using hz))
      rw [Distribution.restrictCLM_apply, chartComponent_localOperatorDualCLM_apply hloc he hV hW
        hφχ (φ := φ) (by simpa [φ, hBt] using hf) (v k) b (fun i ↦ TestFunction.monoCLM ℝ (ψ' i))
        fun i ↦ by simpa [hBt] using hψ' i]
      simp
    · have hmat : (Matrix.of fun i k ↦ smoothPrincipalSymbol 𝓘(ℝ, E) (x := c x)
          BoundarylessManifold.isInteriorPoint
          ⟨_, (c.sectionChartCompressionDifferentialOperators he tV hV tW hW χ χ
            (LinearMap.toContinuousLinearMap (b.coord i)) (v k) r ⟨P, hP⟩).property⟩
          (innerSL ℝ ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) c.symm (c x))) :
            E →L[ℝ] ℝ)) = 1 := by
        ext i k
        rw [Matrix.of_apply, smoothPrincipalSymbol_sectionChartCompressionDifferentialOperators_eq
          hP he hV hW hx ξ (hB1 _ hyB) b i (v k), hσ k,
          tW.continuousLinearMapAt_symmL (R := ℝ) (hW hx)]
        simp [b, Matrix.one_apply, Finsupp.single_apply, eq_comm]
      rw [hmat, Matrix.det_one]
      exact one_ne_zero
  rw [chartComponent_eq_sum tW c hc hW b T w]
  exact Distribution.IsMicrolocallySmoothAt.sum _ hy fun i _ ↦ (hS i).smul _

/-- **Microlocal elliptic regularity for differential operators between bundles** (Hörmander I,
Theorem 8.3.1 and §8.2). Let `P : Γ(V) → Γ(W)` be a differential operator of order at most `r`,
and `ξ` a covector at `x` at which the principal symbol `σ(P)(ξ) : V_x → W_x` is surjective. If
the transpose `T ∘ P` of a functional `T` on the bundle tests of `W` is microlocally smooth at
`ξ`, then so is `T`. Surjectivity of `σ(P)(ξ)` is injectivity of the principal symbol of the
transpose, so this is microlocal elliptic regularity for the transpose; when `V` and `W` have the
same rank it says that `σ(P)(ξ)` is invertible, and when `W` has rank one that it does not
vanish. -/
theorem IsMicrolocallySmoothAt.of_localOperatorDualCLM {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    {T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ} {x : M} {ξ : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ}
    (hσ : Function.Surjective
      (sectionPrincipalSymbol 𝓘(ℝ, E) BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ ξ))
    (h : IsMicrolocallySmoothAt (BundleTest.localOperatorDualCLM P
      (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) x ξ) :
    IsMicrolocallySmoothAt T x ξ := by
  -- A chart of the maximal atlas at `x` over which both bundles are trivial.
  obtain ⟨c, he, hxc, hV, hW⟩ :=
    exists_mem_maximalAtlas_source_subset_baseSet F 𝓘(ℝ, E) (n := ∞) V F' W x
  have hc := contMDiffOn_of_mem_maximalAtlas he
  have hcs := contMDiffOn_symm_of_mem_maximalAtlas he
  -- Vectors `u k ∈ V_x`, with coefficients `v k` in the frame of `V`, which `σ(P)(ξ)` sends to
  -- the vectors of `W_x` with coefficients `b k` in the frame of `W`.
  let b := Module.finBasis ℝ F'
  choose u hu using fun k ↦ hσ ((trivializationAt F' W x).symmL ℝ x (b k))
  refine (isMicrolocallySmoothAt_iff T hc hcs hW hxc ξ).2
    (isMicrolocallySmoothAt_chartComponent_of_localOperatorDualCLM hP he hV hW hxc
      (fun k ↦ (trivializationAt F V x).continuousLinearMapAt ℝ x (u k)) (fun k ↦ ?_)
      fun k ↦ (isMicrolocallySmoothAt_iff _ hc hcs hV hxc ξ).1 h _)
  rw [(trivializationAt F V x).symmL_continuousLinearMapAt (R := ℝ) (hV hxc), hu k]

/-- **Microlocal elliptic regularity for differential operators between bundles**: if
`P : Γ(V) → Γ(W)` is a differential operator, then `WF(T) ⊆ WF(T ∘ P) ∪ Char(P)` for every
functional `T` on the bundle tests of `W`, where `Char(P)` is the set of covectors at which the
principal symbol `σ(P)(ξ) : V_x → W_x` is not surjective. -/
theorem waveFrontSet_subset_waveFrontSet_localOperatorDualCLM_union {r : ℕ}
    (hP : P ∈ differentialOperators ℝ C^∞⟮𝓘(ℝ, E), M; ℝ⟯ Cₛ^∞⟮𝓘(ℝ, E); F, V⟯
      Cₛ^∞⟮𝓘(ℝ, E); F', W⟯ r)
    (T : BundleTest 𝓘(ℝ, E) F' W →L_c[ℝ] ℝ) :
    waveFrontSet 𝓘(ℝ, E) T ⊆ waveFrontSet 𝓘(ℝ, E) (localOperatorDualCLM P
        (fun _ _ ↦ differentialOperators_section_apply_eq_zero_of_eventuallyEq hP) T) ∪
      {p | ¬Function.Surjective (sectionPrincipalSymbol 𝓘(ℝ, E) (x := p.proj)
        BoundarylessManifold.isInteriorPoint ⟨P, hP⟩ p.snd)} := by
  intro p hp
  obtain ⟨hp0, hpT⟩ := mem_waveFrontSet_iff.1 hp
  refine or_iff_not_imp_right.2 fun hσ ↦ mem_waveFrontSet_iff.2 ⟨hp0, fun h ↦ hpT ?_⟩
  exact IsMicrolocallySmoothAt.of_localOperatorDualCLM hP (not_not.1 hσ) h

end TauCeti.BundleTest
