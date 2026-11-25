/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocalDiffeomorph.OpenSubset
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Opens
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology
public import TauCeti.Geometry.Manifold.VectorBundle.Section.LocalSobolev
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Topology.VectorBundle.Pullback

/-!
# Regularity and wave front set of the restriction to an open subset

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space, let `U ⊆ M` be open, and let `T` be a real continuous
linear functional on the bundle tests of `V`, for instance a distributional section of a bundle.
Its restriction `T|_U` (`TauCeti.BundleTest.restrictDualCLM`) is the functional on the bundle tests
of `V|_U` that pairs a test with `T` after extending it by zero. This file shows that local
regularity, microlocal smoothness, the wave front set and the singular support of `T|_U` are read
off from those of `T`: these notions are local, and the charts of `U` are restrictions of the
charts of `M`.

On a manifold without boundary:

* For every invariant notion of local regularity `P` (`Distribution.IsInvariantLocalRegularity`),
  `T|_U` satisfies `P` near `x ∈ U` exactly when `T` does
  (`TauCeti.BundleTest.isLocallyAt_restrictDualCLM_iff`). In particular `T|_U` is `H^s` near `x`
  exactly when `T` is (`TauCeti.BundleTest.isLocallySobolevAt_restrictDualCLM_iff`), and similarly
  for `H^{s,p}`, `1 < p < ∞`, and for the `H^s` singular support.
* `T|_U` is microlocally smooth at a covector `ξ` at `x ∈ U` exactly when `T` is microlocally
  smooth at the same covector viewed on `M`
  (`TauCeti.BundleTest.isMicrolocallySmoothAt_restrictDualCLM_iff`). Hence the wave front set of
  `T|_U` is the part of the wave front set of `T` over `U`, `WF(T|_U) = WF(T) ∩ T*U`, through the
  inclusion `T*U → T*M` (`TauCeti.BundleTest.waveFrontSet_restrictDualCLM`), and the singular
  support of `T|_U` is `singsupp T ∩ U` (`TauCeti.BundleTest.singularSupport_restrictDualCLM`).

## The argument

Let `c` be a smooth chart of `M` with smooth inverse and `t` a frame over its source. Its
restriction `c|_U` (`OpenPartialHomeomorph.subtypeRestr`) is a smooth chart of `U`, with target the
open subset `c (c.source ∩ U)` of the target of `c`, and the pullback of `t` along the inclusion is
a frame over its source. Extending by zero the bundle test of `U` built from a test function `ψ` on
the target of `c|_U` through `c|_U` and this frame gives the bundle test of `M` built from `ψ`,
extended by zero to the target of `c`, through `c` and `t`
(`Bundle.Trivialization.extendByZeroCLM_chartTestCLM_subtypeRestr`). Therefore the components of
`T|_U` in `c|_U` are the restrictions of the components of `T` in `c`
(`Bundle.Trivialization.chartComponent_subtypeRestr_restrictDualCLM`), and restriction of
distributions to open subsets preserves local regularity and microlocal smoothness. The inverse
charts of `U` and `M` have the same differential, so the covectors read in the two charts agree.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold is defined locally).
-/

public section

noncomputable section

open Bundle Set Filter TopologicalSpace Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM ENNReal

/-! ### Restricted charts and pulled back frames -/

namespace Bundle.Trivialization

open TauCeti

section ChartTest

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  {c : OpenPartialHomeomorph M E}
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
  {U : Opens M} (hU : Nonempty U)

/-- **Chart extension commutes with restriction to an open subset.** The bundle test of `U` built
from a test function `ψ` on the target of the restricted chart `c|_U`, through `c|_U` and the
pulled back frame, extends by zero to the bundle test of `M` built from `ψ`, extended by zero to
the target of `c`, through `c` and `t`. -/
theorem extendByZeroCLM_chartTestCLM_subtypeRestr
    (ψ : 𝓓(⟨(c.subtypeRestr hU).target, (c.subtypeRestr hU).open_target⟩, F)) :
    BundleTest.extendByZeroCLM (I := I) (F := F) (V := V)
      ((t.pullback (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))).chartTestCLM
        (c.subtypeRestr hU) (c.contMDiffOn_subtypeRestr hU hc)
        (t.subtypeRestr_source_subset_pullback_baseSet hU hct) ψ) =
      t.chartTestCLM c hc hct (TestFunction.monoCLM ℝ ψ) := by
  have hle : (⟨(c.subtypeRestr hU).target, (c.subtypeRestr hU).open_target⟩ : Opens E) ≤
      ⟨c.target, c.open_target⟩ := c.subtypeRestr_target_subset hU
  apply BundleTest.ext
  intro y
  by_cases hyU : y ∈ U
  · have hyc : y ∈ c.source ↔ (⟨y, hyU⟩ : U) ∈ (c.subtypeRestr hU).source := by
      rw [OpenPartialHomeomorph.subtypeRestr_source, mem_preimage]
    -- The extension and chart-extension lemmas are stated on the native test wrapper and on the
    -- pullback fibre `(Subtype.val *ᵖ V) ⟨y, hyU⟩`; they match this goal only up to unfolding
    -- these, which `rw` does not do.
    erw [BundleTest.extendByZeroCLM_apply_of_mem _ (⟨y, hyU⟩ : U)]
    by_cases hy : y ∈ c.source
    · erw [t.chartTestCLM_apply_of_mem c hc hct _ hy,
        (t.pullback (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))).chartTestCLM_apply_of_mem
          _ _ _ _ (hyc.1 hy)]
      simp only [TestFunction.monoCLM_apply, hle, le_refl, and_self, ↓reduceIte,
        OpenPartialHomeomorph.subtypeRestr_coe, Set.domRestrict_apply]
      exact pullback_symmL_apply t _ _ _
    · erw [t.chartTestCLM_apply_of_notMem c hc hct _ hy,
        (t.pullback (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))).chartTestCLM_apply_of_notMem
          _ _ _ _ (mt hyc.2 hy)]
      -- Both sides are zero; the zero of the pullback fibre `(Subtype.val *ᵖ V) ⟨y, hyU⟩` is by
      -- definition the zero of `V y`.
      rfl
  · rw [BundleTest.extendByZeroCLM_apply_of_notMem _ hyU]
    by_cases hy : y ∈ c.source
    · rw [t.chartTestCLM_apply_of_mem c hc hct _ hy]
      -- `c y` lies outside the restricted target, since `c⁻¹ (c y) = y ∉ U`.
      have hcy : c y ∉ (c.subtypeRestr hU).target := fun h ↦ hyU <| by
        have hsymm := c.subtypeRestr_symm_apply hU h
        rw [c.left_inv hy] at hsymm
        rw [← hsymm]
        exact ((c.subtypeRestr hU).symm (c y)).property
      simp only [TestFunction.monoCLM_apply, hle, le_refl, and_self, ↓reduceIte,
        image_eq_zero_of_notMem_tsupport fun h ↦ hcy (ψ.tsupport_subset h), map_zero]
    · rw [t.chartTestCLM_apply_of_notMem c hc hct _ hy]

end ChartTest

section ChartComponent

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  {c : OpenPartialHomeomorph M E}
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
  {U : Opens M} (hU : Nonempty U)

/-- **Components of a restriction.** The components of the restriction `T|_U` in the restricted
chart `c|_U` and the pulled back frame are the restrictions of the components of `T` in `c` and
`t` to the target of `c|_U`. -/
theorem chartComponent_subtypeRestr_restrictDualCLM (T : BundleTest I F V →L_c[ℝ] ℝ) (v : F) :
    (t.pullback (⟨Subtype.val, continuous_subtypeVal⟩ : C(U, M))).chartComponent
        (c.subtypeRestr hU) (c.contMDiffOn_subtypeRestr hU hc)
        (t.subtypeRestr_source_subset_pullback_baseSet hU hct)
        (BundleTest.restrictDualCLM (I := I) (F := F) (V := V) T) v =
      Distribution.restrictCLM (t.chartComponent c hc hct T v) := by
  have hle : (⟨(c.subtypeRestr hU).target, (c.subtypeRestr hU).open_target⟩ : Opens E) ≤
      ⟨c.target, c.open_target⟩ := c.subtypeRestr_target_subset hU
  ext φ
  rw [chartComponent_apply, restrictCLM_apply, chartComponent_apply]
  -- `restrictDualCLM_apply` is stated after unfolding the bundled inclusion `C(U, M)`, which `rw`
  -- does not do.
  erw [BundleTest.restrictDualCLM_apply]
  rw [extendByZeroCLM_chartTestCLM_subtypeRestr t hc hct hU]
  congr 3
  ext y
  simp [TestFunction.monoCLM_apply, hle]

end ChartComponent

end Bundle.Trivialization

/-! ### Local regularity, wave front set and singular support of a restriction -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M] {U : Opens M}

/-- **Local regularity of a restriction.** On a manifold without boundary, for an invariant notion
of local regularity `P`, the restriction `T|_U` of `T` to an open subset `U` satisfies `P` near a
point `x` of `U` exactly when `T` satisfies `P` near `x`. -/
theorem isLocallyAt_restrictDualCLM_iff {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → Prop}
    (hP : IsInvariantLocalRegularity P) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : U) :
    IsLocallyAt P (restrictDualCLM (I := I) (F := F) (V := V) T) x ↔ IsLocallyAt P T (x : M) := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) (x : M)
  have hU : Nonempty U := ⟨x⟩
  have hxU : x ∈ (c.subtypeRestr hU).source := by rwa [OpenPartialHomeomorph.subtypeRestr_source]
  rw [isLocallyAt_iff hP _ hc hcs hct hx, isLocallyAt_iff hP _ (c.contMDiffOn_subtypeRestr hU hc)
    (c.contMDiffOn_subtypeRestr_symm hU hcs)
    ((trivializationAt F V (x : M)).subtypeRestr_source_subset_pullback_baseSet hU hct) hxU]
  refine forall_congr' fun v ↦ ?_
  rw [chartComponent_subtypeRestr_restrictDualCLM _ hc hct hU]
  exact hP.restrictCLM_iff (c.subtypeRestr_target_subset hU) (c.map_subtype_source hU hx)

/-- **Microlocal smoothness of a restriction.** On a manifold without boundary, the restriction
`T|_U` of `T` to an open subset `U` is microlocally smooth at a covector `ξ` at `x ∈ U` exactly when
`T` is microlocally smooth at `ξ`, read as a covector of `M` at `x`. -/
theorem isMicrolocallySmoothAt_restrictDualCLM_iff (T : BundleTest I F V →L_c[ℝ] ℝ) (x : U)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt (restrictDualCLM (I := I) (F := F) (V := V) T) x ξ ↔
      IsMicrolocallySmoothAt T (x : M)
        (ξ ∘L (Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap) := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) (x : M)
  have hU : Nonempty U := ⟨x⟩
  have hxU : x ∈ (c.subtypeRestr hU).source := by rwa [OpenPartialHomeomorph.subtypeRestr_source]
  rw [isMicrolocallySmoothAt_iff _ hc hcs hct hx, isMicrolocallySmoothAt_iff _
    (c.contMDiffOn_subtypeRestr hU hc) (c.contMDiffOn_subtypeRestr_symm hU hcs)
    ((trivializationAt F V (x : M)).subtypeRestr_source_subset_pullback_baseSet hU hct) hxU]
  -- The inverse charts of `U` and of `M` have the same differential at `c x`, so the covector `ξ`
  -- is read as the same vector of `E` in both charts.
  have hξ : (ξ ∘L mfderiv 𝓘(ℝ, E) I (c.subtypeRestr hU).symm (c.subtypeRestr hU x) : E →L[ℝ] ℝ) =
      (ξ ∘L (Manifold.tangentSpaceOpenEquiv (I := I) x).symm.toContinuousLinearMap) ∘L
        mfderiv 𝓘(ℝ, E) I c.symm (c x) := by
    ext u
    exact congrArg ξ ((c.mfderiv_subtypeRestr_symm_apply hU ((c.subtypeRestr hU).map_source hxU)
      u).trans (Manifold.tangentSpaceOpenEquiv_symm_apply x _).symm)
  refine forall_congr' fun v ↦ ?_
  rw [chartComponent_subtypeRestr_restrictDualCLM _ hc hct hU, hξ]
  exact isMicrolocallySmoothAt_restrictCLM_iff (c.subtypeRestr_target_subset hU)
    (c.map_subtype_source hU hx)

/-- **The wave front set of a restriction** is the part of the wave front set over the open
subset: on a manifold without boundary, a covector of `U` lies in `WF(T|_U)` exactly when its image
under the inclusion `T*U → T*M` lies in `WF(T)`. -/
@[simp]
theorem waveFrontSet_restrictDualCLM (T : BundleTest I F V →L_c[ℝ] ℝ) :
    dsimp% only [ContinuousMap.coe_mk] (
    waveFrontSet I (restrictDualCLM (I := I) (F := F) (V := V) T) =
      CotangentBundle.openInclusion U ⁻¹' waveFrontSet I T) := by
  -- The bundle instances of the restriction live on the pullback along the bundled inclusion, so
  -- the proof works with the statement before `ContinuousMap.coe_mk` unfolds it.
  change waveFrontSet I (restrictDualCLM (I := I) (F := F) (V := V) T) =
    CotangentBundle.openInclusion U ⁻¹' waveFrontSet I T
  ext p
  rw [mem_preimage, mem_waveFrontSet_iff, mem_waveFrontSet_iff,
    isMicrolocallySmoothAt_restrictDualCLM_iff]
  refine and_congr (not_congr ⟨fun h ↦ ?_, fun h ↦ ?_⟩) (by rw [CotangentBundle.openInclusion_def])
  · ext v
    exact (CotangentBundle.openInclusion_snd_apply U p v).trans (by rw [h]; rfl)
  · ext v
    have hv := (CotangentBundle.openInclusion_snd_apply U p _).symm.trans
      (DFunLike.congr_fun h (Manifold.tangentSpaceOpenEquiv (I := I) p.proj v))
    rwa [ContinuousLinearEquiv.symm_apply_apply] at hv

section Measurable

variable [MeasurableSpace E] [BorelSpace E]

/-- **The singular support of a restriction**: on a manifold without boundary, the restriction
`T|_U` of `T` to an open subset `U` is smooth near `x ∈ U` exactly when `T` is, so
`singsupp (T|_U) = singsupp T ∩ U`. -/
@[simp]
theorem singularSupport_restrictDualCLM (T : BundleTest I F V →L_c[ℝ] ℝ) :
    dsimp% only [ContinuousMap.coe_mk] (
    singularSupport I (restrictDualCLM (I := I) (F := F) (V := V) (U := U) T) =
      Subtype.val ⁻¹' singularSupport I T) := by
  -- As for `waveFrontSet_restrictDualCLM`, work with the statement before unfolding.
  change singularSupport I (restrictDualCLM (I := I) (F := F) (V := V) (U := U) T) =
    Subtype.val ⁻¹' singularSupport I T
  ext x
  rw [mem_preimage, ← not_iff_not, notMem_singularSupport_iff_forall_isMicrolocallySmoothAt,
    notMem_singularSupport_iff_forall_isMicrolocallySmoothAt]
  simp_rw [isMicrolocallySmoothAt_restrictDualCLM_iff]
  -- Composition with the identification of the tangent spaces is a bijection on covectors.
  set e := Manifold.tangentSpaceOpenEquiv (I := I) x
  refine ⟨fun h η hη ↦ ?_, fun h ξ hξ ↦ h _ fun h0 ↦ hξ ?_⟩
  · have hη' : η ∘L e.toContinuousLinearMap ≠ 0 := fun h0 ↦ hη <| by
      rw [← ContinuousLinearMap.comp_id η, ← e.coe_comp_coe_symm, ← ContinuousLinearMap.comp_assoc,
        h0, ContinuousLinearMap.zero_comp]
    simpa [ContinuousLinearMap.comp_assoc] using h _ hη'
  · rw [← Manifold.comp_tangentSpaceOpenEquiv_symm_comp (I := I) x ξ]
    exact congrArg (· ∘L _) h0

/-- On a manifold without boundary, the restriction `T|_U` of `T` to an open subset `U` is `H^s`
near `x ∈ U` exactly when `T` is. -/
theorem isLocallySobolevAt_restrictDualCLM_iff {s : ℝ} (T : BundleTest I F V →L_c[ℝ] ℝ)
    (x : U) :
    IsLocallySobolevAt s (restrictDualCLM (I := I) (F := F) (V := V) T) x ↔
      IsLocallySobolevAt s T (x : M) := by
  rw [isLocallySobolevAt_def, isLocallySobolevAt_def]
  exact isLocallyAt_restrictDualCLM_iff (isInvariantLocalRegularity_isLocallySobolevAt s) T x

/-- On a manifold without boundary, the `H^s` singular support of the restriction `T|_U` of `T` to
an open subset `U` is the part of the `H^s` singular support of `T` in `U`. -/
@[simp]
theorem sobolevSingularSupport_restrictDualCLM (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    dsimp% only [ContinuousMap.coe_mk] (
    sobolevSingularSupport I s (restrictDualCLM (I := I) (F := F) (V := V) (U := U) T) =
      Subtype.val ⁻¹' sobolevSingularSupport I s T) := by
  -- As for `waveFrontSet_restrictDualCLM`, work with the statement before unfolding.
  change sobolevSingularSupport I s (restrictDualCLM (I := I) (F := F) (V := V) (U := U) T) =
    Subtype.val ⁻¹' sobolevSingularSupport I s T
  ext x
  rw [mem_preimage, mem_sobolevSingularSupport_iff, mem_sobolevSingularSupport_iff]
  exact (isLocallySobolevAt_restrictDualCLM_iff T x).not

/-- On a manifold without boundary, for `1 < p < ∞`, the restriction `T|_U` of `T` to an open
subset `U` is `H^{s,p}` near `x ∈ U` exactly when `T` is. -/
theorem isLocallyMemSobolevAt_restrictDualCLM_iff {s : ℝ} {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : 1 < p)
    (hp_top : p ≠ (∞ : ℝ≥0∞)) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : U) :
    IsLocallyMemSobolevAt s p (restrictDualCLM (I := I) (F := F) (V := V) T) x ↔
      IsLocallyMemSobolevAt s p T (x : M) := by
  rw [isLocallyMemSobolevAt_def, isLocallyMemSobolevAt_def]
  exact isLocallyAt_restrictDualCLM_iff
    (isInvariantLocalRegularity_isLocallyMemSobolevAt s hp hp_top) T x

end Measurable

end TauCeti.BundleTest
