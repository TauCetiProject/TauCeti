/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.Restriction
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Multiplication of bundle tests and their functionals by smooth functions

Let `V → M` be a smooth real vector bundle and `f` a smooth real function on `M`. Multiplying a
bundle test `s` by `f` gives the bundle test `x ↦ f x • s x`, and this is a continuous linear map
for the test topology (`TauCeti.BundleTest.smulLeftCLM`). Its transpose sends a continuous linear
functional `T` on bundle tests to the functional `f T : s ↦ T (f s)`
(`TauCeti.BundleTest.smulLeftDualCLM`). For a distributional section `u` of a bundle
(`TauCeti.BundleDistribution`) this is the product `f u`: on a section `u` the pairing with a test
is the integral of the density `x ↦ s x (u x)`, and moving `f` from `s` to `u` does not change
it. Multiplication by cutoff functions is how distributions on manifolds are localized.

In a smooth chart `c` with a frame `t` over its source, multiplication by `f` is multiplication by
`f ∘ c⁻¹` in coordinates. Since `f ∘ c⁻¹` is only defined on the chart target, the statements use
a smooth function `g` on the model space agreeing with it where it matters: the chart extension of
a test function `φ` multiplied by `f` is the chart extension of `g φ` when `g = f ∘ c⁻¹` on the
support of `φ` (`Bundle.Trivialization.smulLeftCLM_chartTestCLM`), and over an open set `B` on
which `g = f ∘ c⁻¹`, the local representative of `f T` is `g` times the local representative of
`T` (`Bundle.Trivialization.restrictCLM_chartDistributionCLM_smulLeftDualCLM`). Near every point
of the chart target such a `g` exists
(`Bundle.Trivialization.exists_forall_restrictCLM_chartDistributionCLM_smulLeftDualCLM`). This is
how regularity properties of `f T` are read off from those of `T` chart by chart.

## Main declarations

* `TauCeti.BundleTest.smulLeftCLM`: multiplication of bundle tests by a smooth function.
* `TauCeti.BundleTest.smulLeftDualCLM`: the product `f T` of a functional on bundle tests with a
  smooth function, and `TauCeti.BundleTest.smulLeftDualCLM_delta`: `f δ_x ℓ = f(x) δ_x ℓ`.
* `Bundle.Trivialization.restrictCLM_chartDistributionCLM_smulLeftDualCLM`,
  `Bundle.Trivialization.exists_forall_restrictCLM_chartDistributionCLM_smulLeftDualCLM`: the local
  representative of `f T`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.1 (multiplication of distributions by smooth functions) and §6.3
  (distributions on manifolds).
-/

public noncomputable section

open Bundle Set Function TopologicalSpace ContMDiffSection ContinuousLinearMap
open scoped ContDiff Manifold Distributions CompactConvergenceCLM

namespace TauCeti.BundleTest

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-! ### Multiplication of tests -/

/-- Multiplication of bundle tests by a smooth real function `f`, sending a test `s` to the test
`x ↦ f x • s x`, as a continuous linear map for the test topology. -/
def smulLeftCLM (f : C^∞⟮I, M; ℝ⟯) : BundleTest I F V →L[ℝ] BundleTest I F V where
  toLinearMap := (ofCompactlySupported I F V).toLinearMap ∘ₗ
    (smulLinearMap f).restrict (fun _ hs ↦ smul_function_mem_compactlySupported f hs) ∘ₗ
    (ofCompactlySupported I F V).symm.toLinearMap
  cont := by
    let := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp _).2 fun K ↦ ?_
    -- Multiplication by `f` maps the stage of sections supported in `K` to itself, continuously
    -- for the frame topology.
    refine ((continuous_ofSupportedIn K).comp
      (((continuous_smul_function_frameTopology _ _ _ f).comp continuous_subtypeVal).subtype_mk
        fun s ↦ smul_function_mem_supportedIn f s.property)).congr fun s ↦ ?_
    simp [LinearMap.restrict_apply, Subtype.ext_iff]

@[simp]
theorem smulLeftCLM_apply (f : C^∞⟮I, M; ℝ⟯) (s : BundleTest I F V) (x : M) :
    smulLeftCLM f s x = f x • s x := by
  simp [smulLeftCLM, LinearMap.restrict_apply]

/-- Multiplying a bundle test by a smooth function `f` gives a test supported in the supports of
`f` and of the test. -/
theorem tsupport_smulLeftCLM_subset (f : C^∞⟮I, M; ℝ⟯) (s : BundleTest I F V) :
    closure {x | smulLeftCLM f s x ≠ 0} ⊆ tsupport f ∩ closure {x | s x ≠ 0} := by
  simpa [ContMDiffSection.tsupport_def, ContMDiffSection.smul_apply] using
    tsupport_smul_function_subset f ((ofCompactlySupported I F V).symm s).val

/-- Multiplying by the constant function `1` does nothing. -/
@[simp]
theorem smulLeftCLM_one :
    smulLeftCLM (1 : C^∞⟮I, M; ℝ⟯) = ContinuousLinearMap.id ℝ (BundleTest I F V) := by
  ext s x
  simp

/-- Multiplying by `g` and then by `f` is multiplying by `f g`. -/
@[simp]
theorem smulLeftCLM_smulLeftCLM (f g : C^∞⟮I, M; ℝ⟯) (s : BundleTest I F V) :
    smulLeftCLM f (smulLeftCLM g s) = smulLeftCLM (f * g) s := by
  ext x
  simp [smul_smul]

/-- Multiplication by a sum of functions is the sum of the multiplications. -/
theorem smulLeftCLM_add (f g : C^∞⟮I, M; ℝ⟯) :
    smulLeftCLM (f + g) = (smulLeftCLM f + smulLeftCLM g : BundleTest I F V →L[ℝ] _) := by
  ext s x
  simp [add_smul]

/-! ### Multiplication of functionals -/

section Dual

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul ℝ W]

/-- The product `f T` of a continuous linear functional `T` on bundle tests with a smooth real
function `f`, defined by `(f T) s = T (f s)`: the transpose of multiplication of tests by `f`
(`TauCeti.BundleTest.smulLeftCLM`), as a continuous linear map for the topology of uniform
convergence on compact sets of tests. On the distributional sections of a bundle
(`TauCeti.BundleDistribution`) it extends the pointwise product of a section with `f`. -/
def smulLeftDualCLM (f : C^∞⟮I, M; ℝ⟯) :
    (BundleTest I F V →L_c[ℝ] W) →L[ℝ] BundleTest I F V →L_c[ℝ] W :=
  (smulLeftCLM f).precompCompactConvergenceCLM W

@[simp]
theorem smulLeftDualCLM_apply (f : C^∞⟮I, M; ℝ⟯) (T : BundleTest I F V →L_c[ℝ] W)
    (s : BundleTest I F V) : smulLeftDualCLM f T s = T (smulLeftCLM f s) :=
  (rfl)

/-- Multiplying a functional by the constant function `1` does nothing. -/
@[simp]
theorem smulLeftDualCLM_one (T : BundleTest I F V →L_c[ℝ] W) :
    smulLeftDualCLM (1 : C^∞⟮I, M; ℝ⟯) T = T := by
  ext s
  simp

/-- Multiplying a functional by `g` and then by `f` is multiplying it by `f g`. -/
@[simp]
theorem smulLeftDualCLM_smulLeftDualCLM (f g : C^∞⟮I, M; ℝ⟯) (T : BundleTest I F V →L_c[ℝ] W) :
    smulLeftDualCLM f (smulLeftDualCLM g T) = smulLeftDualCLM (f * g) T := by
  ext s
  simp [mul_comm]

/-- Multiplication of functionals by a sum of functions is the sum of the multiplications. -/
theorem smulLeftDualCLM_add (f g : C^∞⟮I, M; ℝ⟯) :
    smulLeftDualCLM (f + g) =
      (smulLeftDualCLM f + smulLeftDualCLM g : (BundleTest I F V →L_c[ℝ] W) →L[ℝ] _) := by
  ext T s
  simp [smulLeftCLM_add]

/-- Multiplication of functionals by a finite sum of functions is the sum of the multiplications. -/
theorem smulLeftDualCLM_sum {ι : Type*} (s : Finset ι) (f : ι → C^∞⟮I, M; ℝ⟯) :
    smulLeftDualCLM (∑ i ∈ s, f i) =
      (∑ i ∈ s, smulLeftDualCLM (f i) : (BundleTest I F V →L_c[ℝ] W) →L[ℝ] _) :=
  map_sum (AddMonoidHom.mk' (fun g : C^∞⟮I, M; ℝ⟯ ↦
    (smulLeftDualCLM g : (BundleTest I F V →L_c[ℝ] W) →L[ℝ] _)) smulLeftDualCLM_add) f s

/-- A smooth multiple of a point mass is a point mass: `f δ_x ℓ = f(x) δ_x ℓ`. -/
@[simp]
theorem smulLeftDualCLM_delta (f : C^∞⟮I, M; ℝ⟯) (x : M) (ℓ : V x →L[ℝ] W) :
    smulLeftDualCLM f (delta x ℓ) = f x • delta (I := I) (F := F) x ℓ := by
  ext s
  simp

end Dual

end TauCeti.BundleTest

/-! ### Multiplication in charts -/

namespace Bundle.Trivialization

open TauCeti TauCeti.BundleTest

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  (t : Trivialization F (π F V)) [MemTrivializationAtlas t]
  (c : OpenPartialHomeomorph M E)
  (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
  {g : E → ℝ}

/-- Multiplying the chart extension of a test function `φ` on the chart target by a smooth
function `f` gives the chart extension of `g φ`, for any smooth `g` equal to `f ∘ c⁻¹` where `φ`
does not vanish. -/
theorem smulLeftCLM_chartTestCLM (f : C^∞⟮I, M; ℝ⟯) (φ : 𝓓(⟨c.target, c.open_target⟩, F))
    (hg : ContDiff ℝ ∞ g) (hgφ : EqOn g (f ∘ c.symm) (support φ)) :
    smulLeftCLM f (t.chartTestCLM c hc hct φ) =
      t.chartTestCLM c hc hct (TestFunction.smulLeftCLM hg φ) := by
  ext x
  by_cases hx : x ∈ c.source
  · rw [smulLeftCLM_apply, chartTestCLM_apply_of_mem _ _ _ _ _ hx,
      chartTestCLM_apply_of_mem _ _ _ _ _ hx, TestFunction.smulLeftCLM_apply, map_smul]
    by_cases hφ : φ (c x) = 0
    · simp [hφ]
    · rw [hgφ hφ, comp_apply, c.left_inv hx]
  · simp [chartTestCLM_apply_of_notMem _ _ _ _ _ hx]

variable [FiniteDimensional ℝ F] {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **The local representative of a smooth multiple.** Over an open set `B` of the model space on
which the smooth function `g` equals `f ∘ c⁻¹`, the local representative of `f T` in the chart `c`
and the frame `t` is `g` times the local representative of `T`. -/
theorem restrictCLM_chartDistributionCLM_smulLeftDualCLM (f : C^∞⟮I, M; ℝ⟯)
    (T : BundleTest I F V →L_c[ℝ] W) {B : Opens E} (hg : ContDiff ℝ ∞ g)
    (hgB : EqOn g (f ∘ c.symm) B) :
    (Distribution.restrictCLM (t.chartDistributionCLM c hc hct (smulLeftDualCLM f T)) :
        𝓓'(B, F →L[ℝ] W)) =
      Distribution.smulLeftCLM hg
        (Distribution.restrictCLM (t.chartDistributionCLM c hc hct T)) := by
  ext φ v
  simp only [Distribution.restrictCLM_apply, Distribution.smulLeftCLM_apply,
    chartDistributionCLM_apply_apply, smulLeftDualCLM_apply]
  congr 1
  rw [smulLeftCLM_chartTestCLM t c hc hct f _ hg]
  · congr 1
    ext y
    by_cases hB : B ≤ ⟨c.target, c.open_target⟩ <;> simp [hB, smul_smul]
  · -- The test function vanishes outside the support of `φ`, which lies in `B`.
    intro y hy
    refine hgB (φ.tsupport_subset (subset_tsupport _ fun hφ ↦ hy ?_))
    by_cases hB : B ≤ ⟨c.target, c.open_target⟩ <;> simp [hB, hφ]

/-- **Smooth multiples near a point of a chart.** Near every point `y` of the target of a smooth
chart `c` with smooth inverse there are an open neighbourhood `B` of `y` in the chart target and a
smooth function `g` on the model space with `g y = f (c⁻¹ y)`, such that over `B` the local
representative of `f T` is `g` times the local representative of `T`, for every functional `T`. -/
theorem exists_forall_restrictCLM_chartDistributionCLM_smulLeftDualCLM [FiniteDimensional ℝ E]
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (f : C^∞⟮I, M; ℝ⟯) {y : E}
    (hy : y ∈ c.target) :
    ∃ (B : Opens E) (g : E → ℝ) (hg : ContDiff ℝ ∞ g), y ∈ B ∧ B ≤ ⟨c.target, c.open_target⟩ ∧
      g y = f (c.symm y) ∧ ∀ T : BundleTest I F V →L_c[ℝ] W,
        (Distribution.restrictCLM (t.chartDistributionCLM c hc hct (smulLeftDualCLM f T)) :
          𝓓'(B, F →L[ℝ] W)) =
        Distribution.smulLeftCLM hg
          (Distribution.restrictCLM (t.chartDistributionCLM c hc hct T)) := by
  -- Extend `f ∘ c⁻¹` from a neighbourhood of `y` with compact closure in the chart target.
  obtain ⟨B, hBo, hyB, hBs, hBc⟩ := exists_open_between_and_isCompact_closure isCompact_singleton
    c.open_target (singleton_subset_iff.2 hy)
  have hfc : ContDiffOn ℝ (⊤ : ℕ∞) (f ∘ c.symm) c.target :=
    contMDiffOn_iff_contDiffOn.1 (f.contMDiff.comp_contMDiffOn hcs)
  obtain ⟨g, hg, -, -, -, hgf⟩ :=
    hfc.exists_contDiff_eventuallyEq_on_isCompact hBc c.open_target hBs
  have hgB : EqOn g (f ∘ c.symm) B := fun z hz ↦ (hgf z (subset_closure hz)).eq_of_nhds
  exact ⟨⟨B, hBo⟩, g, hg, singleton_subset_iff.1 hyB, fun z hz ↦ hBs (subset_closure hz),
    hgB (singleton_subset_iff.1 hyB), fun T ↦
      t.restrictCLM_chartDistributionCLM_smulLeftDualCLM c hc hct f T hg hgB⟩

end Bundle.Trivialization
