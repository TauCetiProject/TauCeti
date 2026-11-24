/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Local Sobolev regularity of distributions on manifolds

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a finite-dimensional
real inner product space `E`, and let `T` be a real continuous linear functional on the bundle tests
`TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has a local representative on the chart target
(`Bundle.Trivialization.chartDistributionCLM`), a distribution with values in the dual of the model
fibre `F`. Its component along `v : F` (`Bundle.Trivialization.chartComponent`) is the complex
distribution `φ ↦ T (φ • v)` on the chart target, the test function `φ • v` being extended to a
bundle test through the chart and the frame.
The functional `T` is **`H^s` near `x`** (`TauCeti.BundleTest.IsLocallySobolevAt`) when, in some
such chart at `x` and frame, all these components are `H^s` near `c x`
(`Distribution.IsLocallySobolevAt`). This is the local Sobolev space `H^s_loc` of distributions
on a manifold with values in a bundle, defined pointwise; its complement is the **`H^s` singular
support** of `T` (`TauCeti.BundleTest.sobolevSingularSupport`).

The main result is that the chart and the frame do not matter: for two charts `c`, `c'` with
frames `t`, `t'` and a point `x` of both chart sources, all components in `(t', c')` are `H^s`
near `c' x` exactly when all components in `(t, c)` are `H^s` near `c x`
(`Bundle.Trivialization.forall_isLocallySobolevAt_chartComponent_iff`). Hence `T` is `H^s`
near `x` exactly when its components are `H^s` near `c x` in any chart `c` at `x` and any frame
(`TauCeti.BundleTest.isLocallySobolevAt_iff`).

## The argument

Near `c' x`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

where `κ = c ∘ c'⁻¹` is the chart transition, `G = t ∘ t'⁻¹` the change of frame, `S_{bⱼ}` the
components in `(t, c)` along a basis `(bⱼ)` of `F` and `κ^*` the pullback of distributions
(`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`). The pullback preserves local Sobolev
regularity (`Distribution.isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), and so do
smooth multiples and finite sums. Exchanging the roles of the two charts gives the converse.

## Main declarations

* `Bundle.Trivialization.forall_isLocallySobolevAt_chartComponent_iff`: local Sobolev
  regularity of all components does not depend on the chart and the frame.
* `Bundle.Trivialization.isLocallySobolevAt_chartComponent_of_basis`: the components along a basis
  of `F` control all components.
* `TauCeti.BundleTest.IsLocallySobolevAt`: the functional `T` is `H^s` near a point of `M`, and
  `TauCeti.BundleTest.isLocallySobolevAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.sobolevSingularSupport`: the `H^s` singular support, a closed subset of `M`
  (`TauCeti.BundleTest.isClosed_sobolevSingularSupport`) growing with `s`, with the rules for
  sums, differences, negatives and scalar multiples.
* `TauCeti.BundleTest.exists_forall_isLocallySobolevAt`: on a manifold without boundary every
  functional on bundle tests has a finite Sobolev order near every compact set.
* `TauCeti.BundleTest.sobolevSingularSupport_delta`,
  `TauCeti.BundleTest.sobolevSingularSupport_delta_eq_empty`: in dimension `d > 0` the point mass
  `δ_x ℓ` with `ℓ ≠ 0` has `H^s` singular support `{x}` for `s ≥ -d / 2`, and it is `H^s`
  everywhere for `s < -d / 2`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (the local Sobolev spaces `H^s_loc` on manifolds, defined chart by chart).
* M. Taylor, *Partial Differential Equations I*, second edition, Springer, 2011, Chapter 4, §3
  (Sobolev spaces on manifolds and their invariance under coordinate changes).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology CompactConvergenceCLM

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  {t t' : Trivialization F (π F V)} [MemTrivializationAtlas t] [MemTrivializationAtlas t']
  {c c' : OpenPartialHomeomorph M E}
  {hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source} {hct : c.source ⊆ t.baseSet}
  {hc' : ContMDiffOn I 𝓘(ℝ, E) ∞ c' c'.source} {hct' : c'.source ⊆ t'.baseSet}

/-- Finitely many components, along a basis of `F`, control the local Sobolev regularity of all
components. -/
theorem isLocallySobolevAt_chartComponent_of_basis {ι : Type*} [Finite ι]
    (b : Module.Basis ι ℝ F) (T : BundleTest I F V →L_c[ℝ] ℝ) {s : ℝ} {y : E} (hy : y ∈ c.target)
    (h : ∀ i, (t.chartComponent c hc hct T (b i)).IsLocallySobolevAt s y) (v : F) :
    (t.chartComponent c hc hct T v).IsLocallySobolevAt s y := by
  have := Fintype.ofFinite ι
  rw [chartComponent_eq_sum _ _ _ _ b]
  exact Distribution.IsLocallySobolevAt.sum hy fun i _ ↦ (h i).smul _

/-- If every component of the local representative in `(t, c)` is `H^s` near `κ y`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` is `H^s` near `y`. -/
private theorem isLocallySobolevAt_chartComponent_of_forall
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ) {s : ℝ}
    {y : E} (hy : y ∈ (c'.symm.trans c).source)
    (h : ∀ w, (t.chartComponent c hc hct T w).IsLocallySobolevAt s (c'.symm.trans c y)) (v : F) :
    (t'.chartComponent c' hc' hct' T v).IsLocallySobolevAt s y := by
  obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
  obtain ⟨B, hB, hBc, g, hg, hyB, hS⟩ := exists_restrictCLM_chartComponent_eq_sum (hc := hc)
    (hct := hct) (hc' := hc') (hct' := hct') hcs' he he' T v hy
  rw [← isLocallySobolevAt_restrictCLM_iff (fun z hz ↦ (hB hz).1) hyB, hS]
  exact Distribution.IsLocallySobolevAt.sum hyB fun j _ ↦
    ((isLocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff hyB).2 (h _)).smulLeftCLM (hg j)

/-- **Independence of the chart and the frame.** Let `c` and `c'` be smooth charts with smooth
inverses, with frames `t` and `t'` over their sources, and let `x` be a point of both chart
sources. All components of the local representative of `T` in `(t', c')` are `H^s` near `c' x`
exactly when all components in `(t, c)` are `H^s` near `c x`. -/
theorem forall_isLocallySobolevAt_chartComponent_iff
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {s : ℝ} {x : M} (hx : x ∈ c.source) (hx' : x ∈ c'.source) :
    (∀ v, (t'.chartComponent c' hc' hct' T v).IsLocallySobolevAt s (c' x)) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallySobolevAt s (c x) := by
  have key {t₁ t₂ : Trivialization F (π F V)} [MemTrivializationAtlas t₁]
      [MemTrivializationAtlas t₂] {c₁ c₂ : OpenPartialHomeomorph M E}
      (hc₁ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₁ c₁.source) (hct₁ : c₁.source ⊆ t₁.baseSet)
      (hc₂ : ContMDiffOn I 𝓘(ℝ, E) ∞ c₂ c₂.source) (hct₂ : c₂.source ⊆ t₂.baseSet)
      (hcs₁ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₁.symm c₁.target)
      (hcs₂ : ContMDiffOn 𝓘(ℝ, E) I ∞ c₂.symm c₂.target) (hx₁ : x ∈ c₁.source)
      (hx₂ : x ∈ c₂.source)
      (h : ∀ v, (t₁.chartComponent c₁ hc₁ hct₁ T v).IsLocallySobolevAt s (c₁ x)) (v : F) :
      (t₂.chartComponent c₂ hc₂ hct₂ T v).IsLocallySobolevAt s (c₂ x) := by
    have hy : c₂ x ∈ (c₂.symm.trans c₁).source := by
      simpa [c₂.left_inv hx₂] using ⟨c₂.map_source hx₂, hx₁⟩
    have hyx : c₂.symm.trans c₁ (c₂ x) = c₁ x := by simp [c₂.left_inv hx₂]
    exact isLocallySobolevAt_chartComponent_of_forall (t := t₁) (hc := hc₁)
      (hct := hct₁) (t' := t₂) (hc' := hc₂) (hct' := hct₂) hcs₁ hcs₂ T hy (hyx ▸ h) v
  exact ⟨key hc' hct' hc hct hcs' hcs hx' hx, key hc hct hc' hct' hcs hcs' hx hx'⟩

end Bundle.Trivialization

/-! ### Local Sobolev regularity on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **`H^s` near `x`** if, in some smooth chart `c` at `x`
with smooth inverse and some frame `t` over its source, the component `φ ↦ T (φ • v)` of the local
representative of `T` along every `v : F` is `H^s` near `c x`. The chart and the frame do not
matter (`TauCeti.BundleTest.isLocallySobolevAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never `H^s`
there. -/
def IsLocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, (t.chartComponent c hc hct T v).IsLocallySobolevAt s (c x)

/-- **Local Sobolev regularity in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `T` is `H^s` near `x` exactly when every component of
its local representative in `(t, c)` is `H^s` near `c x`. -/
theorem isLocallySobolevAt_iff {s : ℝ} (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) :
    IsLocallySobolevAt s T x ↔
      ∀ v, (t.chartComponent c hc hct T v).IsLocallySobolevAt s (c x) :=
  ⟨fun ⟨t₀, _, _, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦
    (forall_isLocallySobolevAt_chartComponent_iff (t' := t₀) (hc' := hc₀) (hct' := hct₀)
      (hc := hc) (hct := hct) hcs hcs₀ T hx hx₀).1 h,
    fun h ↦ ⟨t, inferInstance, c, hc, hcs, hct, hx, h⟩⟩

/-- Being `H^s` near `x` gets weaker as `s` decreases. -/
theorem IsLocallySobolevAt.mono {s s' : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (hs : s' ≤ s) : IsLocallySobolevAt s' T x :=
  let ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).mono hs⟩

/-- The points near which `T` is `H^s` form an open set. -/
theorem isOpen_setOf_isLocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {x : M | IsLocallySobolevAt s T x} := by
  refine isOpen_iff_mem_nhds.2 fun x ⟨t, ht, c, hc, hcs, hct, hx, h⟩ ↦ ?_
  -- Finitely many components, along a basis of `F`, determine all of them.
  set b := Module.finBasis ℝ F
  have hopen : IsOpen (c.source ∩ c ⁻¹' ⋂ j,
      {y | (t.chartComponent c hc hct T (b j)).IsLocallySobolevAt s y}) :=
    c.isOpen_inter_preimage (isOpen_iInter_of_finite fun j ↦
      Distribution.isOpen_setOf_isLocallySobolevAt _ _)
  exact Filter.mem_of_superset (hopen.mem_nhds ⟨hx, mem_iInter.2 fun j ↦ h (b j)⟩)
    fun y ⟨hy, hyj⟩ ↦ ⟨t, ht, c, hc, hcs, hct, hy,
      isLocallySobolevAt_chartComponent_of_basis b T (c.map_source hy) (mem_iInter.1 hyj)⟩

/-- A sum of functionals `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.add {s : ℝ} {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (h' : IsLocallySobolevAt s T' x) :
    IsLocallySobolevAt s (T + T') x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_add]
  exact (hT v).add ((isLocallySobolevAt_iff T' hc hcs hct hx).1 h' v)

/-- A real multiple of a functional `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.smul {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (a : ℝ) : IsLocallySobolevAt s (a • T) x := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, hT⟩ := h
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_smul]
  exact (hT v).smul _

/-- The negative of a functional `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.neg {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) : IsLocallySobolevAt s (-T) x := by
  simpa using h.smul (-1)

/-- A nonzero real multiple of `T` is `H^s` near `x` exactly when `T` is. -/
theorem isLocallySobolevAt_smul_iff {s : ℝ} {a : ℝ} (ha : a ≠ 0)
    {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallySobolevAt s (a • T) x ↔ IsLocallySobolevAt s T x :=
  ⟨fun h ↦ by simpa [smul_smul, inv_mul_cancel₀ ha] using h.smul a⁻¹, fun h ↦ h.smul a⟩

/-- The negative of `T` is `H^s` near `x` exactly when `T` is. -/
@[simp]
theorem isLocallySobolevAt_neg_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    IsLocallySobolevAt s (-T) x ↔ IsLocallySobolevAt s T x := by
  rw [← neg_one_smul ℝ T, isLocallySobolevAt_smul_iff (neg_ne_zero.2 one_ne_zero)]

/-- A difference of functionals `H^s` near `x` is `H^s` near `x`. -/
theorem IsLocallySobolevAt.sub {s : ℝ} {T T' : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    (h : IsLocallySobolevAt s T x) (h' : IsLocallySobolevAt s T' x) :
    IsLocallySobolevAt s (T - T') x := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-! ### The `H^s` singular support -/

variable (I) in
/-- The **`H^s` singular support** of a real functional `T` on bundle tests: the points of `M` near
which `T` is not `H^s`. -/
def sobolevSingularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Set M :=
  {x | ¬ IsLocallySobolevAt s T x}

@[simp]
theorem mem_sobolevSingularSupport_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    x ∈ sobolevSingularSupport I s T ↔ ¬ IsLocallySobolevAt s T x :=
  Iff.rfl

/-- The `H^s` singular support is closed. -/
theorem isClosed_sobolevSingularSupport (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsClosed (sobolevSingularSupport I s T) :=
  (isOpen_setOf_isLocallySobolevAt s T).isClosed_compl

/-- The `H^s` singular support grows with `s`. -/
theorem sobolevSingularSupport_mono {s s' : ℝ} (hs : s' ≤ s) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s' T ⊆ sobolevSingularSupport I s T :=
  fun _ hx h ↦ hx (h.mono hs)

/-- The `H^s` singular support of a sum lies in the union of the `H^s` singular supports. -/
theorem sobolevSingularSupport_add_subset (s : ℝ) (T T' : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (T + T') ⊆
      sobolevSingularSupport I s T ∪ sobolevSingularSupport I s T' := by
  intro x hx
  by_contra h
  simp only [mem_union, mem_sobolevSingularSupport_iff, not_or, not_not] at h
  exact hx (h.1.add h.2)

/-- The `H^s` singular support of a real multiple lies in the `H^s` singular support. -/
theorem sobolevSingularSupport_smul_subset (s : ℝ) (a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (a • T) ⊆ sobolevSingularSupport I s T :=
  fun _ hx h ↦ hx (h.smul a)

/-- A nonzero real multiple of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_smul (s : ℝ) {a : ℝ} (ha : a ≠ 0)
    (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (a • T) = sobolevSingularSupport I s T := by
  ext x
  simp [isLocallySobolevAt_smul_iff ha]

/-- The negative of `T` has the same `H^s` singular support as `T`. -/
@[simp]
theorem sobolevSingularSupport_neg (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (-T) = sobolevSingularSupport I s T := by
  ext x
  simp

/-- The `H^s` singular support of a difference lies in the union of the `H^s` singular
supports. -/
theorem sobolevSingularSupport_sub_subset (s : ℝ) (T T' : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevSingularSupport I s (T - T') ⊆
      sobolevSingularSupport I s T ∪ sobolevSingularSupport I s T' := by
  simpa [sub_eq_add_neg] using sobolevSingularSupport_add_subset s T (-T')

/-! ### Manifolds without boundary -/

section Boundaryless

variable [I.Boundaryless]

/-- On a manifold without boundary, the zero functional is `H^s` near every point. -/
theorem isLocallySobolevAt_zero (s : ℝ) (x : M) :
    IsLocallySobolevAt s (0 : BundleTest I F V →L_c[ℝ] ℝ) x := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine ⟨trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_zero]
  exact isLocallySobolevAt_zero_iff.2 (c.map_source hx)

/-- On a manifold without boundary, the zero functional has empty `H^s` singular support. -/
@[simp]
theorem sobolevSingularSupport_zero (s : ℝ) :
    sobolevSingularSupport I s (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun x hx ↦ hx (isLocallySobolevAt_zero s x)

/-- **Functionals on bundle tests have finite Sobolev order locally.** On a manifold without
boundary, for every compact set `K ⊆ M` there is an order `s` such that `T` is `H^s` near every
point of `K`. -/
theorem exists_forall_isLocallySobolevAt (T : BundleTest I F V →L_c[ℝ] ℝ) {K : Set M}
    (hK : IsCompact K) : ∃ s : ℝ, ∀ x ∈ K, IsLocallySobolevAt s T x := by
  -- At each point, the finitely many basis components have a common finite order.
  have hpt (x : M) : ∃ s : ℝ, IsLocallySobolevAt s T x := by
    obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
    set b := Module.finBasis ℝ F
    choose s hs using fun j ↦ Distribution.exists_forall_isLocallySobolevAt
      ((trivializationAt F V x).chartComponent c hc hct T (b j))
      (isCompact_singleton (x := c x)) (singleton_subset_iff.2 (c.map_source hx))
    refine ⟨-∑ j, |s j|, trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx,
      isLocallySobolevAt_chartComponent_of_basis b T (c.map_source hx) fun j ↦
        (hs j (c x) rfl).mono ?_⟩
    have := Finset.single_le_sum (f := fun j ↦ |s j|) (fun j _ ↦ abs_nonneg _)
      (Finset.mem_univ j)
    linarith [neg_abs_le (s j)]
  -- Patch the orders over a finite cover of `K`, using that each order holds on an open set.
  refine hK.induction_on (p := fun S ↦ ∃ s : ℝ, ∀ x ∈ S, IsLocallySobolevAt s T x)
    ⟨0, by simp⟩ (fun S S' hS ⟨s, hs⟩ ↦ ⟨s, fun x hx ↦ hs x (hS hx)⟩)
    (fun S S' ⟨s, hs⟩ ⟨s', hs'⟩ ↦ ⟨min s s', fun x hx ↦ hx.elim
      (fun hx ↦ (hs x hx).mono (min_le_left _ _)) fun hx ↦ (hs' x hx).mono (min_le_right _ _)⟩)
    fun x _ ↦ ?_
  obtain ⟨s, hs⟩ := hpt x
  exact ⟨_, mem_nhdsWithin_of_mem_nhds ((isOpen_setOf_isLocallySobolevAt s T).mem_nhds hs),
    s, fun _ hy ↦ hy⟩

/-! ### Point masses -/

/-- **Point masses are `H^s` below the critical order.** On a manifold without boundary of
dimension `d`, the point mass `δ_x ℓ` has empty `H^s` singular support for `s < -d / 2`. -/
theorem sobolevSingularSupport_delta_eq_empty {s : ℝ}
    (hs : (Module.finrank ℝ E : ℝ) < -2 * s) (x : M) (ℓ : V x →L[ℝ] ℝ) :
    sobolevSingularSupport I s (BundleTest.delta x ℓ : BundleTest I F V →L_c[ℝ] ℝ) = ∅ := by
  refine eq_empty_iff_forall_notMem.2 fun p hp ↦ hp ?_
  obtain ⟨c, hc, hcs, hct, hp⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p
  refine ⟨trivializationAt F V p, inferInstance, c, hc, hcs, hct, hp, fun v ↦ ?_⟩
  by_cases hx : x ∈ c.source
  · rw [chartComponent_delta_of_mem _ _ _ _ hx]
    exact ((notMem_sobolevSingularSupport_iff (c.map_source hp)).1
      (by simp [Distribution.sobolevSingularSupport_delta_eq_empty hs])).smul _
  · rw [chartComponent_delta_of_notMem _ _ _ _ hx]
    exact isLocallySobolevAt_zero_iff.2 (c.map_source hp)

/-- **The `H^s` singular support of a point mass.** On a manifold without boundary of positive
dimension `d`, the point mass `δ_x ℓ` with `ℓ ≠ 0` has `H^s` singular support `{x}` for
`s ≥ -d / 2`. -/
theorem sobolevSingularSupport_delta [Nontrivial E] {s : ℝ}
    (hs : -2 * s ≤ Module.finrank ℝ E) {x : M} {ℓ : V x →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    sobolevSingularSupport I s (BundleTest.delta x ℓ : BundleTest I F V →L_c[ℝ] ℝ) = {x} := by
  ext p
  obtain ⟨c, hc, hcs, hct, hp⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p
  rw [mem_sobolevSingularSupport_iff, isLocallySobolevAt_iff _ hc hcs hct hp, mem_singleton_iff]
  have hdelta (y : E) (hy : y ∈ c.target) := Distribution.sobolevSingularSupport_delta
    (Ω := ⟨c.target, c.open_target⟩) (x₀ := y) hs hy
  constructor
  · -- Away from `x`, the local representative is a multiple of a point mass elsewhere, or zero.
    intro h
    by_contra hpx
    refine h fun v ↦ ?_
    by_cases hx : x ∈ c.source
    · rw [chartComponent_delta_of_mem _ _ _ _ hx]
      refine ((notMem_sobolevSingularSupport_iff (c.map_source hp)).1 ?_).smul _
      rw [hdelta _ (c.map_source hx), mem_singleton_iff]
      exact fun h' ↦ hpx (c.injOn hp hx h')
    · rw [chartComponent_delta_of_notMem _ _ _ _ hx]
      exact isLocallySobolevAt_zero_iff.2 (c.map_source hp)
  · -- At `x`, some component is a nonzero multiple of the point mass at `c x`.
    rintro rfl h
    obtain ⟨u, hu⟩ : ∃ u, ℓ u ≠ 0 := by
      by_contra! h0
      exact hℓ (ContinuousLinearMap.ext h0)
    have hv := h ((trivializationAt F V p).continuousLinearMapAt ℝ p u)
    rw [chartComponent_delta_of_mem _ _ _ _ hp,
      (trivializationAt F V p).symmL_continuousLinearMapAt (hct hp),
      Distribution.isLocallySobolevAt_smul_iff (Complex.ofReal_ne_zero.2 hu)] at hv
    exact (notMem_sobolevSingularSupport_iff (c.map_source hp)).2 hv
      (by simp [hdelta _ (c.map_source hp)])

end Boundaryless

end TauCeti.BundleTest
