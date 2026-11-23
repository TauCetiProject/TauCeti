/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.ChangeOfVariables
public import TauCeti.Analysis.Distribution.WaveFrontSet.SingularSupport
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent
public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
public import TauCeti.Topology.VectorBundle.ZeroSection
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Topology.VectorBundle.Trivialization

/-!
# The wave front set of a functional on bundle tests

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space `E`, and let `T` be a real continuous linear functional
on the bundle tests `TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has a local representative on the chart target
(`Bundle.Trivialization.chartDistributionCLM`). Its **component along** `v : F`
(`Bundle.Trivialization.chartComponent`, in
`TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent`) is the complex distribution
`φ ↦ T (φ • v)` on the chart target, the test function `φ • v` being extended to a bundle test
through the chart and the frame.
As for vector-valued distributions (`Distribution.vectorWaveFrontSet`), `T` is microlocally smooth
in the chart at `(y, η)` when all these components are.

This file proves that this notion does not depend on the chart or the frame: for two charts
`c`, `c'` with frames `t`, `t'`, and a point `y = c' x` with `x` in both chart sources,

`S'_v` is microlocally smooth at `(y, Dκ(y)ᵀ η)` for all `v` if and only if
`S_v` is microlocally smooth at `(κ y, η)` for all `v`,

where `S_v` and `S'_v` are the components in `(t, c)` and in `(t', c')`, and `κ = c ∘ c'⁻¹` is the
chart transition (`Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff`). For
one chart and two frames the transition is the identity
(`Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff_of_chart`).

So covectors transform by the transpose of the derivative of the transition, and on a manifold
without boundary microlocal smoothness of `T` at a covector `ξ ∈ T*ₓM` is well defined: it is
microlocal smoothness of the components in any chart `c` at `x`, at `c x` in the direction of the
covector `ξ ∘ D(c⁻¹)(c x)` read in the chart (`TauCeti.BundleTest.IsMicrolocallySmoothAt`,
`TauCeti.BundleTest.isMicrolocallySmoothAt_iff`). The **wave front set** of `T`
(`TauCeti.BundleTest.waveFrontSet`) is the set of nonzero covectors of the cotangent bundle
`TauCeti.CotangentBundle I M` at which `T` is not microlocally smooth.

Multiplying `T` by a smooth function `f` multiplies its local representatives by `f` read in the
chart, so the Euclidean behaviour of the wave front set under smooth multiplication carries over:
on a manifold without boundary `WF(f T)` lies in `WF(T)` over the support of `f`, and in general
it agrees with `WF(T)` where `f ≠ 0`.

## The argument

Near `y`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

for the change of frame `G = t ∘ t'⁻¹` and a basis `(bⱼ)` of `F`
(`Bundle.Trivialization.restrictCLM_chartComponent_eq_sum`), where `κ^*` is the pullback of
distributions (`Distribution.compCLMOfOpenPartialHomeomorph`). The pullback transforms microlocal
smoothness by the transpose of `Dκ`
(`Distribution.isMicrolocallySmoothAt_compCLMOfOpenPartialHomeomorph_iff`), and smooth multiples
and finite sums preserve it. Exchanging the roles of the two charts gives the converse. On the
manifold, the chain rule `D(c⁻¹)(c x) = D(c₀⁻¹)(c₀ x) ∘ Dκ(c x)` for `κ = c₀ ∘ c⁻¹`
(`OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans`) identifies the
covectors read in two charts.

## Main declarations

* `Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff`: microlocal smoothness
  of all components does not depend on the chart and the frame, covectors transforming by the
  transpose of the derivative of the chart transition.
* `Bundle.Trivialization.forall_isMicrolocallySmoothAt_chartComponent_iff_of_chart`: in one chart,
  it does not depend on the frame.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt`: microlocal smoothness of `T` at a covector of `M`,
  and `TauCeti.BundleTest.isMicrolocallySmoothAt_iff`, its characterization in every chart and
  frame.
* `TauCeti.BundleTest.waveFrontSet`: the wave front set of `T`, a subset of the cotangent bundle,
  empty for `T = 0` on a manifold without boundary (`TauCeti.BundleTest.waveFrontSet_zero`).
* `TauCeti.BundleTest.mk_smul_mem_waveFrontSet_iff`: the wave front set is conic.
* `TauCeti.BundleTest.waveFrontSet_add_subset`, `TauCeti.BundleTest.waveFrontSet_smul`: the wave
  front set of a sum lies in the union, and nonzero real multiples do not change it.
* `TauCeti.BundleTest.singularSupport`: the singular support of `T`, the points near which `T` is
  not smooth, read in a chart and a frame; on a manifold with boundary it contains every boundary
  point. It does not depend on the chart and the frame
  (`TauCeti.BundleTest.notMem_singularSupport_iff`), and it is closed
  (`TauCeti.BundleTest.isClosed_singularSupport`).
* `TauCeti.BundleTest.proj_image_waveFrontSet`: on a manifold without boundary, the projection of
  the wave front set to `M` is the singular support.
* `TauCeti.BundleTest.waveFrontSet_delta`: the point mass `δ_x ℓ` with `ℓ ≠ 0` has wave front set
  the nonzero covectors at `x`, so its singular support is `{x}` in positive dimension
  (`TauCeti.BundleTest.singularSupport_delta`).
* `TauCeti.BundleTest.isOpen_setOf_isMicrolocallySmoothAt`: microlocal smoothness is an open
  condition on the cotangent bundle, so the wave front set is closed in the complement of the
  zero section (`TauCeti.BundleTest.isOpen_diff_waveFrontSet`).
* `TauCeti.BundleTest.waveFrontSet_smulLeftDualCLM_subset`,
  `TauCeti.BundleTest.mem_waveFrontSet_smulLeftDualCLM_iff`: the wave front set of a smooth
  multiple `f T` (`TauCeti.BundleTest.smulLeftDualCLM`) lies in that of `T` over the support of
  `f` on a manifold without boundary, with equality over the points where `f` does not vanish.

## Singular support

`T` is smooth near `x` when, in a chart `c` at `x` and a frame, all components of its local
representative are smooth functions near `c x` (`Distribution.singularSupport`). As for the wave
front set, this is meant for a manifold without boundary: at a boundary point there is no chart
into `E`, so every boundary point lies in the singular support. The Euclidean
theorem that a distribution is smooth near a point exactly when it is microlocally smooth at that
point in every nonzero direction
(`Distribution.notMem_singularSupport_iff_forall_isMicrolocallySmoothAt`) turns this into
microlocal smoothness of `T` at every nonzero covector at `x`, since the differential of the
inverse chart identifies the covectors at `x` with the vectors of `E`. The latter condition does
not mention the chart, which gives the independence of the chart and the frame, and the
projection theorem.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold, after Theorem 8.2.4) and §8.1 (the
  wave front set of a vector-valued distribution).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology InnerProduct CompactConvergenceCLM

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

/-! ### Changes of chart and frame -/

/-- If every component in `(t, c)` is microlocally smooth at `(κ y, (Dκ⁻¹(κ y))ᵀ ξ)`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` is microlocally smooth at
`(y, ξ)`. -/
private theorem isMicrolocallySmoothAt_chartComponent_of_forall
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ (c'.symm.trans c).source) {ξ : E}
    (h : ∀ w, (t.chartComponent c hc hct T w).IsMicrolocallySmoothAt (c'.symm.trans c y)
      (((fderiv ℝ (c'.symm.trans c).symm (c'.symm.trans c y))†) ξ)) (v : F) :
    (t'.chartComponent c' hc' hct' T v).IsMicrolocallySmoothAt y ξ := by
  obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
  obtain ⟨B, hB, hBc, g, hg, hyB, hS⟩ := exists_restrictCLM_chartComponent_eq_sum (hc := hc)
    (hct := hct) (hc' := hc') (hct' := hct') hcs' he he' T v hy
  rw [← isMicrolocallySmoothAt_restrictCLM_iff (fun z hz ↦ (hB hz).1) hyB, hS]
  exact IsMicrolocallySmoothAt.sum _ hyB fun j _ ↦
    ((h _).compCLMOfOpenPartialHomeomorph (c'.symm.trans c) he he' hB hBc hyB).smulLeftCLM (hg j)

/-- **Independence of the chart and the frame.** Let `c` and `c'` be smooth charts with smooth
inverses, with frames `t` and `t'` over their sources, and let `y = c' x` for a point `x` of both
chart sources. All components of the local representative of `T` in `(t', c')` are microlocally
smooth at `(y, Dκ(y)ᵀ η)`, for the chart transition `κ = c ∘ c'⁻¹`, exactly when all components
in `(t, c)` are microlocally smooth at `(κ y, η)`. -/
theorem forall_isMicrolocallySmoothAt_chartComponent_iff
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ c'.target) (hyc : c'.symm y ∈ c.source) (η : E) :
    (∀ v, (t'.chartComponent c' hc' hct' T v).IsMicrolocallySmoothAt y
      (((fderiv ℝ (c ∘ c'.symm) y)†) η)) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt (c (c'.symm y)) η := by
  have hys : y ∈ (c'.symm.trans c).source := ⟨hy, hyc⟩
  constructor
  · -- Exchange the roles of the two charts: the transition from `c` to `c'` is `κ⁻¹`.
    intro h v
    have hz : c (c'.symm y) ∈ (c.symm.trans c').source :=
      ⟨c.map_source hyc, by simpa [c.left_inv hyc] using c'.map_target hy⟩
    refine isMicrolocallySmoothAt_chartComponent_of_forall (t := t') (hc := hc') (hct := hct')
      (t' := t) (hc' := hc) (hct' := hct) hcs' hcs T hz (fun w ↦ ?_) v
    have hzy : c.symm.trans c' (c (c'.symm y)) = y := by simp [c.left_inv hyc, c'.right_inv hy]
    rw [hzy]
    exact h w
  · intro h v
    obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
    refine isMicrolocallySmoothAt_chartComponent_of_forall (t := t) (hc := hc) (hct := hct)
      (t' := t') (hc' := hc') (hct' := hct') hcs hcs' T hys (fun w ↦ ?_) v
    have hη := (c'.symm.trans c).adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_contDiffOn he
      he' (by simp) hys η
    rw [OpenPartialHomeomorph.coe_trans] at hη ⊢
    rw [hη]
    exact h w

/-- **Independence of the frame.** In a smooth chart `c` with smooth inverse, all components of
the local representative of `T` in the frame `t'` are microlocally smooth at `(y, η)` exactly when
all components in the frame `t` are. -/
theorem forall_isMicrolocallySmoothAt_chartComponent_iff_of_chart
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct' : c.source ⊆ t'.baseSet)
    (T : BundleTest I F V →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target) (η : E) :
    (∀ v, (t'.chartComponent c hc hct' T v).IsMicrolocallySmoothAt y η) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt y η := by
  have hid : fderiv ℝ (c ∘ c.symm) y = ContinuousLinearMap.id ℝ E := by
    have hc_id : c ∘ c.symm =ᶠ[𝓝 y] id := c.eventually_right_inverse hy
    rw [hc_id.fderiv_eq, fderiv_id]
  have h := forall_isMicrolocallySmoothAt_chartComponent_iff (t := t) (t' := t') (hc := hc)
    (hct := hct) (hc' := hc) (hct' := hct') hcs hcs T hy (c.map_target hy) η
  rwa [hid, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, c.right_inv hy] at h

end Bundle.Trivialization

/-! ### Microlocal smoothness on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization InnerProductSpace

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **microlocally smooth** at a covector `ξ` at `x` if,
in some smooth chart `c` at `x` with smooth inverse and some frame `t` over its source, every
component of the local representative of `T` is microlocally smooth at `c x` in the direction of
the covector `ξ ∘ D(c⁻¹)(c x)` read in the chart, identified with a vector of `E` through the inner
product. The chart and the frame do not matter (`TauCeti.BundleTest.isMicrolocallySmoothAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never
microlocally smooth there. -/
def IsMicrolocallySmoothAt (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)))

/-- **Microlocal smoothness in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `T` is microlocally smooth at the covector `ξ` at `x`
exactly when every component of its local representative in `(t, c)` is microlocally smooth at
`c x` in the direction of `ξ` read in the chart. -/
theorem isMicrolocallySmoothAt_iff (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt T x ξ ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySmoothAt (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) := by
  refine ⟨fun ⟨t₀, _, c₀, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦ ?_, fun h ↦ ⟨t, inferInstance, c, hc, hcs,
    hct, hx, h⟩⟩
  -- Transfer from the chart `c₀` of the definition to `c`, through the transition `c₀ ∘ c⁻¹`.
  have hiff := forall_isMicrolocallySmoothAt_chartComponent_iff (t := t₀) (hc := hc₀)
    (hct := hct₀) (t' := t) (hc' := hc) (hct' := hct) hcs₀ hcs T (c.map_source hx)
    (by simpa [c.left_inv hx] using hx₀) ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c₀.symm (c₀ x)))
  -- The chain rule `D(c⁻¹)(c x) = D(c₀⁻¹)(c₀ x) ∘ D(c₀ ∘ c⁻¹)(c x)` identifies the covectors.
  have hw : c x ∈ (c.symm.trans c₀).source :=
    ⟨c.map_source hx, by simpa [c.left_inv hx] using hx₀⟩
  have hwx : c.symm.trans c₀ (c x) = c₀ x := by simp [c.left_inv hx]
  have hΘ : DifferentiableAt ℝ (c.symm.trans c₀) (c x) :=
    ((OpenPartialHomeomorph.contDiffOn_symm_trans_of_contMDiffOn hc₀ hcs).differentiableOn
      (by simp)).differentiableAt ((c.symm.trans c₀).open_source.mem_nhds hw)
  have hψ : MDifferentiableAt 𝓘(ℝ, E) I c₀.symm (c.symm.trans c₀ (c x)) := by
    rw [hwx]
    exact (hcs₀.contMDiffAt (c₀.open_target.mem_nhds (c₀.map_source hx₀))).mdifferentiableAt
      (by simp)
  have hD := c.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans hw hψ hΘ
  rw [c.left_inv hx] at hiff
  intro v
  convert hiff.2 h v using 2
  -- Through the Riesz isomorphism, precomposition with the derivative of the transition is its
  -- adjoint.
  apply (toDual ℝ E).injective
  ext u
  simp only [LinearIsometryEquiv.apply_symm_apply, toDual_apply_apply, adjoint_inner_left,
    toDual_symm_apply]
  rw [hD, hwx, OpenPartialHomeomorph.coe_trans]
  exact ContinuousLinearMap.comp_apply _ _ _

variable (I) in
/-- The **wave front set** of a real functional `T` on bundle tests, for instance a distributional
section of a bundle: the nonzero covectors of `M` at which `T` is not microlocally smooth. -/
def waveFrontSet (T : BundleTest I F V →L_c[ℝ] ℝ) : Set (CotangentBundle I M) :=
  {p | p.snd ≠ 0 ∧ ¬ IsMicrolocallySmoothAt T p.proj p.snd}

@[simp]
theorem mem_waveFrontSet_iff {T : BundleTest I F V →L_c[ℝ] ℝ} {p : CotangentBundle I M} :
    p ∈ waveFrontSet I T ↔ p.snd ≠ 0 ∧ ¬ IsMicrolocallySmoothAt T p.proj p.snd :=
  Iff.rfl

/-- On a manifold without boundary, the zero functional has empty wave front set. -/
@[simp]
theorem waveFrontSet_zero [I.Boundaryless] : waveFrontSet I (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ :=
  eq_empty_iff_forall_notMem.2 fun p hp ↦ hp.2 <| by
    obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) p.proj
    refine ⟨trivializationAt F V p.proj, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
    rw [chartComponent_zero]
    exact Distribution.isMicrolocallySmoothAt_zero (c.map_source hx) _

/-! ### Conicity and linearity -/

/-- Microlocal smoothness on the manifold depends only on the ray through the covector. -/
theorem isMicrolocallySmoothAt_smul_iff {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) :
    IsMicrolocallySmoothAt T x (r • ξ) ↔ IsMicrolocallySmoothAt T x ξ := by
  have key {s : ℝ} (hs : 0 < s) {ζ : TangentSpace I x →L[ℝ] ℝ} :
      IsMicrolocallySmoothAt T x ζ → IsMicrolocallySmoothAt T x (s • ζ) := by
    rintro ⟨t, ht, c, hc, hcs, hct, hx, h⟩
    refine ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
    have hsm : (toDual ℝ E).symm ((s • ζ) ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) =
        s • (toDual ℝ E).symm (ζ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) :=
      (congrArg _ (ContinuousLinearMap.smul_comp _ _ _)).trans (map_smul _ _ _)
    rw [hsm]
    exact (Distribution.isMicrolocallySmoothAt_smul_iff hs).2 (h v)
  refine ⟨fun h ↦ ?_, key hr⟩
  simpa [smul_smul, inv_mul_cancel₀ hr.ne'] using key (inv_pos.2 hr) h

/-- The wave front set is conic: it is invariant under positive scaling of the covectors. -/
theorem mk_smul_mem_waveFrontSet_iff {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) :
    TotalSpace.mk x (r • ξ) ∈ waveFrontSet I T ↔ TotalSpace.mk x ξ ∈ waveFrontSet I T := by
  simp [isMicrolocallySmoothAt_smul_iff hr, hr.ne']

/-- The sum of two functionals microlocally smooth at a covector is microlocally smooth there. -/
theorem IsMicrolocallySmoothAt.add {S T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (hS : IsMicrolocallySmoothAt S x ξ)
    (hT : IsMicrolocallySmoothAt T x ξ) : IsMicrolocallySmoothAt (S + T) x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, hS⟩ := hS
  have hT' := (isMicrolocallySmoothAt_iff T (t := t) hc hcs hct hx ξ).1 hT
  exact ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ by simpa using (hS v).add (hT' v)⟩

/-- A real multiple of a functional microlocally smooth at a covector is microlocally smooth
there. -/
theorem IsMicrolocallySmoothAt.smul {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySmoothAt T x ξ) (a : ℝ) :
    IsMicrolocallySmoothAt (a • T) x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  exact ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ by simpa using (h v).smul (a : ℂ)⟩

/-- The wave front set of a sum lies in the union of the wave front sets. -/
theorem waveFrontSet_add_subset (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I (S + T) ⊆ waveFrontSet I S ∪ waveFrontSet I T := by
  refine fun p ⟨hp, h⟩ ↦ by_contra fun hST ↦ h ?_
  simp only [mem_union, mem_waveFrontSet_iff, not_or, not_and, not_not] at hST
  exact (hST.1 hp).add (hST.2 hp)

/-- A real multiple of `T` has wave front set contained in that of `T`. -/
theorem waveFrontSet_smul_subset (a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I (a • T) ⊆ waveFrontSet I T :=
  fun _ ⟨hp, h⟩ ↦ ⟨hp, fun hT ↦ h (hT.smul a)⟩

/-- A nonzero real multiple of `T` has the same wave front set as `T`. -/
@[simp]
theorem waveFrontSet_smul {a : ℝ} (ha : a ≠ 0) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I (a • T) = waveFrontSet I T := by
  refine (waveFrontSet_smul_subset a T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ ha] using waveFrontSet_smul_subset a⁻¹ (a • T)

/-- The negative of `T` has the same wave front set as `T`. -/
@[simp]
theorem waveFrontSet_neg (T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I (-T) = waveFrontSet I T := by
  rw [← neg_one_smul ℝ T, waveFrontSet_smul (neg_ne_zero.2 one_ne_zero)]

/-- The wave front set of a difference lies in the union of the wave front sets. -/
theorem waveFrontSet_sub_subset (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I (S - T) ⊆ waveFrontSet I S ∪ waveFrontSet I T := by
  simpa [sub_eq_add_neg] using waveFrontSet_add_subset S (-T)

omit [T2Space M] [IsManifold I ∞ M] in
/-- In a smooth chart `c` at `x` with smooth inverse, a covector `ξ` at `x` is read as the zero
vector of `E` exactly when it is zero. -/
private theorem toDual_symm_comp_mfderiv_symm_eq_zero_iff {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    {x : M} (hx : x ∈ c.source) {ξ : TangentSpace I x →L[ℝ] ℝ} :
    (toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) = 0 ↔ ξ = 0 :=
  (toDual ℝ E).symm.map_eq_zero_iff.trans
    ((OpenPartialHomeomorph.MDifferentiable.comp_mfderiv_symm_bijective
      ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hx).1.eq_iff'
      (zero_comp _))

/-! ### The singular support and the projection of the wave front set -/

section SingularSupport

variable [MeasurableSpace E] [BorelSpace E]

variable (I) in
/-- The **singular support** of a real functional `T` on bundle tests: the points `x` near which
`T` is not smooth, that is, such that in no smooth chart `c` at `x` with smooth inverse and frame
`t` over its source are all the components of the local representative of `T` smooth functions
near `c x`. The chart and the frame do not matter (`TauCeti.BundleTest.notMem_singularSupport_iff`),
and on a manifold without boundary the singular support is the projection of the wave front set
(`TauCeti.BundleTest.proj_image_waveFrontSet`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, so every boundary point lies
in the singular support, even for `T = 0`. -/
def singularSupport (T : BundleTest I F V →L_c[ℝ] ℝ) : Set M :=
  {x | ¬ ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t)
    (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, c x ∉ Distribution.singularSupport (t.chartComponent c hc hct T v)}

theorem mem_singularSupport_iff {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    x ∈ singularSupport I T ↔ ¬ ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t)
      (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
      (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet),
      x ∈ c.source ∧ ∀ v, c x ∉ Distribution.singularSupport (t.chartComponent c hc hct T v) :=
  Iff.rfl

/-- In a smooth chart `c` at `x` with smooth inverse and a frame `t` over its source, all
components of the local representative of `T` are smooth near `c x` exactly when `T` is
microlocally smooth at every nonzero covector at `x`. -/
private theorem forall_notMem_singularSupport_chartComponent_iff
    (T : BundleTest I F V →L_c[ℝ] ℝ) {t : Trivialization F (π F V)} [MemTrivializationAtlas t]
    {c : OpenPartialHomeomorph M E} (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet) {x : M}
    (hx : x ∈ c.source) :
    (∀ v, c x ∉ Distribution.singularSupport (t.chartComponent c hc hct T v)) ↔
      ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ξ ≠ 0 → IsMicrolocallySmoothAt T x ξ := by
  have hcx : c x ∈ (⟨c.target, c.open_target⟩ : Opens E) := c.map_source hx
  -- Reading covectors at `x` in the chart is a bijection onto the covectors of `E`.
  have hb := OpenPartialHomeomorph.MDifferentiable.comp_mfderiv_symm_bijective
    ⟨hc.mdifferentiableOn (by simp), hcs.mdifferentiableOn (by simp)⟩ hx
  refine ⟨fun h ξ hξ ↦ (isMicrolocallySmoothAt_iff T hc hcs hct hx ξ).2 fun v ↦
    (Distribution.notMem_singularSupport_iff_forall_isMicrolocallySmoothAt hcx).1 (h v) _
      (mt (toDual_symm_comp_mfderiv_symm_eq_zero_iff hc hcs hx).1 hξ), fun h v ↦ ?_⟩
  refine (Distribution.notMem_singularSupport_iff_forall_isMicrolocallySmoothAt hcx).2 fun η hη ↦ ?_
  obtain ⟨ξ, hξη⟩ := hb.2 (toDual ℝ E η)
  rw [← (toDual ℝ E).symm_apply_apply η, ← hξη] at hη ⊢
  have hξ : ξ ≠ 0 := mt (toDual_symm_comp_mfderiv_symm_eq_zero_iff hc hcs hx).2 hη
  exact (isMicrolocallySmoothAt_iff T hc hcs hct hx ξ).1 (h ξ hξ) v

/-- **The singular support in any chart and frame.** For a smooth chart `c` at `x` with smooth
inverse and a frame `t` over its source, `x` lies outside the singular support of `T` exactly when
every component of the local representative of `T` in `(t, c)` is a smooth function near `c x`. -/
theorem notMem_singularSupport_iff (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) :
    x ∉ singularSupport I T ↔
      ∀ v, c x ∉ Distribution.singularSupport (t.chartComponent c hc hct T v) := by
  rw [mem_singularSupport_iff, not_not]
  refine ⟨fun ⟨t₀, _, c₀, hc₀, hcs₀, hct₀, hx₀, h₀⟩ ↦ ?_, fun h ↦ ⟨t, inferInstance, c, hc, hcs,
    hct, hx, h⟩⟩
  exact (forall_notMem_singularSupport_chartComponent_iff T hc hcs hct hx).2
    ((forall_notMem_singularSupport_chartComponent_iff T hc₀ hcs₀ hct₀ hx₀).1 h₀)

/-- On a manifold without boundary, `T` is smooth near `x` exactly when it is microlocally smooth
at every nonzero covector at `x`. -/
theorem notMem_singularSupport_iff_forall_isMicrolocallySmoothAt [I.Boundaryless]
    {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M} :
    x ∉ singularSupport I T ↔
      ∀ ξ : TangentSpace I x →L[ℝ] ℝ, ξ ≠ 0 → IsMicrolocallySmoothAt T x ξ := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  rw [notMem_singularSupport_iff T hc hcs hct hx]
  exact forall_notMem_singularSupport_chartComponent_iff T hc hcs hct hx

/-- **The projection of the wave front set is the singular support** (Hörmander I, §8.2). -/
theorem proj_image_waveFrontSet [I.Boundaryless] (T : BundleTest I F V →L_c[ℝ] ℝ) :
    TotalSpace.proj '' waveFrontSet I T = singularSupport I T := by
  ext x
  rw [← not_iff_not, notMem_singularSupport_iff_forall_isMicrolocallySmoothAt]
  refine ⟨fun h ξ hξ ↦ by_contra fun hT ↦ h ⟨⟨x, ξ⟩, ⟨hξ, hT⟩, rfl⟩, ?_⟩
  rintro h ⟨p, ⟨hp, hT⟩, rfl⟩
  exact hT (h p.snd hp)

/-- On a manifold without boundary, a functional has empty singular support exactly when it has
empty wave front set. -/
theorem singularSupport_eq_empty_iff_waveFrontSet_eq_empty [I.Boundaryless]
    {T : BundleTest I F V →L_c[ℝ] ℝ} : singularSupport I T = ∅ ↔ waveFrontSet I T = ∅ := by
  rw [← proj_image_waveFrontSet, image_eq_empty]

/-- The singular support is closed. -/
theorem isClosed_singularSupport (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsClosed (singularSupport I T) := by
  refine isOpen_compl_iff.1 (isOpen_iff_mem_nhds.2 fun x hx ↦ ?_)
  rw [mem_compl_iff, mem_singularSupport_iff, not_not] at hx
  obtain ⟨t, _, c, hc, hcs, hct, hxc, h⟩ := hx
  set b := Module.finBasis ℝ F
  -- Near `c x` the finitely many components along a basis are smooth, hence so are all
  -- components, which are combinations of these.
  have hU : ∀ i, c.source ∩ c ⁻¹' ((c.target : Set E) \
      Distribution.singularSupport (t.chartComponent c hc hct T (b i))) ∈ 𝓝 x := fun i ↦
    (c.continuousOn.isOpen_inter_preimage c.open_source
      (Distribution.isOpen_diff_singularSupport _)).mem_nhds ⟨hxc, c.map_source hxc, h (b i)⟩
  filter_upwards [Filter.iInter_mem.2 hU, c.open_source.mem_nhds hxc] with y hy hyc
  refine fun hys ↦ hys ⟨t, inferInstance, c, hc, hcs, hct, hyc, fun v hv ↦ ?_⟩
  rw [t.chartComponent_eq_sum c hc hct b] at hv
  obtain ⟨i, -, hi⟩ := mem_iUnion₂.1 (Distribution.singularSupport_sum_subset _ _ hv)
  exact (mem_iInter.1 hy i).2.2 (Distribution.singularSupport_smul_subset _ _ hi)

/-- On a manifold without boundary, the zero functional has empty singular support. -/
@[simp]
theorem singularSupport_zero [I.Boundaryless] :
    singularSupport I (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ := by
  simp [singularSupport_eq_empty_iff_waveFrontSet_eq_empty]

/-- The singular support of a sum lies in the union of the singular supports. -/
theorem singularSupport_add_subset (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    singularSupport I (S + T) ⊆ singularSupport I S ∪ singularSupport I T := by
  refine fun x hx ↦ by_contra fun h ↦ ?_
  rw [mem_union, not_or] at h
  obtain ⟨t, _, c, hc, hcs, hct, hxc, hS⟩ := not_not.1 (mem_singularSupport_iff.not.1 h.1)
  have hT := (notMem_singularSupport_iff T hc hcs hct hxc).1 h.2
  refine (notMem_singularSupport_iff (S + T) hc hcs hct hxc).2 (fun v hv ↦ ?_) hx
  rw [chartComponent_add] at hv
  exact (Distribution.singularSupport_add_subset _ _ hv).elim (hS v) (hT v)

/-- A real multiple of `T` has singular support contained in that of `T`. -/
theorem singularSupport_smul_subset (a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    singularSupport I (a • T) ⊆ singularSupport I T := by
  refine fun x hx ↦ by_contra fun h ↦ ?_
  obtain ⟨t, _, c, hc, hcs, hct, hxc, hT⟩ := not_not.1 (mem_singularSupport_iff.not.1 h)
  refine (notMem_singularSupport_iff (a • T) hc hcs hct hxc).2 (fun v hv ↦ ?_) hx
  rw [chartComponent_smul] at hv
  exact hT v (Distribution.singularSupport_smul_subset _ _ hv)

/-- A nonzero real multiple of `T` has the same singular support as `T`. -/
@[simp]
theorem singularSupport_smul {a : ℝ} (ha : a ≠ 0) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    singularSupport I (a • T) = singularSupport I T := by
  refine (singularSupport_smul_subset a T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ ha] using singularSupport_smul_subset a⁻¹ (a • T)

/-- The negative of `T` has the same singular support as `T`. -/
@[simp]
theorem singularSupport_neg (T : BundleTest I F V →L_c[ℝ] ℝ) :
    singularSupport I (-T) = singularSupport I T := by
  rw [← neg_one_smul ℝ T, singularSupport_smul (neg_ne_zero.2 one_ne_zero)]

/-- The singular support of a difference lies in the union of the singular supports. -/
theorem singularSupport_sub_subset (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    singularSupport I (S - T) ⊆ singularSupport I S ∪ singularSupport I T := by
  simpa [sub_eq_add_neg] using singularSupport_add_subset S (-T)

end SingularSupport

/-! ### Point masses -/

/-- **The wave front set of a point mass.** On a manifold without boundary, the point mass
`δ_x ℓ : s ↦ ℓ (s x)` with a nonzero covector `ℓ` on the fibre `V x` has wave front set the
nonzero covectors of `M` at `x`. -/
theorem waveFrontSet_delta [I.Boundaryless] {x : M} {ℓ : V x →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    waveFrontSet I (delta (I := I) (F := F) x ℓ) = {p | p.proj = x ∧ p.snd ≠ 0} := by
  ext ⟨y, ξ⟩
  simp only [mem_waveFrontSet_iff, mem_ofPred_eq]
  obtain ⟨c, hc, hcs, hct, hy⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) y
  rw [isMicrolocallySmoothAt_iff _ hc hcs hct hy]
  -- A nonzero covector at `y` is read in the chart as a nonzero vector.
  have hne {ξ : TangentSpace I y →L[ℝ] ℝ} (hξ : ξ ≠ 0) :
      (toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c y)) ≠ 0 :=
    mt (toDual_symm_comp_mfderiv_symm_eq_zero_iff hc hcs hy).1 hξ
  refine ⟨fun ⟨hξ, hT⟩ ↦ ⟨by_contra fun hyx ↦ hT fun v ↦ ?_, hξ⟩, ?_⟩
  · -- Away from `x`, every component is microlocally smooth at `c y`.
    by_cases hx : x ∈ c.source
    · rw [chartComponent_delta_of_mem _ _ _ _ hx]
      refine not_not.1 fun h ↦ ?_
      have hmem := Distribution.waveFrontSet_smul_subset _ _ (Distribution.mem_waveFrontSet_iff.2
        ⟨c.map_source hy, hne hξ, h⟩)
      rw [Distribution.waveFrontSet_delta (c.map_source hx)] at hmem
      exact hyx (c.injOn hy hx hmem.1)
    · rw [chartComponent_delta_of_notMem _ _ _ _ hx]
      exact Distribution.isMicrolocallySmoothAt_zero (c.map_source hy) _
  · -- At `x`, the component along a vector `v` with `ℓ (t⁻¹ v) ≠ 0` is a nonzero multiple of the
    -- point mass at `c x`.
    rintro ⟨rfl, hξ⟩
    refine ⟨hξ, fun h ↦ ?_⟩
    obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hℓ
    set t := trivializationAt F V y
    have hv := h (t.continuousLinearMapAt ℝ y w)
    rw [chartComponent_delta_of_mem _ _ _ _ hy,
      t.symmL_continuousLinearMapAt (hct hy)] at hv
    have hmem : (c y, (toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c y))) ∈
        ((ℓ w : ℂ) • mapCLM ofRealCLM
          (Distribution.delta (c y) : 𝓓'(⟨c.target, c.open_target⟩, ℝ))).waveFrontSet := by
      rw [Distribution.waveFrontSet_smul (Complex.ofReal_ne_zero.2 hw),
        Distribution.waveFrontSet_delta (c.map_source hy)]
      exact ⟨rfl, hne hξ⟩
    exact (Distribution.mem_waveFrontSet_iff.1 hmem).2.2 hv

/-- On a manifold without boundary of positive dimension, the point mass `δ_x ℓ` with a nonzero
covector `ℓ` on the fibre `V x` has singular support `{x}`. -/
theorem singularSupport_delta [MeasurableSpace E] [BorelSpace E] [I.Boundaryless] [Nontrivial E]
    {x : M} {ℓ : V x →L[ℝ] ℝ} (hℓ : ℓ ≠ 0) :
    singularSupport I (delta (I := I) (F := F) x ℓ) = {x} := by
  rw [← proj_image_waveFrontSet, waveFrontSet_delta hℓ]
  obtain ⟨w, hw⟩ := exists_ne (0 : E)
  refine subset_antisymm (fun _ ⟨p, hp, h⟩ ↦ h ▸ hp.1) (singleton_subset_iff.2
    ⟨⟨x, toDual ℝ E w⟩, ⟨rfl, ?_⟩, rfl⟩)
  exact fun h0 ↦ hw ((toDual ℝ E).map_eq_zero_iff.1 h0)

/-! ### Closedness of the wave front set -/

/-- **Microlocal smoothness is an open condition.** The covectors at which a real functional on
bundle tests is microlocally smooth form an open subset of the cotangent bundle. -/
theorem isOpen_setOf_isMicrolocallySmoothAt (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {p : CotangentBundle I M | IsMicrolocallySmoothAt T p.proj p.snd} := by
  refine isOpen_iff_mem_nhds.2 fun p₀ ⟨t, _, c, hc, hcs, hct, hx₀, h⟩ ↦ ?_
  have hsrc : ∀ᶠ p : CotangentBundle I M in 𝓝 p₀, p.proj ∈ c.source :=
    (FiberBundle.continuous_proj _ _).continuousAt.preimage_mem_nhds
      (c.open_source.mem_nhds hx₀)
  -- A covector `p` read in the chart `c`: its base point and its direction in `E`.
  let Φ : CotangentBundle I M → E × E := fun p ↦
    (c p.proj, (toDual ℝ E).symm (p.snd ∘L mfderiv 𝓘(ℝ, E) I c.symm (c p.proj)))
  have hΦ : ContinuousAt Φ p₀ := by
    refine ((c.continuousAt hx₀).comp (FiberBundle.continuous_proj _ _).continuousAt).prodMk
      ((toDual ℝ E).symm.continuous.continuousAt.comp (continuousAt_clm_apply.2 fun e ↦ ?_))
    -- Pair the covector with the image of the constant tangent vector `e` at `c p.proj` under
    -- the differential of `c⁻¹`, rewriting the covector over the base point `c⁻¹ (c p.proj)`.
    have hΨ : ContinuousAt (fun p : CotangentBundle I M ↦
        (TotalSpace.mk' (E →L[ℝ] ℝ) (c.symm (c p.proj)) p.snd : CotangentBundle I M)) p₀ :=
      continuousAt_id.congr <| hsrc.mono fun p hp ↦ CotangentBundle.ext (z := p)
        (w := TotalSpace.mk' (E →L[ℝ] ℝ) (c.symm (c p.proj)) p.snd) (c.left_inv hp).symm
        fun _ ↦ rfl
    have hv : ContinuousAt (fun p : CotangentBundle I M ↦
        ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm (c p.proj, e))) p₀ :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, E)).symm.continuous.continuousAt.comp
        (((c.continuousAt hx₀).comp
          (FiberBundle.continuous_proj _ _).continuousAt).prodMk continuousAt_const)
    have hf : ContMDiffAt 𝓘(ℝ, E) I 1 c.symm (c p₀.proj) :=
      (hcs.contMDiffAt (c.open_target.mem_nhds (c.map_source hx₀))).of_le (by simp)
    -- The base point and the vector of `(c p.proj, e)` in the tangent bundle of `E` are
    -- `c p.proj` and `e` by definition of `tangentBundleModelSpaceHomeomorph`.
    exact CotangentBundle.continuousAt_snd_apply_mfderiv (f := c.symm) (hΨ := hΨ) (hv := hv)
      (hf := hf) (hΨv := fun _ ↦ rfl)
  -- In a basis of `F`, finitely many components are microlocally smooth near `Φ p₀`.
  let b := Module.finBasis ℝ F
  have hb : ∀ᶠ p in 𝓝 p₀, ∀ i, (t.chartComponent c hc hct T (b i)).IsMicrolocallySmoothAt
      (Φ p).1 (Φ p).2 :=
    eventually_all.2 fun i ↦
      hΦ.eventually ((Distribution.isOpen_setOf_isMicrolocallySmoothAt _).mem_nhds (h (b i)))
  filter_upwards [hsrc, hb] with p hp hpb
  refine ⟨t, inferInstance, c, hc, hcs, hct, hp, fun v ↦ ?_⟩
  rw [t.chartComponent_eq_sum c hc hct b]
  exact Distribution.IsMicrolocallySmoothAt.sum _ (c.map_source hp) fun i _ ↦ (hpb i).smul _

/-- **The wave front set is closed** in the complement of the zero section of the cotangent
bundle. -/
theorem isOpen_diff_waveFrontSet (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen (zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) \
      waveFrontSet I T) := by
  have h : zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) \
      waveFrontSet I T = zeroSectionCompl (E →L[ℝ] ℝ) (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) ∩
        {p | IsMicrolocallySmoothAt T p.proj p.snd} := by
    ext p
    simp only [Set.mem_sdiff, mem_zeroSectionCompl, mem_waveFrontSet_iff, mem_inter_iff,
      mem_ofPred_eq]
    tauto
  rw [h]
  exact (isOpen_zeroSectionCompl _ _).inter (isOpen_setOf_isMicrolocallySmoothAt T)

/-! ### Multiplication by smooth functions -/

section SmulLeft

/-- If over an open set `B` the local representative of `S` is `g` times that of `T`, then so are
its components. -/
private theorem restrictCLM_chartComponent_eq_smulLeftCLM {t : Trivialization F (π F V)}
    [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hct : c.source ⊆ t.baseSet)
    {S T : BundleTest I F V →L_c[ℝ] ℝ} {B : Opens E} {g : E → ℝ} (hg : ContDiff ℝ ∞ g)
    (h : (restrictCLM (t.chartDistributionCLM c hc hct S) : 𝓓'(B, F →L[ℝ] ℝ)) =
      Distribution.smulLeftCLM hg (restrictCLM (t.chartDistributionCLM c hc hct T))) (v : F) :
    (restrictCLM (t.chartComponent c hc hct S v) : 𝓓'(B, ℂ)) =
      Distribution.smulLeftCLM hg (restrictCLM (t.chartComponent c hc hct T v)) := by
  ext φ
  have h := congr($h φ v)
  simp only [restrictCLM_apply, chartDistributionCLM_apply_apply,
    Distribution.smulLeftCLM_apply] at h
  simp [h]

/-- A smooth multiple `f T` of a functional microlocally smooth at a covector `ξ` is microlocally
smooth at `ξ`. -/
theorem IsMicrolocallySmoothAt.smulLeftDualCLM {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySmoothAt T x ξ) (f : C^∞⟮I, M; ℝ⟯) :
    IsMicrolocallySmoothAt (smulLeftDualCLM f T) x ξ := by
  obtain ⟨t, _, c, hc, hcs, hct, hx, h⟩ := h
  obtain ⟨B, g, hg, hyB, hBt, -, hB⟩ :=
    t.exists_forall_restrictCLM_chartDistributionCLM_smulLeftDualCLM (W := ℝ) c hc hct hcs f
      (c.map_source hx)
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [← isMicrolocallySmoothAt_restrictCLM_iff hBt hyB,
    restrictCLM_chartComponent_eq_smulLeftCLM hc hct hg (hB T)]
  exact ((isMicrolocallySmoothAt_restrictCLM_iff hBt hyB).2 (h v)).smulLeftCLM hg

/-- Where `f` does not vanish, a smooth multiple `f T` is microlocally smooth exactly where `T`
is. -/
theorem isMicrolocallySmoothAt_smulLeftDualCLM_iff {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {f : C^∞⟮I, M; ℝ⟯} (hfx : f x ≠ 0) :
    IsMicrolocallySmoothAt (smulLeftDualCLM f T) x ξ ↔ IsMicrolocallySmoothAt T x ξ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.smulLeftDualCLM f⟩
  obtain ⟨t, _, c, hc, hcs, hct, hx, h⟩ := h
  obtain ⟨B, g, hg, hyB, hBt, hgy, hB⟩ :=
    t.exists_forall_restrictCLM_chartDistributionCLM_smulLeftDualCLM (W := ℝ) c hc hct hcs f
      (c.map_source hx)
  have hgx : g (c x) ≠ 0 := by rwa [hgy, c.left_inv hx]
  refine ⟨t, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [← isMicrolocallySmoothAt_restrictCLM_iff hBt hyB,
    ← Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff hg hgx,
    ← restrictCLM_chartComponent_eq_smulLeftCLM hc hct hg (hB T),
    isMicrolocallySmoothAt_restrictCLM_iff hBt hyB]
  exact h v

/-- On a manifold without boundary, a smooth multiple `f T` is microlocally smooth at every
covector at a point outside the support of `f`. -/
theorem isMicrolocallySmoothAt_smulLeftDualCLM_of_notMem_tsupport [I.Boundaryless]
    (T : BundleTest I F V →L_c[ℝ] ℝ) {f : C^∞⟮I, M; ℝ⟯} {x : M} (hx : x ∉ tsupport f)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySmoothAt (smulLeftDualCLM f T) x ξ := by
  obtain ⟨c, hc, hcs, hct, hxc⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  -- Near `c x` the function `f ∘ c⁻¹` vanishes, so the local representative of `f T` does.
  let B : Opens E := ⟨c.target ∩ c.symm ⁻¹' (tsupport f)ᶜ,
    c.isOpen_inter_preimage_symm (isClosed_tsupport f).isOpen_compl⟩
  have hyB : c x ∈ B := ⟨c.map_source hxc, by simpa [c.left_inv hxc] using hx⟩
  have hBt : B ≤ ⟨c.target, c.open_target⟩ := fun _ hz ↦ hz.1
  have hgB : EqOn (fun _ ↦ (0 : ℝ)) (f ∘ c.symm) B := fun z hz ↦
    (image_eq_zero_of_notMem_tsupport hz.2).symm
  refine ⟨trivializationAt F V x, inferInstance, c, hc, hcs, hct, hxc, fun v ↦ ?_⟩
  rw [← isMicrolocallySmoothAt_restrictCLM_iff hBt hyB,
    restrictCLM_chartComponent_eq_smulLeftCLM hc hct contDiff_const
      ((trivializationAt F V x).restrictCLM_chartDistributionCLM_smulLeftDualCLM c hc hct f T
        contDiff_const hgB)]
  convert Distribution.isMicrolocallySmoothAt_zero hyB _
  ext φ
  simp

/-- **Smooth multiplication** (Hörmander I, §8.1 and §8.2). On a manifold without boundary, the
wave front set of a smooth multiple `f T` lies in the wave front set of `T`, over the support of
`f`. -/
theorem waveFrontSet_smulLeftDualCLM_subset [I.Boundaryless] (f : C^∞⟮I, M; ℝ⟯)
    (T : BundleTest I F V →L_c[ℝ] ℝ) :
    waveFrontSet I (smulLeftDualCLM f T) ⊆ waveFrontSet I T ∩ {p | p.proj ∈ tsupport f} :=
  fun p ⟨hp, hT⟩ ↦ ⟨⟨hp, fun h ↦ hT (h.smulLeftDualCLM f)⟩, by_contra fun hx ↦
    hT (isMicrolocallySmoothAt_smulLeftDualCLM_of_notMem_tsupport T hx p.snd)⟩

/-- Over the points where `f` does not vanish, a smooth multiple `f T` has the same wave front set
as `T`. -/
theorem mem_waveFrontSet_smulLeftDualCLM_iff {T : BundleTest I F V →L_c[ℝ] ℝ}
    {f : C^∞⟮I, M; ℝ⟯} {p : CotangentBundle I M} (hf : f p.proj ≠ 0) :
    p ∈ waveFrontSet I (smulLeftDualCLM f T) ↔ p ∈ waveFrontSet I T := by
  simp [isMicrolocallySmoothAt_smulLeftDualCLM_iff hf]

/-- Multiplying by a smooth function that vanishes nowhere over the wave front set does not change
the wave front set. -/
theorem waveFrontSet_smulLeftDualCLM_of_forall_mem_ne_zero {f : C^∞⟮I, M; ℝ⟯}
    (T : BundleTest I F V →L_c[ℝ] ℝ) (hf : ∀ p ∈ waveFrontSet I T, f p.proj ≠ 0) :
    waveFrontSet I (smulLeftDualCLM f T) = waveFrontSet I T :=
  Subset.antisymm (fun _ ⟨hp, hT⟩ ↦ ⟨hp, fun h ↦ hT (h.smulLeftDualCLM f)⟩)
    fun p hp ↦ (mem_waveFrontSet_smulLeftDualCLM_iff (hf p hp)).2 hp

/-- Multiplying by a smooth function that vanishes nowhere does not change the wave front set. -/
theorem waveFrontSet_smulLeftDualCLM_of_ne_zero {f : C^∞⟮I, M; ℝ⟯}
    (T : BundleTest I F V →L_c[ℝ] ℝ) (hf : ∀ x, f x ≠ 0) :
    waveFrontSet I (smulLeftDualCLM f T) = waveFrontSet I T :=
  waveFrontSet_smulLeftDualCLM_of_forall_mem_ne_zero T fun p _ ↦ hf p.proj

end SmulLeft

end TauCeti.BundleTest
