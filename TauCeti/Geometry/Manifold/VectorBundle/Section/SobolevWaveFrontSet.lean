/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.ChangeOfVariables
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Localization
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# The Sobolev wave front set of a functional on bundle tests

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space `E`, and let `T` be a real continuous linear functional
on the bundle tests `TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has components along the vectors `v` of the model fibre `F`
(`Bundle.Trivialization.chartComponent`), complex distributions on the chart target. As for the
wave front set (`TauCeti.BundleTest.waveFrontSet`), `T` is **microlocally `H^s`** in the chart at
`(y, η)` when all these components are microlocally `H^s` there
(`Distribution.IsMicrolocallySobolevAt`).

This file proves that this notion does not depend on the chart or the frame: for two charts
`c`, `c'` with frames `t`, `t'`, and a point `y = c' x` with `x` in both chart sources,

`S'_v` is microlocally `H^s` at `(y, Dκ(y)ᵀ η)` for all `v` if and only if
`S_v` is microlocally `H^s` at `(κ y, η)` for all `v`,

where `S_v` and `S'_v` are the components in `(t, c)` and in `(t', c')`, and `κ = c ∘ c'⁻¹` is the
chart transition (`Bundle.Trivialization.forall_isMicrolocallySobolevAt_chartComponent_iff`).
So microlocal `H^s` regularity of `T` at a covector `ξ ∈ T*ₓM` is well defined on a manifold
without boundary (`TauCeti.BundleTest.IsMicrolocallySobolevAt`,
`TauCeti.BundleTest.isMicrolocallySobolevAt_iff`), and the **`H^s` wave front set** of `T`
(`TauCeti.BundleTest.sobolevWaveFrontSet`) is the set of nonzero covectors of the cotangent bundle
`TauCeti.CotangentBundle I M` at which `T` is not microlocally `H^s`. It is conic, grows with `s`,
lies in the wave front set, and the `H^s` wave front set of a sum lies in the union.

## The argument

The argument is that for the wave front set, with microlocal `H^s` regularity in place of
microlocal smoothness. Near `y`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`

for smooth functions `gⱼ` built from the change of frame and the Jacobian of `κ`, and a basis
`(bⱼ)` of `F` (`Bundle.Trivialization.exists_restrictCLM_chartComponent_eq_sum`), where `κ^*` is the
pullback of distributions (`Distribution.compCLMOfOpenPartialHomeomorph`). The pullback transforms
microlocal `H^s` regularity by the transpose of `Dκ`
(`Distribution.isMicrolocallySobolevAt_compCLMOfOpenPartialHomeomorph_iff`), and smooth multiples
and finite sums preserve it. Exchanging the roles of the two charts gives the converse.

## Main declarations

* `Bundle.Trivialization.forall_isMicrolocallySobolevAt_chartComponent_iff`: microlocal `H^s`
  regularity of all components does not depend on the chart and the frame, covectors transforming
  by the transpose of the derivative of the chart transition.
* `Bundle.Trivialization.forall_isMicrolocallySobolevAt_chartComponent_iff_of_chart`: in one
  chart, it does not depend on the frame.
* `TauCeti.BundleTest.IsMicrolocallySobolevAt`: microlocal `H^s` regularity of `T` at a covector
  of `M`, with its defining property `TauCeti.BundleTest.isMicrolocallySobolevAt_def`, and
  `TauCeti.BundleTest.isMicrolocallySobolevAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.IsMicrolocallySmoothAt.isMicrolocallySobolevAt`,
  `TauCeti.BundleTest.IsMicrolocallySobolevAt.mono`,
  `TauCeti.BundleTest.IsMicrolocallySobolevAt.add`,
  `TauCeti.BundleTest.IsMicrolocallySobolevAt.smul`: microlocal smoothness implies microlocal
  `H^s` regularity, which implies `H^r` regularity for `r ≤ s` and is preserved by sums and real
  multiples.
* `TauCeti.BundleTest.sobolevWaveFrontSet`: the `H^s` wave front set of `T`, a subset of the
  cotangent bundle.
* `TauCeti.BundleTest.mk_smul_mem_sobolevWaveFrontSet_iff`: the `H^s` wave front set is conic.
* `TauCeti.BundleTest.sobolevWaveFrontSet_mono`,
  `TauCeti.BundleTest.sobolevWaveFrontSet_subset_waveFrontSet`: it grows with `s` and lies in the
  wave front set.
* `TauCeti.BundleTest.sobolevWaveFrontSet_add_subset`,
  `TauCeti.BundleTest.sobolevWaveFrontSet_smul`: the `H^s` wave front set of a sum lies in the
  union, and nonzero real multiples do not change it.

## References

* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (the `H^s` wave front set, and its invariance under diffeomorphisms).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold).
-/

public section

noncomputable section

open Set Filter Function TopologicalSpace Complex Distribution ContinuousLinearMap
open scoped Manifold ContDiff Distributions Topology InnerProduct CompactConvergenceCLM

namespace Bundle.Trivialization

open TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
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

/-- If every component in `(t, c)` is microlocally `H^s` at `(κ y, (Dκ⁻¹(κ y))ᵀ ξ)`, for the
transition `κ = c ∘ c'⁻¹`, then every component in `(t', c')` is microlocally `H^s` at
`(y, ξ)`. -/
private theorem isMicrolocallySobolevAt_chartComponent_of_forall {s : ℝ}
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ (c'.symm.trans c).source) {ξ : E}
    (h : ∀ w, (t.chartComponent c hc hct T w).IsMicrolocallySobolevAt s (c'.symm.trans c y)
      (((fderiv ℝ (c'.symm.trans c).symm (c'.symm.trans c y))†) ξ)) (v : F) :
    (t'.chartComponent c' hc' hct' T v).IsMicrolocallySobolevAt s y ξ := by
  obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
  obtain ⟨B, hB, hBc, g, hg, hyB, hS⟩ := exists_restrictCLM_chartComponent_eq_sum (hc := hc)
    (hct := hct) (hc' := hc') (hct' := hct') hcs' he he' T v hy
  rw [← isMicrolocallySobolevAt_restrictCLM_iff (fun z hz ↦ (hB hz).1) hyB, hS]
  exact IsMicrolocallySobolevAt.sum _ hyB fun j _ ↦
    ((h _).compCLMOfOpenPartialHomeomorph hyB).smulLeftCLM (hg j)

/-- **Independence of the chart and the frame.** Let `c` and `c'` be smooth charts with smooth
inverses, with frames `t` and `t'` over their sources, and let `y = c' x` for a point `x` of both
chart sources. All components of the local representative of `T` in `(t', c')` are microlocally
`H^s` at `(y, Dκ(y)ᵀ η)`, for the chart transition `κ = c ∘ c'⁻¹`, exactly when all components
in `(t, c)` are microlocally `H^s` at `(κ y, η)`. -/
theorem forall_isMicrolocallySobolevAt_chartComponent_iff {s : ℝ}
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ c'.target) (hyc : c'.symm y ∈ c.source) (η : E) :
    (∀ v, (t'.chartComponent c' hc' hct' T v).IsMicrolocallySobolevAt s y
      (((fderiv ℝ (c ∘ c'.symm) y)†) η)) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySobolevAt s (c (c'.symm y)) η := by
  have hys : y ∈ (c'.symm.trans c).source := ⟨hy, hyc⟩
  constructor
  · -- Exchange the roles of the two charts: the transition from `c` to `c'` is `κ⁻¹`.
    intro h v
    have hz : c (c'.symm y) ∈ (c.symm.trans c').source :=
      ⟨c.map_source hyc, by simpa [c.left_inv hyc] using c'.map_target hy⟩
    refine isMicrolocallySobolevAt_chartComponent_of_forall (t := t') (hc := hc') (hct := hct')
      (t' := t) (hc' := hc) (hct' := hct) hcs' hcs T hz (fun w ↦ ?_) v
    have hzy : c.symm.trans c' (c (c'.symm y)) = y := by simp [c.left_inv hyc, c'.right_inv hy]
    rw [hzy]
    exact h w
  · intro h v
    obtain ⟨he, he'⟩ :=
      OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
    refine isMicrolocallySobolevAt_chartComponent_of_forall (t := t) (hc := hc) (hct := hct)
      (t' := t') (hc' := hc') (hct' := hct') hcs hcs' T hys (fun w ↦ ?_) v
    have hη := (c'.symm.trans c).adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_contDiffOn he
      he' (by simp) hys η
    rw [OpenPartialHomeomorph.coe_trans] at hη ⊢
    rw [hη]
    exact h w

/-- **Independence of the frame.** In a smooth chart `c` with smooth inverse, all components of
the local representative of `T` in the frame `t'` are microlocally `H^s` at `(y, η)` exactly when
all components in the frame `t` are. -/
theorem forall_isMicrolocallySobolevAt_chartComponent_iff_of_chart {s : ℝ}
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct' : c.source ⊆ t'.baseSet)
    (T : BundleTest I F V →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target) (η : E) :
    (∀ v, (t'.chartComponent c hc hct' T v).IsMicrolocallySobolevAt s y η) ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySobolevAt s y η := by
  have hid : fderiv ℝ (c ∘ c.symm) y = ContinuousLinearMap.id ℝ E := by
    have hc_id : c ∘ c.symm =ᶠ[𝓝 y] id := c.eventually_right_inverse hy
    rw [hc_id.fderiv_eq, fderiv_id]
  have h := forall_isMicrolocallySobolevAt_chartComponent_iff (s := s) (t := t) (t' := t')
    (hc := hc) (hct := hct) (hc' := hc) (hct' := hct') hcs hcs T hy (c.map_target hy) η
  rwa [hid, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, c.right_inv hy] at h

end Bundle.Trivialization

/-! ### Microlocal Sobolev regularity on the manifold -/

namespace TauCeti.BundleTest

open Bundle Bundle.Trivialization InnerProductSpace

variable {E H M F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- A real functional `T` on bundle tests is **microlocally `H^s`** at a covector `ξ` at `x` if,
in some smooth chart `c` at `x` with smooth inverse and some frame `t` over its source, every
component of the local representative of `T` is microlocally `H^s` at `c x` in the direction of
the covector `ξ ∘ D(c⁻¹)(c x)` read in the chart, identified with a vector of `E` through the inner
product. The chart and the frame do not matter
(`TauCeti.BundleTest.isMicrolocallySobolevAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` is never
microlocally `H^s` there. -/
def IsMicrolocallySobolevAt (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySobolevAt s (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)))

/-- The defining property of `TauCeti.BundleTest.IsMicrolocallySobolevAt`: microlocal `H^s`
regularity of all components in some smooth chart at `x` with smooth inverse and some frame over
its source. -/
theorem isMicrolocallySobolevAt_def {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} :
    IsMicrolocallySobolevAt s T x ξ ↔
      ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t)
        (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
        (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet),
        x ∈ c.source ∧ ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySobolevAt s (c x)
          ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) :=
  Iff.rfl

/-- **Microlocal Sobolev regularity in any chart and frame.** For a smooth chart `c` at `x` with
smooth inverse and a frame `t` over its source, `T` is microlocally `H^s` at the covector `ξ` at
`x` exactly when every component of its local representative in `(t, c)` is microlocally `H^s`
at `c x` in the direction of `ξ` read in the chart. -/
theorem isMicrolocallySobolevAt_iff {s : ℝ} (T : BundleTest I F V →L_c[ℝ] ℝ)
    {t : Trivialization F (π F V)} [MemTrivializationAtlas t] {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet) {x : M} (hx : x ∈ c.source) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallySobolevAt s T x ξ ↔
      ∀ v, (t.chartComponent c hc hct T v).IsMicrolocallySobolevAt s (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) := by
  refine ⟨fun ⟨t₀, _, c₀, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦ ?_, fun h ↦ ⟨t, inferInstance, c, hc, hcs,
    hct, hx, h⟩⟩
  -- Transfer from the chart `c₀` of the definition to `c`, through the transition `c₀ ∘ c⁻¹`.
  have hiff := forall_isMicrolocallySobolevAt_chartComponent_iff (s := s) (t := t₀) (hc := hc₀)
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

/-- A functional microlocally smooth at a covector is microlocally `H^s` there, for every `s`. -/
theorem IsMicrolocallySmoothAt.isMicrolocallySobolevAt {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySmoothAt T x ξ) (s : ℝ) :
    IsMicrolocallySobolevAt s T x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := isMicrolocallySmoothAt_def.1 h
  exact ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).isMicrolocallySobolevAt s⟩

/-- Being microlocally `H^s` at a covector implies being microlocally `H^r` there for `r ≤ s`. -/
theorem IsMicrolocallySobolevAt.mono {s r : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySobolevAt s T x ξ) (hrs : r ≤ s) :
    IsMicrolocallySobolevAt r T x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  exact ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ (h v).mono hrs⟩

/-- Microlocal `H^s` regularity on the manifold depends only on the ray through the covector. -/
theorem isMicrolocallySobolevAt_smul_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) :
    IsMicrolocallySobolevAt s T x (r • ξ) ↔ IsMicrolocallySobolevAt s T x ξ := by
  have key {a : ℝ} (ha : 0 < a) {ζ : TangentSpace I x →L[ℝ] ℝ} :
      IsMicrolocallySobolevAt s T x ζ → IsMicrolocallySobolevAt s T x (a • ζ) := by
    rintro ⟨t, ht, c, hc, hcs, hct, hx, h⟩
    refine ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
    have hsm : (toDual ℝ E).symm ((a • ζ) ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) =
        a • (toDual ℝ E).symm (ζ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) :=
      (congrArg _ (ContinuousLinearMap.smul_comp _ _ _)).trans (map_smul _ _ _)
    rw [hsm]
    exact (Distribution.isMicrolocallySobolevAt_smul_iff ha).2 (h v)
  refine ⟨fun h ↦ ?_, key hr⟩
  simpa [smul_smul, inv_mul_cancel₀ hr.ne'] using key (inv_pos.2 hr) h

/-- The sum of two functionals microlocally `H^s` at a covector is microlocally `H^s` there. -/
theorem IsMicrolocallySobolevAt.add {s : ℝ} {S T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (hS : IsMicrolocallySobolevAt s S x ξ)
    (hT : IsMicrolocallySobolevAt s T x ξ) : IsMicrolocallySobolevAt s (S + T) x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, hS⟩ := hS
  have hT' := (isMicrolocallySobolevAt_iff T (t := t) hc hcs hct hx ξ).1 hT
  exact ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ by simpa using (hS v).add (hT' v)⟩

/-- A real multiple of a functional microlocally `H^s` at a covector is microlocally `H^s`
there. -/
theorem IsMicrolocallySobolevAt.smul {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} (h : IsMicrolocallySobolevAt s T x ξ) (a : ℝ) :
    IsMicrolocallySobolevAt s (a • T) x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  exact ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ by simpa using (h v).smul (a : ℂ)⟩

/-! ### The Sobolev wave front set -/

variable (I) in
/-- The **`H^s` wave front set** of a real functional `T` on bundle tests, for instance a
distributional section of a bundle: the nonzero covectors of `M` at which `T` is not microlocally
`H^s`. -/
def sobolevWaveFrontSet (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Set (CotangentBundle I M) :=
  {p | p.snd ≠ 0 ∧ ¬ IsMicrolocallySobolevAt s T p.proj p.snd}

@[simp]
theorem mem_sobolevWaveFrontSet_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ}
    {p : CotangentBundle I M} :
    p ∈ sobolevWaveFrontSet I s T ↔ p.snd ≠ 0 ∧ ¬ IsMicrolocallySobolevAt s T p.proj p.snd :=
  Iff.rfl

/-- The `H^s` wave front set is conic: it is invariant under positive scaling of the
covectors. -/
theorem mk_smul_mem_sobolevWaveFrontSet_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} {x : M}
    {ξ : TangentSpace I x →L[ℝ] ℝ} {r : ℝ} (hr : 0 < r) :
    TotalSpace.mk x (r • ξ) ∈ sobolevWaveFrontSet I s T ↔
      TotalSpace.mk x ξ ∈ sobolevWaveFrontSet I s T := by
  simp [isMicrolocallySobolevAt_smul_iff hr, hr.ne']

/-- The `H^s` wave front set grows with `s`. -/
theorem sobolevWaveFrontSet_mono {s r : ℝ} (hrs : r ≤ s) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I r T ⊆ sobolevWaveFrontSet I s T :=
  fun _ ⟨hp, h⟩ ↦ ⟨hp, fun h' ↦ h (h'.mono hrs)⟩

/-- The `H^s` wave front set lies in the wave front set. -/
theorem sobolevWaveFrontSet_subset_waveFrontSet (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s T ⊆ waveFrontSet I T :=
  fun _ ⟨hp, h⟩ ↦ mem_waveFrontSet_iff.2 ⟨hp, fun h' ↦ h (h'.isMicrolocallySobolevAt s)⟩

/-- The `H^s` wave front set of a sum lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_add_subset (s : ℝ) (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (S + T) ⊆ sobolevWaveFrontSet I s S ∪ sobolevWaveFrontSet I s T := by
  refine fun p ⟨hp, h⟩ ↦ by_contra fun hST ↦ h ?_
  simp only [mem_union, mem_sobolevWaveFrontSet_iff, not_or, not_and, not_not] at hST
  exact (hST.1 hp).add (hST.2 hp)

/-- A real multiple of `T` has `H^s` wave front set contained in that of `T`. -/
theorem sobolevWaveFrontSet_smul_subset (s a : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (a • T) ⊆ sobolevWaveFrontSet I s T :=
  fun _ ⟨hp, h⟩ ↦ ⟨hp, fun hT ↦ h (hT.smul a)⟩

/-- A nonzero real multiple of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_smul (s : ℝ) {a : ℝ} (ha : a ≠ 0) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (a • T) = sobolevWaveFrontSet I s T := by
  refine (sobolevWaveFrontSet_smul_subset s a T).antisymm ?_
  simpa [smul_smul, inv_mul_cancel₀ ha] using sobolevWaveFrontSet_smul_subset s a⁻¹ (a • T)

/-- The negative of `T` has the same `H^s` wave front set as `T`. -/
@[simp]
theorem sobolevWaveFrontSet_neg (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (-T) = sobolevWaveFrontSet I s T := by
  rw [← neg_one_smul ℝ T, sobolevWaveFrontSet_smul s (neg_ne_zero.2 one_ne_zero)]

/-- The `H^s` wave front set of a difference lies in the union of the `H^s` wave front sets. -/
theorem sobolevWaveFrontSet_sub_subset (s : ℝ) (S T : BundleTest I F V →L_c[ℝ] ℝ) :
    sobolevWaveFrontSet I s (S - T) ⊆ sobolevWaveFrontSet I s S ∪ sobolevWaveFrontSet I s T := by
  simpa [sub_eq_add_neg] using sobolevWaveFrontSet_add_subset s S (-T)

/-- On a manifold without boundary, the zero functional has empty `H^s` wave front set. -/
@[simp]
theorem sobolevWaveFrontSet_zero [I.Boundaryless] (s : ℝ) :
    sobolevWaveFrontSet I s (0 : BundleTest I F V →L_c[ℝ] ℝ) = ∅ :=
  subset_empty_iff.1 (waveFrontSet_zero (I := I) (F := F) (V := V) ▸
    sobolevWaveFrontSet_subset_waveFrontSet s 0)

end TauCeti.BundleTest
