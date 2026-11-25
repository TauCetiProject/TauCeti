/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.MicrolocalRegularity
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartComponent
import TauCeti.Analysis.Calculus.FDeriv.Equiv
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv
import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization

/-!
# Microlocal regularity of distributions on manifolds, chart by chart

Let `V → M` be a smooth real vector bundle over a smooth manifold modelled on a
finite-dimensional real inner product space `E`, and let `T` be a real continuous linear functional
on the bundle tests `TauCeti.BundleTest I F V`, for instance a distributional section of a bundle
(`TauCeti.BundleDistribution`). In a smooth chart `c` with smooth inverse and a bundle frame `t`
over its source, `T` has components along the vectors `v` of the model fibre `F`
(`Bundle.Trivialization.chartComponent`), complex distributions on the chart target.

Let `P` be an invariant notion of microlocal regularity of distributions on open subsets of `E`
(`Distribution.IsInvariantMicrolocalRegularity`), such as microlocal smoothness or microlocal
`H^s` regularity. The functional `T` **satisfies `P` at a covector `ξ` at `x`**
(`TauCeti.BundleTest.IsMicrolocallyAt`) when, in some such chart at `x` and frame, all its
components satisfy `P` at `c x` in the direction of the covector `ξ ∘ D(c⁻¹)(c x)` read in the
chart, identified with a vector of `E` through the inner product. The chart and the frame do not
matter: for two charts `c`, `c'` with frames `t`, `t'`, and a point `y = c' x` with `x` in both
chart sources,

`S'_v` satisfies `P` at `(y, Dκ(y)ᵀ η)` for all `v` if and only if
`S_v` satisfies `P` at `(κ y, η)` for all `v`,

where `S_v` and `S'_v` are the components in `(t, c)` and in `(t', c')`, and `κ = c ∘ c'⁻¹` is the
chart transition (`Bundle.Trivialization.forall_chartComponent_microlocal_iff`). Hence `T`
satisfies `P` at `ξ` exactly when its components do in any chart and frame
(`TauCeti.BundleTest.isMicrolocallyAt_iff`).

This is the common construction behind the wave front set (`TauCeti.BundleTest.waveFrontSet`)
and the `H^s` wave front set (`TauCeti.BundleTest.sobolevWaveFrontSet`) of functionals on bundle
tests, and the microlocal analogue of `TauCeti.BundleTest.IsLocallyAt`.

## The argument

Near `y`, the component along `v` in `(t', c')` is

`S'_v = ∑ⱼ gⱼ κ^* S_{bⱼ}`, with `gⱼ = |det Dκ| · bⱼ*(G(c'⁻¹ ·) v)`,

for the change of frame `G = t ∘ t'⁻¹` and a basis `(bⱼ)` of `F`
(`Bundle.Trivialization.exists_restrictCLM_chartComponent_eq_sum`), where `κ^*` is the pullback of
distributions (`Distribution.compCLMOfOpenPartialHomeomorph`). The pullback transforms `P` by the
transpose of `Dκ`, and restriction, smooth multiples and finite sums preserve it. Exchanging the
roles of the two charts gives the converse. On the manifold, the chain rule
`D(c⁻¹)(c x) = D(c₀⁻¹)(c₀ x) ∘ Dκ(c x)` for `κ = c₀ ∘ c⁻¹`
(`OpenPartialHomeomorph.mfderiv_symm_eq_mfderiv_symm_comp_fderiv_symm_trans`) identifies the
covectors read in two charts.

## Main declarations

* `Bundle.Trivialization.forall_chartComponent_microlocal_iff`: for an invariant notion of
  microlocal regularity, the regularity of all components does not depend on the chart and the
  frame, covectors transforming by the transpose of the derivative of the chart transition.
* `Bundle.Trivialization.forall_chartComponent_microlocal_iff_of_chart`: in one chart, it does not
  depend on the frame.
* `TauCeti.BundleTest.IsMicrolocallyAt`: the functional `T` satisfies `P` at a covector of `M`, and
  `TauCeti.BundleTest.isMicrolocallyAt_iff`, its characterization in every chart and frame.
* `TauCeti.BundleTest.isMicrolocallyAt_smul_iff`, `TauCeti.BundleTest.IsMicrolocallyAt.add`,
  `TauCeti.BundleTest.IsMicrolocallyAt.smul`: it depends only on the ray through the covector and
  is preserved by sums and real multiples.
* `TauCeti.BundleTest.isOpen_setOf_isMicrolocallyAt`: it is an open condition on the cotangent
  bundle.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2 (the wave front set on a manifold, after Theorem 8.2.4) and §8.1 (the
  wave front set of a vector-valued distribution).
* L. Hörmander, *Lectures on Nonlinear Hyperbolic Differential Equations*, Springer, 1997, §11.1
  (the `H^s` wave front set, and its invariance under diffeomorphisms).
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
  {P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → E → Prop}

/-- If every component in `(t, c)` satisfies `P` at `(κ y, (Dκ⁻¹(κ y))ᵀ ξ)`, for the transition
`κ = c ∘ c'⁻¹`, then every component in `(t', c')` satisfies `P` at `(y, ξ)`. -/
private theorem chartComponent_of_forall_microlocal (hP : IsInvariantMicrolocalRegularity P)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ (c'.symm.trans c).source) {ξ : E}
    (h : ∀ w, P _ (t.chartComponent c hc hct T w) (c'.symm.trans c y)
      (((fderiv ℝ (c'.symm.trans c).symm (c'.symm.trans c y))†) ξ)) (v : F) :
    P _ (t'.chartComponent c' hc' hct' T v) y ξ := by
  obtain ⟨he, he'⟩ :=
    OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
  obtain ⟨B, hB, hBc, g, hg, hyB, hS⟩ := exists_restrictCLM_chartComponent_eq_sum (hc := hc)
    (hct := hct) (hc' := hc') (hct' := hct') hcs' he he' T v hy
  rw [← hP.restrictCLM_iff (fun z hz ↦ (hB hz).1) hyB, hS]
  exact hP.sum hyB fun j _ ↦
    hP.smulLeftCLM (hg j) (hP.compCLMOfOpenPartialHomeomorph he he' hB hBc hyB (h _))

/-- **Independence of the chart and the frame.** Let `P` be an invariant notion of microlocal
regularity, let `c` and `c'` be smooth charts with smooth inverses, with frames `t` and `t'` over
their sources, and let `y = c' x` for a point `x` of both chart sources. All components of the
local representative of `T` in `(t', c')` satisfy `P` at `(y, Dκ(y)ᵀ η)`, for the chart transition
`κ = c ∘ c'⁻¹`, exactly when all components in `(t, c)` satisfy `P` at `(κ y, η)`. -/
theorem forall_chartComponent_microlocal_iff (hP : IsInvariantMicrolocalRegularity P)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hcs' : ContMDiffOn 𝓘(ℝ, E) I ∞ c'.symm c'.target) (T : BundleTest I F V →L_c[ℝ] ℝ)
    {y : E} (hy : y ∈ c'.target) (hyc : c'.symm y ∈ c.source) (η : E) :
    (∀ v, P _ (t'.chartComponent c' hc' hct' T v) y (((fderiv ℝ (c ∘ c'.symm) y)†) η)) ↔
      ∀ v, P _ (t.chartComponent c hc hct T v) (c (c'.symm y)) η := by
  have hys : y ∈ (c'.symm.trans c).source := ⟨hy, hyc⟩
  constructor
  · -- Exchange the roles of the two charts: the transition from `c` to `c'` is `κ⁻¹`.
    intro h v
    have hz : c (c'.symm y) ∈ (c.symm.trans c').source :=
      ⟨c.map_source hyc, by simpa [c.left_inv hyc] using c'.map_target hy⟩
    refine chartComponent_of_forall_microlocal (t := t') (hc := hc') (hct := hct') (t' := t)
      (hc' := hc) (hct' := hct) hP hcs' hcs T hz (fun w ↦ ?_) v
    have hzy : c.symm.trans c' (c (c'.symm y)) = y := by simp [c.left_inv hyc, c'.right_inv hy]
    rw [hzy]
    exact h w
  · intro h v
    obtain ⟨he, he'⟩ :=
      OpenPartialHomeomorph.contDiffOn_symm_trans_and_symm_of_contMDiffOn hc' hcs' hc hcs
    refine chartComponent_of_forall_microlocal (t := t) (hc := hc) (hct := hct) (t' := t')
      (hc' := hc') (hct' := hct') hP hcs hcs' T hys (fun w ↦ ?_) v
    have hη := (c'.symm.trans c).adjoint_fderiv_symm_apply_adjoint_fderiv_apply_of_contDiffOn he
      he' (by simp) hys η
    rw [OpenPartialHomeomorph.coe_trans] at hη ⊢
    rw [hη]
    exact h w

/-- **Independence of the frame.** In a smooth chart `c` with smooth inverse, for an invariant
notion of microlocal regularity `P`, all components of the local representative of `T` in the
frame `t'` satisfy `P` at `(y, η)` exactly when all components in the frame `t` do. -/
theorem forall_chartComponent_microlocal_iff_of_chart (hP : IsInvariantMicrolocalRegularity P)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct' : c.source ⊆ t'.baseSet)
    (T : BundleTest I F V →L_c[ℝ] ℝ) {y : E} (hy : y ∈ c.target) (η : E) :
    (∀ v, P _ (t'.chartComponent c hc hct' T v) y η) ↔
      ∀ v, P _ (t.chartComponent c hc hct T v) y η := by
  have hid : fderiv ℝ (c ∘ c.symm) y = ContinuousLinearMap.id ℝ E := by
    have hc_id : c ∘ c.symm =ᶠ[𝓝 y] id := c.eventually_right_inverse hy
    rw [hc_id.fderiv_eq, fderiv_id]
  have h := forall_chartComponent_microlocal_iff (t := t) (t' := t') (hc := hc) (hct := hct)
    (hc' := hc) (hct' := hct') hP hcs hcs T hy (c.map_target hy) η
  rwa [hid, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply, c.right_inv hy] at h

end Bundle.Trivialization

/-! ### Microlocal regularity on the manifold -/

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

/-- A real functional `T` on bundle tests **satisfies the notion of microlocal regularity `P` at a
covector `ξ` at `x`** if, in some smooth chart `c` at `x` with smooth inverse and some frame `t`
over its source, every component of the local representative of `T` satisfies `P` at `c x` in the
direction of the covector `ξ ∘ D(c⁻¹)(c x)` read in the chart, identified with a vector of `E`
through the inner product. For an invariant notion of microlocal regularity `P`, the chart and the
frame do not matter (`TauCeti.BundleTest.isMicrolocallyAt_iff`).

The notion is meant for a boundaryless model `I`, where such charts exist at every point. At a
boundary point of a manifold with boundary there is no chart into `E`, and `T` never satisfies `P`
there. -/
@[expose]
def IsMicrolocallyAt (P : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → E → Prop)
    (T : BundleTest I F V →L_c[ℝ] ℝ) (x : M) (ξ : TangentSpace I x →L[ℝ] ℝ) : Prop :=
  ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t) (c : OpenPartialHomeomorph M E)
    (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source) (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target)
    (hct : c.source ⊆ t.baseSet), x ∈ c.source ∧
    ∀ v, P _ (t.chartComponent c hc hct T v) (c x)
      ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)))

variable {P Q : (Ω : Opens E) → 𝓓'(Ω, ℂ) → E → E → Prop} {S T : BundleTest I F V →L_c[ℝ] ℝ}
  {x : M} {ξ : TangentSpace I x →L[ℝ] ℝ}

/-- Unfolding `TauCeti.BundleTest.IsMicrolocallyAt`: `T` satisfies `P` at `ξ` exactly when, in some
smooth chart `c` at `x` with smooth inverse and some frame `t` over its source, every component of
the local representative of `T` satisfies `P` at `c x` in the direction of `ξ` read in the chart. No
property of `P` is needed. -/
theorem isMicrolocallyAt_def :
    IsMicrolocallyAt P T x ξ ↔ ∃ (t : Trivialization F (π F V)) (_ : MemTrivializationAtlas t)
      (c : OpenPartialHomeomorph M E) (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
      (_ : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet),
      x ∈ c.source ∧ ∀ v, P _ (t.chartComponent c hc hct T v) (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) :=
  Iff.rfl

/-- **Microlocal regularity in any chart and frame.** Let `P` be an invariant notion of microlocal
regularity. For a smooth chart `c` at `x` with smooth inverse and a frame `t` over its source, `T`
satisfies `P` at the covector `ξ` at `x` exactly when every component of its local representative
in `(t, c)` satisfies `P` at `c x` in the direction of `ξ` read in the chart. -/
theorem isMicrolocallyAt_iff (hP : IsInvariantMicrolocalRegularity P)
    (T : BundleTest I F V →L_c[ℝ] ℝ) {t : Trivialization F (π F V)} [MemTrivializationAtlas t]
    {c : OpenPartialHomeomorph M E} (hc : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source)
    (hcs : ContMDiffOn 𝓘(ℝ, E) I ∞ c.symm c.target) (hct : c.source ⊆ t.baseSet)
    (hx : x ∈ c.source) (ξ : TangentSpace I x →L[ℝ] ℝ) :
    IsMicrolocallyAt P T x ξ ↔
      ∀ v, P _ (t.chartComponent c hc hct T v) (c x)
        ((toDual ℝ E).symm (ξ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x))) := by
  refine ⟨fun ⟨t₀, _, c₀, hc₀, hcs₀, hct₀, hx₀, h⟩ ↦ ?_, fun h ↦ ⟨t, inferInstance, c, hc, hcs,
    hct, hx, h⟩⟩
  -- Transfer from the chart `c₀` of the definition to `c`, through the transition `c₀ ∘ c⁻¹`.
  have hiff := forall_chartComponent_microlocal_iff (t := t₀) (hc := hc₀) (hct := hct₀) (t' := t)
    (hc' := hc) (hct' := hct) hP hcs₀ hcs T (c.map_source hx)
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

/-- **Monotonicity in the notion.** If `P` implies `Q`, then satisfying `P` at a covector implies
satisfying `Q` there. -/
theorem IsMicrolocallyAt.mono (h : IsMicrolocallyAt P T x ξ)
    (hPQ : ∀ (Ω : Opens E) (S : 𝓓'(Ω, ℂ)) (y η : E), P Ω S y η → Q Ω S y η) :
    IsMicrolocallyAt Q T x ξ :=
  let ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ hPQ _ _ _ _ (h v)⟩

/-- For an invariant notion of microlocal regularity `P`, satisfying `P` on the manifold depends
only on the ray through the covector. -/
theorem isMicrolocallyAt_smul_iff (hP : IsInvariantMicrolocalRegularity P) {r : ℝ} (hr : 0 < r) :
    IsMicrolocallyAt P T x (r • ξ) ↔ IsMicrolocallyAt P T x ξ := by
  have key {a : ℝ} (ha : 0 < a) {ζ : TangentSpace I x →L[ℝ] ℝ} :
      IsMicrolocallyAt P T x ζ → IsMicrolocallyAt P T x (a • ζ) := by
    rintro ⟨t, ht, c, hc, hcs, hct, hx, h⟩
    refine ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
    have hsm : (toDual ℝ E).symm ((a • ζ) ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) =
        a • (toDual ℝ E).symm (ζ ∘L mfderiv 𝓘(ℝ, E) I c.symm (c x)) :=
      (congrArg _ (ContinuousLinearMap.smul_comp _ _ _)).trans (map_smul _ _ _)
    rw [hsm]
    exact hP.smul_covector ha (h v)
  refine ⟨fun h ↦ ?_, key hr⟩
  simpa [smul_smul, inv_mul_cancel₀ hr.ne'] using key (inv_pos.2 hr) h

/-- For an invariant notion of microlocal regularity `P`, the sum of two functionals satisfying
`P` at a covector satisfies `P` there. -/
theorem IsMicrolocallyAt.add (hP : IsInvariantMicrolocalRegularity P)
    (hS : IsMicrolocallyAt P S x ξ) (hT : IsMicrolocallyAt P T x ξ) :
    IsMicrolocallyAt P (S + T) x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, hS⟩ := hS
  have hT' := (isMicrolocallyAt_iff hP T (t := t) hc hcs hct hx ξ).1 hT
  refine ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_add]
  exact hP.add (hS v) (hT' v)

/-- For an invariant notion of microlocal regularity `P`, a real multiple of a functional
satisfying `P` at a covector satisfies `P` there. -/
theorem IsMicrolocallyAt.smul (hP : IsInvariantMicrolocalRegularity P)
    (h : IsMicrolocallyAt P T x ξ) (a : ℝ) : IsMicrolocallyAt P (a • T) x ξ := by
  obtain ⟨t, ht, c, hc, hcs, hct, hx, h⟩ := h
  refine ⟨t, ht, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_smul]
  exact hP.smul _ (h v)

variable (P) in
/-- On a manifold without boundary, the zero functional satisfies every invariant notion of
microlocal regularity at every covector. -/
theorem isMicrolocallyAt_zero [I.Boundaryless] (hP : IsInvariantMicrolocalRegularity P) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) : IsMicrolocallyAt P (0 : BundleTest I F V →L_c[ℝ] ℝ) x ξ := by
  obtain ⟨c, hc, hcs, hct, hx⟩ := exists_chart_source_subset_baseSet F I V (n := ∞) x
  refine ⟨trivializationAt F V x, inferInstance, c, hc, hcs, hct, hx, fun v ↦ ?_⟩
  rw [chartComponent_zero]
  exact hP.zero (c.map_source hx) _

/-- **Microlocal regularity is an open condition.** For an invariant notion of microlocal
regularity `P`, the covectors at which a real functional on bundle tests satisfies `P` form an
open subset of the cotangent bundle. -/
theorem isOpen_setOf_isMicrolocallyAt (hP : IsInvariantMicrolocalRegularity P)
    (T : BundleTest I F V →L_c[ℝ] ℝ) :
    IsOpen {p : CotangentBundle I M | IsMicrolocallyAt P T p.proj p.snd} := by
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
  -- In a basis of `F`, finitely many components satisfy `P` near `Φ p₀`.
  let b := Module.finBasis ℝ F
  have hb : ∀ᶠ p in 𝓝 p₀, ∀ i, P _ (t.chartComponent c hc hct T (b i)) (Φ p).1 (Φ p).2 :=
    eventually_all.2 fun i ↦ hΦ.eventually ((hP.isOpen_setOf _ _).mem_nhds (h (b i)))
  filter_upwards [hsrc, hb] with p hp hpb
  refine ⟨t, inferInstance, c, hc, hcs, hct, hp, fun v ↦ ?_⟩
  rw [t.chartComponent_eq_sum c hc hct b]
  exact hP.sum (c.map_source hp) fun i _ ↦ hP.smul _ (hpb i)

end TauCeti.BundleTest
