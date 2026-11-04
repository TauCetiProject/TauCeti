/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SecondFundamentalForm
public import TauCeti.Geometry.Manifold.Immersion.Diffeomorph
public import TauCeti.Geometry.Manifold.MFDeriv.Chart
public import TauCeti.Geometry.Manifold.SmoothEmbedding.NormalSpace.Euclidean
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The second fundamental form of a map from a manifold into an inner product space

Let `i : M → F` be a map from a manifold modelled on a finite-dimensional normed space `E` over
`𝕜 = ℝ` or `ℂ` into an inner product space `F` over `𝕜`. Its **second fundamental form**
`TauCeti.manifoldSecondFundamentalForm I i x` at `x : M` is the second fundamental form
`TauCeti.secondFundamentalForm 𝕜` of the coordinate expression `i ∘ (extChartAt I x).symm` at
`extChartAt I x x`, regarded as a continuous bilinear map on `TangentSpace I x` with values in `F`.

Like `TauCeti.criticalHessian`, the definition is total and carries no regularity or boundaryless
hypotheses. When `I` is boundaryless:

* the coordinate normal space `(D(i ∘ (extChartAt I x).symm)(extChartAt I x x)).rangeᗮ` coincides
  with the orthogonal complement `(mvfderiv I i x).rangeᗮ` of the image of the manifold
  differential, and over `ℝ` with `TauCeti.normalSubspace I i x`;
* for `i` of class `C²` at `x`, `manifoldSecondFundamentalForm I i x` is symmetric, may be computed
  in any chart of the `C²` maximal atlas containing `x`, and pulls back along any `C²` map whose
  differential at the base point is surjective (in particular, along any local diffeomorphism or
  diffeomorphism): the second-order term of a coordinate transition is tangent to the image of `Di`
  and is killed by the orthogonal projection onto the normal space;
* for a `TauCeti.SmoothEmbedding` into a real Hilbert space, `manifoldSecondFundamentalForm` agrees
  under `TauCeti.SmoothEmbedding.normalSpaceOrthogonalEquiv` with the intrinsic quotient normal
  class of the coordinate second derivative.

## Main definitions

* `TauCeti.manifoldSecondFundamentalForm I i x`: the normal component of the coordinate second
  derivative of `i : M → F` at `x : M`.

## Main results

* `TauCeti.manifoldSecondFundamentalForm_modelSpace`: on a normed space with its self-model,
  `manifoldSecondFundamentalForm` reduces to `TauCeti.secondFundamentalForm`.
* `TauCeti.manifoldSecondFundamentalForm_apply_mem_orthogonal` and
  `TauCeti.manifoldSecondFundamentalForm_apply_mem_normalSubspace`: on a boundaryless manifold,
  the second fundamental form takes values in `(mvfderiv I i x).rangeᗮ` (and over `ℝ` in
  `TauCeti.normalSubspace I i x`).
* `TauCeti.inner_manifoldSecondFundamentalForm_apply_of_mem_orthogonal` and
  `TauCeti.inner_manifoldSecondFundamentalForm_apply_of_mem_normalSubspace`: against a normal
  vector, `manifoldSecondFundamentalForm` pairs like the coordinate second derivative.
* `ContMDiffAt.manifoldSecondFundamentalForm_apply_comm`: symmetry for `C²` maps.
* `ContMDiffAt.manifoldSecondFundamentalForm_apply_eq_of_mem_maximalAtlas`: chart independence in
  any chart of the `C²` maximal atlas.
* `ContMDiffAt.manifoldSecondFundamentalForm_comp` and
  `Diffeomorph.manifoldSecondFundamentalForm_comp`: invariance under reparametrisation of the
  source.
* `TauCeti.SmoothEmbedding.coe_normalSpaceOrthogonalEquiv_sndFDeriv`: compatibility with the
  quotient normal bundle of a smooth embedding.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §§6–7.
* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. II, Chapter IX.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer, 2018, Chapter 8.
-/

public section

open Filter Function Set Topology
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti

section General

variable {𝕜 E H M F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The range of `mvfderiv I i x` agrees with the range of `mfderiv I 𝓘(𝕜, F) i x` read in `F`. -/
theorem range_mvfderiv (I : ModelWithCorners 𝕜 E H) (i : M → F) (x : M) :
    (mvfderiv I i x).range = (mfderiv I 𝓘(𝕜, F) i x : E →L[𝕜] F).range := by
  ext w
  simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  refine ⟨?_, ?_⟩
  · rintro ⟨v, rfl⟩
    exact ⟨tangentSpaceCastModel I x v, by rw [mvfderiv_apply_eq_mfderiv_apply]; rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨(tangentSpaceCastModel I x).symm v, by rw [mvfderiv_apply_eq_mfderiv_apply]; rfl⟩

/-- On a boundaryless manifold, `mvfderiv I i x`, read on the model space `E`, agrees with the
Fréchet derivative of the preferred coordinate expression at `extChartAt I x x`, even without a
differentiability hypothesis (both vanish when `i` is not differentiable at `x`). -/
theorem mvfderiv_comp_tangentSpaceCastModel_symm [I.Boundaryless] (i : M → F) (x : M) :
    (mvfderiv I i x).comp ((tangentSpaceCastModel I x).symm : E →L[𝕜] TangentSpace I x) =
      fderiv 𝕜 (i ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  by_cases hi : MDifferentiableAt I 𝓘(𝕜, F) i x
  · ext v
    exact DFunLike.congr_fun hi.mvfderiv_eq_fderiv_comp_extChartAt_symm v
  · have hi' : ¬DifferentiableAt 𝕜 (i ∘ (extChartAt I x).symm) (extChartAt I x x) :=
      hi ∘ mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm.mpr
    rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hi, ContinuousLinearMap.comp_zero,
      ContinuousLinearMap.zero_comp, fderiv_zero_of_not_differentiableAt hi']

/-- On a boundaryless manifold, the range of `mvfderiv I i x` equals the range of the Fréchet
derivative of the preferred coordinate expression at `extChartAt I x x`. -/
theorem range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm [I.Boundaryless] (i : M → F) (x : M) :
    (mvfderiv I i x).range = (fderiv 𝕜 (i ∘ (extChartAt I x).symm) (extChartAt I x x)).range := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (tangentSpaceCastModel I x).symm.surjective

variable [FiniteDimensional 𝕜 E] {i j : M → F} {x : M}

/-- The **second fundamental form** of a map `i : M → F` from a manifold into an inner product
space at `x : M`: the second fundamental form of the preferred coordinate expression
`i ∘ (extChartAt I x).symm` at `extChartAt I x x`, as a continuous bilinear map on
`TangentSpace I x` with values in `F`.

Like `TauCeti.criticalHessian`, the definition carries no regularity hypotheses. On a boundaryless
manifold, `ContMDiffAt.manifoldSecondFundamentalForm_apply_eq_of_mem_maximalAtlas` shows that for a
map which is `C²` at `x` it is independent of the choice of `C²` chart. -/
def manifoldSecondFundamentalForm (I : ModelWithCorners 𝕜 E H) (i : M → F) (x : M) :
    TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] F :=
  (tangentSpaceCastModel I x).symm.arrowCongrEquiv
    ((tangentSpaceCastModel I x).symm.arrowCongr (ContinuousLinearEquiv.refl 𝕜 F))
    (secondFundamentalForm 𝕜 (i ∘ (extChartAt I x).symm) (extChartAt I x x))

/-- Evaluating `manifoldSecondFundamentalForm` evaluates `secondFundamentalForm` of the preferred
coordinate expression on the model-space casts of the tangent vectors. -/
theorem manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm
    (v w : TangentSpace I x) :
    manifoldSecondFundamentalForm I i x v w =
      secondFundamentalForm 𝕜 (i ∘ (extChartAt I x).symm) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w) :=
  (rfl)

/-- On a manifold modelled on its model vector space, the `secondFundamentalForm` in the preferred
chart is `manifoldSecondFundamentalForm`. -/
theorem secondFundamentalForm_comp_chartAt_symm {N : Type*} [TopologicalSpace N] [ChartedSpace E N]
    {g : N → F} {y : N} (v w : E) :
    secondFundamentalForm 𝕜 (g ∘ (chartAt E y).symm) (chartAt E y y) v w =
      manifoldSecondFundamentalForm 𝓘(𝕜, E) g y
        ((tangentSpaceCastModel 𝓘(𝕜, E) y).symm v) ((tangentSpaceCastModel 𝓘(𝕜, E) y).symm w) := by
  have hext : ((extChartAt 𝓘(𝕜, E) y).symm : E → N) = (chartAt E y).symm := by ext; simp
  have hext' : extChartAt 𝓘(𝕜, E) y y = chartAt E y y := by simp
  rw [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearEquiv.apply_symm_apply, hext, hext']

/-- On a normed space with its self-model, `manifoldSecondFundamentalForm` is
`secondFundamentalForm`. -/
@[simp]
theorem manifoldSecondFundamentalForm_modelSpace {g : E → F} {v : E} :
    manifoldSecondFundamentalForm 𝓘(𝕜, E) g v = secondFundamentalForm 𝕜 g v := by
  ext u w
  simp only [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe, comp_id, id_eq]
  -- `tangentSpaceCastModel 𝓘(𝕜, E) v` is the identity on `E`.
  rfl

/-- `manifoldSecondFundamentalForm` depends only on the germ of the map at the base point. -/
theorem manifoldSecondFundamentalForm_congr_of_eventuallyEq (hij : i =ᶠ[𝓝 x] j) :
    manifoldSecondFundamentalForm I i x = manifoldSecondFundamentalForm I j x := by
  have hchart : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have hij' : i ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x x)] j ∘ (extChartAt I x).symm :=
    (hchart ▸ hij).comp_tendsto (continuousAt_extChartAt_symm (I := I) x)
  ext v w
  rw [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    secondFundamentalForm_apply, secondFundamentalForm_apply, hij'.fderiv.fderiv_eq]
  simp only [hij'.fderiv_eq]

/-! ### Boundaryless manifolds: normal projection, symmetry, and chart independence -/

section Boundaryless

variable [I.Boundaryless]

/-- On a boundaryless manifold, `manifoldSecondFundamentalForm` is the orthogonal projection onto
`(mvfderiv I i x).rangeᗮ` of the second derivative of the preferred coordinate expression. -/
theorem manifoldSecondFundamentalForm_apply (i : M → F) (x : M) (v w : TangentSpace I x) :
    manifoldSecondFundamentalForm I i x v w =
      (mvfderiv I i x).rangeᗮ.starProjection
        (fderiv 𝕜 (fderiv 𝕜 (i ∘ (extChartAt I x).symm)) (extChartAt I x x)
          (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)) := by
  rw [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    secondFundamentalForm_apply]
  simp only [range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm]

/-- On a boundaryless manifold, the second fundamental form takes values orthogonal to the range of
`mvfderiv I i x`. -/
@[simp]
theorem manifoldSecondFundamentalForm_apply_mem_orthogonal (i : M → F) (x : M)
    (v w : TangentSpace I x) :
    manifoldSecondFundamentalForm I i x v w ∈ (mvfderiv I i x).rangeᗮ := by
  rw [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm]
  exact secondFundamentalForm_apply_mem_orthogonal (𝕜 := 𝕜) (i ∘ (extChartAt I x).symm)
    (extChartAt I x x) (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)

/-- Paired with a vector orthogonal to `(mvfderiv I i x).range`, `manifoldSecondFundamentalForm`
agrees with the second derivative of the preferred coordinate expression. -/
theorem inner_manifoldSecondFundamentalForm_apply_of_mem_orthogonal {ν : F}
    (hν : ν ∈ (mvfderiv I i x).rangeᗮ) (v w : TangentSpace I x) :
    ⟪ν, manifoldSecondFundamentalForm I i x v w⟫_𝕜 =
      ⟪ν, fderiv 𝕜 (fderiv 𝕜 (i ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)⟫_𝕜 := by
  rw [range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm] at hν
  exact inner_secondFundamentalForm_apply_of_mem_orthogonal hν _ _

/-- The second fundamental form of a map which is `C²` at `x` is symmetric. -/
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_apply_comm
    (hi : ContMDiffAt I 𝓘(𝕜, F) 2 i x) (v w : TangentSpace I x) :
    manifoldSecondFundamentalForm I i x v w = manifoldSecondFundamentalForm I i x w v :=
  hi.contDiffAt_comp_extChartAt_symm.secondFundamentalForm_apply_comm
    (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)

/-- **The second fundamental form in an arbitrary chart.** For a map `i : M → F` which is `C²` at
`x` on a boundaryless manifold, `manifoldSecondFundamentalForm I i x` equals the
`secondFundamentalForm` of the coordinate expression `i ∘ (e.extend I).symm` in any chart `e` of
the `C²` maximal atlas containing `x`, evaluated on the images of the tangent vectors under
`mvfderiv I (e.extend I) x`. -/
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_apply_eq_of_mem_maximalAtlas
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 2 M) (hx : x ∈ e.source)
    (hi : ContMDiffAt I 𝓘(𝕜, F) 2 i x) (v w : TangentSpace I x) :
    manifoldSecondFundamentalForm I i x v w =
      secondFundamentalForm 𝕜 (i ∘ (e.extend I).symm) (e.extend I x)
        (mvfderiv I (e.extend I) x v) (mvfderiv I (e.extend I) x w) := by
  set z := extChartAt I x x
  set φ : E → E := e.extend I ∘ (extChartAt I x).symm
  have he1 : e ∈ IsManifold.maximalAtlas I 1 M :=
    IsManifold.maximalAtlas_subset_of_le (by norm_num) he
  have hext : ContMDiffAt I 𝓘(𝕜, E) 2 (e.extend I) x := e.contMDiffAt_extend he hx
  have hφ : ContDiffAt 𝕜 2 φ z := hext.contDiffAt_comp_extChartAt_symm
  have hφz : φ z = e.extend I x := by simp [φ, z]
  have hDφ (u : TangentSpace I x) : fderiv 𝕜 φ z (tangentSpaceCastModel I x u) =
      mvfderiv I (e.extend I) x u := by
    have h := (hext.mdifferentiableAt two_ne_zero).mvfderiv_eq_fderiv_comp_extChartAt_symm.symm
    exact DFunLike.congr_fun h u
  have hinv : (mvfderiv I (e.extend I) x).IsInvertible := by
    unfold mvfderiv
    exact ContinuousLinearMap.IsInvertible.comp ⟨NormedSpace.fromTangentSpace (e.extend I x), rfl⟩
      (isInvertible_mfderiv_extend he1 hx)
  have hsurj : Surjective (fderiv 𝕜 φ z) := by
    intro u
    obtain ⟨L, hL⟩ := hinv
    refine ⟨tangentSpaceCastModel I x (L.symm u), ?_⟩
    rw [hDφ, ← hL]
    exact L.apply_symm_apply u
  have hi_ext : ContDiffAt 𝕜 2 (i ∘ (e.extend I).symm) (φ z) :=
    hφz ▸ (contMDiffAt_iff_contDiffAt_comp_extend_symm he hx).mp hi
  have hev : i ∘ (extChartAt I x).symm =ᶠ[𝓝 z] (i ∘ (e.extend I).symm) ∘ φ := by
    have hmem : (extChartAt I x).symm ⁻¹' e.source ∈ 𝓝 z :=
      (continuousAt_extChartAt_symm (I := I) x).preimage_mem_nhds
        (by simpa only [z, extChartAt_to_inv] using e.open_source.mem_nhds hx)
    filter_upwards [hmem] with u hu
    have hu' : (extChartAt I x).symm u ∈ (e.extend I).source := by rwa [e.extend_source]
    simp only [φ, comp_apply, (e.extend I).left_inv hu']
  have hz : extChartAt I x x = z := rfl
  have hcongr := manifoldSecondFundamentalForm_congr_of_eventuallyEq (I := 𝓘(𝕜, E)) hev
  simp only [manifoldSecondFundamentalForm_modelSpace] at hcongr
  rw [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm, hz, hcongr,
    hi_ext.secondFundamentalForm_comp hφ hsurj, hφz, hDφ, hDφ]

/-- **Invariance under reparametrisation.** If `φ : N → M` is `C²` at `y` between boundaryless
manifolds with surjective differential at `y` (for instance, a local diffeomorphism at `y`), and
`i : M → F` is `C²` at `φ y`, then the second fundamental form of `i ∘ φ` at `y` is that of `i` at
`φ y` evaluated on `mfderiv J I φ y v` and `mfderiv J I φ y w`. -/
theorem _root_.ContMDiffAt.manifoldSecondFundamentalForm_comp
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] {φ : N → M} {y : N}
    (hi : ContMDiffAt I 𝓘(𝕜, F) 2 i (φ y)) (hφ : ContMDiffAt J I 2 φ y)
    (hsurj : Surjective (mfderiv J I φ y)) (v w : TangentSpace J y) :
    manifoldSecondFundamentalForm J (i ∘ φ) y v w =
      manifoldSecondFundamentalForm I i (φ y) (mfderiv J I φ y v) (mfderiv J I φ y w) := by
  set z := extChartAt J y y
  set ψ : E' → E := extChartAt I (φ y) ∘ φ ∘ (extChartAt J y).symm
  have hψ : ContDiffAt 𝕜 2 ψ z := by
    have h := (contMDiffAt_iff.mp hφ).2
    rwa [J.range_eq_univ, contDiffWithinAt_univ] at h
  have hψz : ψ z = extChartAt I (φ y) (φ y) := by simp [ψ, z]
  have hDψ (u : TangentSpace J y) :
      fderiv 𝕜 ψ z (tangentSpaceCastModel J y u) =
        tangentSpaceCastModel I (φ y) (mfderiv J I φ y u) :=
    ((hφ.mdifferentiableAt two_ne_zero).tangentSpaceCastModel_mfderiv_apply u).symm
  have hsurjψ : Surjective (fderiv 𝕜 ψ z) := by
    intro u
    obtain ⟨u₀, hu₀⟩ := hsurj ((tangentSpaceCastModel I (φ y)).symm u)
    refine ⟨tangentSpaceCastModel J y u₀, ?_⟩
    rw [hDψ, hu₀, ContinuousLinearEquiv.apply_symm_apply]
  have hi_chart : ContDiffAt 𝕜 2 (i ∘ (extChartAt I (φ y)).symm) (ψ z) :=
    hψz ▸ hi.contDiffAt_comp_extChartAt_symm
  have hev : (i ∘ φ) ∘ (extChartAt J y).symm =ᶠ[𝓝 z] (i ∘ (extChartAt I (φ y)).symm) ∘ ψ := by
    have hcont : ContinuousAt (φ ∘ (extChartAt J y).symm) z :=
      (by simpa [z] using hφ.continuousAt : ContinuousAt φ ((extChartAt J y).symm z)).comp
        (continuousAt_extChartAt_symm (I := J) y)
    have hmem : (φ ∘ (extChartAt J y).symm) ⁻¹' (extChartAt I (φ y)).source ∈ 𝓝 z :=
      hcont.preimage_mem_nhds
        (by simpa [z] using extChartAt_source_mem_nhds (I := I) (φ y))
    filter_upwards [hmem] with u hu
    have hu' : φ ((extChartAt J y).symm u) ∈ (extChartAt I (φ y)).source := hu
    simp only [ψ, comp_apply, (extChartAt I (φ y)).left_inv hu']
  have hz : extChartAt J y y = z := rfl
  have hcongr := manifoldSecondFundamentalForm_congr_of_eventuallyEq (I := 𝓘(𝕜, E')) hev
  simp only [manifoldSecondFundamentalForm_modelSpace] at hcongr
  rw [manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm,
    manifoldSecondFundamentalForm_eq_secondFundamentalForm_comp_extChartAt_symm, hz, hcongr,
    hi_chart.secondFundamentalForm_comp hψ hsurjψ, hψz, hDψ, hDψ]

/-- Precomposing with a `C^n` diffeomorphism (`2 ≤ n`) between boundaryless manifolds pulls back
the second fundamental form along the differential of the diffeomorphism. -/
theorem _root_.Diffeomorph.manifoldSecondFundamentalForm_comp
    {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
    [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'} [J.Boundaryless]
    [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} (Φ : N ≃ₘ^n⟮J, I⟯ M) (hn : 2 ≤ n)
    {y : N} (hi : ContMDiffAt I 𝓘(𝕜, F) 2 i (Φ y)) (v w : TangentSpace J y) :
    manifoldSecondFundamentalForm J (i ∘ Φ) y v w =
      manifoldSecondFundamentalForm I i (Φ y) (mfderiv J I Φ y v) (mfderiv J I Φ y w) := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hsurj : Surjective (mfderiv J I Φ y) := by
    rw [← Φ.mfderivToContinuousLinearEquiv_coe hn0 (x := y)]
    exact (Φ.mfderivToContinuousLinearEquiv hn0 y).surjective
  exact hi.manifoldSecondFundamentalForm_comp ((Φ.contMDiff.of_le hn).contMDiffAt) hsurj v w

end Boundaryless

end General

/-! ### Real manifolds: `TauCeti.normalSubspace` and smooth embeddings -/

section Real

variable {E H M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The orthogonal complement of `(mvfderiv I i x).range` in a real inner product space `V` is
`TauCeti.normalSubspace I i x`. -/
theorem orthogonal_range_mvfderiv_eq_normalSubspace (I : ModelWithCorners ℝ E H) (i : M → V)
    (x : M) : (mvfderiv I i x).rangeᗮ = normalSubspace I i x := by
  rw [normalSubspace, range_mvfderiv]

/-- Membership in `TauCeti.normalSubspace I i x` in terms of `mvfderiv I i x`. -/
theorem mem_normalSubspace_iff_mvfderiv {i : M → V} {x : M} {ν : V} :
    ν ∈ normalSubspace I i x ↔ ∀ u : TangentSpace I x, ⟪ν, mvfderiv I i x u⟫_ℝ = 0 := by
  rw [← orthogonal_range_mvfderiv_eq_normalSubspace]
  refine ⟨fun h u ↦ Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self _ u) h,
    fun h _ ⟨u, hu⟩ ↦ hu ▸ inner_eq_zero_symm.mp (h u)⟩

/-- When the model space `E` is finite-dimensional, `(mvfderiv I i x).range` is finite-dimensional
and hence complete, so `TauCeti.normalSubspace I i x` has an orthogonal projection even when the
ambient inner product space `V` is not complete. -/
instance instHasOrthogonalProjectionNormalSubspace [FiniteDimensional ℝ E]
    (I : ModelWithCorners ℝ E H) (i : M → V) (x : M) :
    (normalSubspace I i x).HasOrthogonalProjection := by
  rw [← orthogonal_range_mvfderiv_eq_normalSubspace]
  have : FiniteDimensional ℝ (TangentSpace I x) :=
    Module.Finite.equiv (tangentSpaceCastModel I x).symm.toLinearEquiv
  have : FiniteDimensional ℝ (mvfderiv I i x).range :=
    Module.Finite.range (mvfderiv I i x : TangentSpace I x →ₗ[ℝ] V)
  infer_instance

variable [FiniteDimensional ℝ E] [I.Boundaryless]

/-- On a real boundaryless manifold, the second fundamental form takes values in
`TauCeti.normalSubspace I i x`. -/
theorem manifoldSecondFundamentalForm_apply_mem_normalSubspace (i : M → V) (x : M)
    (v w : TangentSpace I x) :
    manifoldSecondFundamentalForm I i x v w ∈ normalSubspace I i x := by
  rw [← orthogonal_range_mvfderiv_eq_normalSubspace]
  exact manifoldSecondFundamentalForm_apply_mem_orthogonal i x v w

/-- Paired with a vector in `TauCeti.normalSubspace I i x`, `manifoldSecondFundamentalForm` agrees
with the second derivative of the preferred coordinate expression. -/
theorem inner_manifoldSecondFundamentalForm_apply_of_mem_normalSubspace {i : M → V} {x : M} {ν : V}
    (hν : ν ∈ normalSubspace I i x) (v w : TangentSpace I x) :
    ⟪ν, manifoldSecondFundamentalForm I i x v w⟫_ℝ =
      ⟪ν, fderiv ℝ (fderiv ℝ (i ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)⟫_ℝ := by
  rw [← orthogonal_range_mvfderiv_eq_normalSubspace] at hν
  exact inner_manifoldSecondFundamentalForm_apply_of_mem_orthogonal hν v w

/-- For a smooth embedding `f : M → V` into a real Hilbert space, `manifoldSecondFundamentalForm`
is the orthogonal representative (`TauCeti.SmoothEmbedding.normalSpaceOrthogonalEquiv`) of the
intrinsic normal class of the coordinate second derivative. -/
theorem SmoothEmbedding.coe_normalSpaceOrthogonalEquiv_sndFDeriv [CompleteSpace V] {n : ℕ∞ω}
    (f : SmoothEmbedding I 𝓘(ℝ, V) n M V) (x : M) (hn : n ≠ 0) (v w : TangentSpace I x) :
    (f.normalSpaceOrthogonalEquiv x hn
      (f.normalClass x hn ((NormedSpace.fromTangentSpace (f x)).symm
        (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
          (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)))) : V) =
      manifoldSecondFundamentalForm I f x v w := by
  rw [f.normalSpaceOrthogonalEquiv_normalClass, ← Submodule.starProjection_apply,
    manifoldSecondFundamentalForm_apply]
  simp only [orthogonal_range_mvfderiv_eq_normalSubspace]

end Real

end TauCeti

end
