/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

/-!
# A manifold derivative read in arbitrary charts

A map `f : M → M'` with manifold derivative `f'` at `x'` becomes, in the extended charts centred at
any `x` and `y` whose sources contain `x'` and `f x'`, a map between model vector spaces. Its
Fréchet derivative within `range I` is `f'` conjugated by the derivatives of the two charts.
Mathlib's `mdifferentiableAt_iff_of_mem_source` records differentiability in such charts, but not
the value of the derivative. Change-of-variables arguments on a manifold need that value, because
they integrate the absolute Jacobian determinant of `f` read in fixed charts.

For a map into a normed space on a boundaryless manifold, the coordinate expression in the
preferred extended chart at `x` is an honest function on the model space, `C^n` or differentiable
whenever `f` is, and its Fréchet derivative at the chart image of `x` is the vector-valued
manifold derivative `mvfderiv I f x`. This is how critical points defined through the preferred
chart, as in Morse theory, are identified with the zeros of `mvfderiv`.

## Main results

* `TauCeti.Manifold.mdifferentiableAt_iff_of_chartAt_eq`: preferred-chart invariance of
  manifold differentiability.
* `TauCeti.Manifold.mfderiv_eq_of_chartAt_eq`: retaining the preferred charts preserves
  manifold derivatives when the source atlas changes.

* `HasMFDerivAt.hasFDerivWithinAt_of_mem_source`: the derivative of `f` read in the extended
  charts at `x` and `y`.
* `ContDiffAt.contMDiffAt_extChartAt_symm_comp_extChartAt`: a map between model spaces that is
  `C^n` at the chart image of a point, read back through extended charts into a boundaryless
  target, is `C^n` on the manifolds.
* `TauCeti.mfderiv_eq_fderiv_comp_mfderiv_extChartAt` and
  `TauCeti.fderiv_comp_extChartAt_symm_injective`: for a map into a normed space, the manifold
  derivative at any point of a chart's source, in terms of the Fréchet derivative of the
  coordinate expression, and the resulting transfer of injectivity.
* `TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero`: the zeros of the manifold
  derivative are the zeros of the Fréchet derivative of the coordinate expression in any chart.
* `TauCeti.isInvertible_mvfderiv_extend`: the derivative of an extended chart of the maximal
  atlas, read as a map into the model space, is invertible on the chart source.
* `TauCeti.mvfderiv_eq_of_fderiv_comp_extChartAt_symm_eq`: maps whose coordinate expressions in
  some chart locally agree with maps having equal Fréchet derivatives have equal differentials.
* `TauCeti.eventually_mfderiv_eq_zero_iff_extChartAt_symm`: local uniqueness of critical points
  of a `C¹` family in the extended chart at `x` transfers to the manifold.
* `ContMDiffAt.contDiffAt_comp_extChartAt_symm` and
  `MDifferentiableAt.differentiableAt_comp_extChartAt_symm`: on a boundaryless manifold, the
  coordinate expression of a `C^n` (resp. differentiable) map into a normed space is `C^n` (resp.
  differentiable) at the chart image of the point.
* `ContMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint`: the same for `C^n` maps at
  an interior point of a manifold with boundary.
* `ContMDiffAt.contDiffAt_comp_prod_extChartAt_symm`: the same for a map on a product of
  boundaryless manifolds, read in the product of the preferred charts at the two factors.
* `ContMDiffAt.contDiffAt_writtenInExtChartAt` and
  `MDifferentiableAt.differentiableAt_writtenInExtChartAt`: the same for a map between manifolds,
  read in the extended charts at the point and at its image.
* `MDifferentiableAt.tangentSpaceCastModel_mfderiv_apply`: on a boundaryless source, the coordinate
  derivative is the manifold derivative transported by the canonical tangent-to-model casts.
* `TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm`: on a boundaryless
  manifold, a map into a normed space is differentiable at a point exactly when its preferred
  coordinate expression is differentiable at the chart image of the point.
* `TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm`: on a boundaryless manifold, the
  vector-valued manifold derivative is the Fréchet derivative of the coordinate expression;
  `TauCeti.mvfderiv_comp_tangentSpaceCastModel_symm`,
  `TauCeti.mvfderiv_apply_eq_fderiv_comp_extChartAt_symm`,
  `TauCeti.range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm`, and
  `TauCeti.injective_fderiv_comp_extChartAt_symm_iff` record the corresponding composition with
  the model-space tangent cast, pointwise evaluation, range equality, and injectivity equivalence.
* `TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm`: on a boundaryless manifold, the
  differential of a map into a normed space vanishes at a point exactly when the
  Fréchet derivative of its preferred-chart coordinate expression does.
* `MDifferentiableAt.mfderiv_eq_fderiv_extChartAt_conj`: on a boundaryless manifold, the manifold
  derivative of a map between manifolds is the Fréchet derivative of its expression in the extended
  charts at the point and at its image.
* `ContMDiffAt.hasStrictFDerivAt_extChartAt_conj`: over `ℝ` or `ℂ`, a map out of a boundaryless
  manifold that is `C¹` at a point, read in the extended charts at that point and at its image, is
  strictly differentiable at the chart image of the point.
* `TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm` and
  `TauCeti.contMDiffAt_iff_contDiffAt_comp_extend_symm`: on a boundaryless manifold, a map into a
  normed space is `C^n` at a point exactly when its coordinate expression in the preferred chart,
  or in any chart of the `C^n` maximal atlas, is `C^n` there.
* `ContMDiffAt.contDiffAt_comp_chartAt_symm` and
  `TauCeti.fderiv_comp_chartAt_symm`: the corresponding
  regularity and derivative formulas for a manifold modelled on its model space, with
  `TauCeti.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm` reading the kernel of the
  differential as a subspace of the model space.
* `TauCeti.mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero`: on a boundaryless manifold, the
  differential of a map into a normed space vanishes at a point exactly when the derivative of its
  coordinate expression in any chart of the `C¹` maximal atlas vanishes there.
* `MDifferentiableAt.fderivWithin_comp_extChartAt_symm`: read a model-valued manifold
  derivative after an inverse chart, including derivatives within the model range.
* `MDifferentiableAt.fderivWithin_extChartAt_comp_extChartAt_symm`: the same for a map between
  manifolds read in arbitrary preferred charts of the source and the target.
* `ContMDiffAt.contDiffAt_extChartAt_comp_extChartAt_symm`: a `C^n` map between manifolds, read in
  arbitrary preferred charts, is `C^n` at interior points of the source chart target.
* `HasMFDerivAt.hasFDerivAt_extChartAt_comp`: read the coordinate derivative of a map from
  a normed source by composing its manifold derivative with the tangent chart.
* `MDifferentiableAt.fderiv_extChartAt_comp_apply`: the same, with the manifold derivative of the
  chart in place of the tangent chart.
* `MDifferentiableAt.differentiableAt_chartAt_comp`: a differentiable map from a normed space
  into a manifold modelled on a normed space is differentiable in the preferred chart at its
  image.
* `MDifferentiableAt.fderiv_chartAt_comp`: the derivative in that chart is the manifold
  derivative with the canonical source tangent identification.
* `TauCeti.mfderivWithin_extChartAt_symm_of_subset`: within a subset of the chart target with
  unique derivatives, the derivative of the inverse chart is its derivative within the model range.
* `TauCeti.eventually_differentiableAt_chart_comp_of_eventually_mdifferentiableAt` and
  `TauCeti.eventually_mdifferentiableAt_chart_symm_comp_of_eventually_differentiableAt`:
  transport differentiability near a point between a product of manifolds and model spaces
  using maximal-atlas charts.
* `TauCeti.hasFDerivWithinAt_extChartAt_coordChange`: on a subset of a chart overlap, the extended
  coordinate change has its derivative within the model range as Fréchet derivative within the
  image of the subset.
* `TauCeti.hasMFDerivAt_extChartAt_self` and `TauCeti.mfderiv_extChartAt_eq_id`: the extended
  chart at `x` has the identity as its manifold derivative at `x`, with no smoothness hypothesis on
  the atlas.
* `TauCeti.writtenInExtChartAt_chartAt_comp_eventuallyEq`, `TauCeti.hasMFDerivAt_chartAt_comp` and
  `TauCeti.contMDiffAt_chartAt_comp`: for a space charted over a charted space `X`, with the
  composite charts, the preferred `X`-valued chart at `x` reads as the identity near `x`, so it is
  smooth at `x` with the identity as its derivative there.
* `MDifferentiableAt.differentiableWithinAt_and_fderivWithin_extChartAt_comp_eq_zero`: where the
  manifold differential vanishes at a point of differentiability, the coordinate expression in
  extended charts is differentiable within the model range with zero derivative.
* `TauCeti.fderiv_comp_extChartAt_symm_apply_zero_one`: the preferred chart of `M × 𝕜` is the
  identity on `𝕜`, so the derivative of a coordinate expression in the direction `(0, 1)` is the
  derivative along `𝕜`, read without any chart; `TauCeti.deriv_prodMk_eventuallyEq_fderiv` is the
  same identity near a point, in the preferred chart at that point.
* `ContMDiff.contMDiff_deriv_prodMk` and `ContMDiff.continuous_deriv_prodMk`: the derivative along
  `𝕜` of a `C^(n + 1)` function on `M × 𝕜` is `C^n`, and that of a `C¹` function is continuous.
-/

public section

open Set
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' 1 M']

namespace TauCeti.Manifold

omit [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- Preferred charts determine manifold differentiability independently of the rest of the atlas. -/
theorem mdifferentiableAt_iff_of_chartAt_eq {c c' : ChartedSpace H M}
    (h : c.chartAt = c'.chartAt) (f : M → M') (x : M) :
    (letI := c; MDifferentiableAt I I' f x) ↔ (letI := c'; MDifferentiableAt I I' f x) := by
  simp only [mdifferentiableAt_iff, writtenInExtChartAt, extChartAt, chartAt, h]

omit [ChartedSpace H M] [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- Changing the source atlas while retaining its preferred charts preserves manifold derivatives
for maps to any charted target. -/
theorem mfderiv_eq_of_chartAt_eq {c c' : ChartedSpace H M} (h : c.chartAt = c'.chartAt)
    (f : M → M') (x : M) :
    (letI := c; mfderiv I I' f x) = (letI := c'; mfderiv I I' f x) := by
  have hd := mdifferentiableAt_iff_of_chartAt_eq (I := I) (I' := I') h f x
  -- Select c as the local atlas for the source-side derivative formula.
  let _ : ChartedSpace H M := c
  by_cases hf : (letI := c; MDifferentiableAt I I' f x)
  · have hleft : (letI := c; mfderiv I I' f x) = _ := hf.mfderiv
    -- Select c' for the target-side formula; both displayed statements fix their atlas.
    let _ : ChartedSpace H M := c'
    have hright : (letI := c'; mfderiv I I' f x) = _ := (hd.mp hf).mfderiv
    apply hleft.trans
    apply Eq.trans ?_ hright.symm
    simp only [writtenInExtChartAt, extChartAt, chartAt, h]
    -- The tangent-space implementation casts are independent of the chosen atlas.
    rfl
  · have hleft : (letI := c; mfderiv I I' f x) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt hf
    -- Select c' to apply its non-differentiability law.
    let _ : ChartedSpace H M := c'
    have hright : (letI := c'; mfderiv I I' f x) = 0 :=
      mfderiv_zero_of_not_mdifferentiableAt (hd.not.mp hf)
    exact hleft.trans hright.symm

end TauCeti.Manifold

/-- Read in the extended charts at `x` and `y`, a map with manifold derivative `f'` at `x'` has
Fréchet derivative within `range I` equal to `f'` pre- and post-composed with the derivatives of
the inverse chart at `x` and of the chart at `y`. The charts need only contain `x'` and `f x'` in
their sources; they need not be centred there. -/
theorem HasMFDerivAt.hasFDerivWithinAt_of_mem_source {f : M → M'} {x x' : M} {y : M'}
    {f' : TangentSpace I x' →L[𝕜] TangentSpace I' (f x')} (hf : HasMFDerivAt I I' f x' f')
    (hx : x' ∈ (chartAt H x).source) (hy : f x' ∈ (chartAt H' y).source) :
    HasFDerivWithinAt (extChartAt I' y ∘ f ∘ (extChartAt I x).symm)
      (mfderiv I' 𝓘(𝕜, E') (extChartAt I' y) (f x') ∘L f' ∘L
        mfderivWithin 𝓘(𝕜, E) I (extChartAt I x).symm (range I) (extChartAt I x x') :
          E →L[𝕜] E')
      (range I) (extChartAt I x x') := by
  have hx' : x' ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hsymm := (mdifferentiableWithinAt_extChartAt_symm
    ((extChartAt I x).map_source hx')).hasMFDerivWithinAt
  -- Both remaining derivatives are taken at `(extChartAt I x).symm (extChartAt I x x') = x'`.
  have hf' : HasMFDerivAt I I' f ((extChartAt I x).symm (extChartAt I x x')) f' := by
    rwa [(extChartAt I x).left_inv hx']
  have hchart : HasMFDerivAt I' 𝓘(𝕜, E') (extChartAt I' y)
      (f ((extChartAt I x).symm (extChartAt I x x')))
      (mfderiv I' 𝓘(𝕜, E') (extChartAt I' y) (f x')) := by
    rw [(extChartAt I x).left_inv hx']
    exact (mdifferentiableAt_extChartAt hy).hasMFDerivAt
  exact hasMFDerivWithinAt_iff_hasFDerivWithinAt.1
    ((hchart.comp _ hf').comp_hasMFDerivWithinAt _ hsymm)

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- A map `g` between model spaces which is `C^n` at the chart image of `x` and sends it to the
chart image of `y` gives, read back through the extended charts at `x` and `y`, a map `M → M'`
which is `C^n` at `x`. The target model must be boundaryless, so that `g` stays in the chart
target near the chart image of `x`. -/
theorem ContDiffAt.contMDiffAt_extChartAt_symm_comp_extChartAt [I'.Boundaryless]
    {n : WithTop ℕ∞} {g : E → E'} {x : M} {y : M'} (hg : ContDiffAt 𝕜 n g (extChartAt I x x))
    (hgx : g (extChartAt I x x) = extChartAt I' y y) :
    ContMDiffAt I I' n (fun z ↦ (extChartAt I' y).symm (g (extChartAt I x z))) x := by
  have hy : (extChartAt I' y).symm (g (extChartAt I x x)) = y := by
    rw [hgx, extChartAt_to_inv]
  have htarget : ∀ᶠ w in 𝓝 (extChartAt I x x), g w ∈ (extChartAt I' y).target :=
    hg.continuousAt.preimage_mem_nhds (hgx ▸ extChartAt_target_mem_nhds y)
  rw [contMDiffAt_iff, hy]
  refine ⟨ContinuousAt.comp_of_eq (continuousAt_extChartAt_symm y)
    (hg.continuousAt.comp (continuousAt_extChartAt x)) hgx, ?_⟩
  refine hg.contDiffWithinAt.congr_of_eventuallyEq_of_mem ?_ (mem_range_self _)
  filter_upwards [nhdsWithin_le_nhds htarget, extChartAt_target_mem_nhdsWithin x] with w hw hw'
  simp only [Function.comp_apply, (extChartAt I x).right_inv hw', (extChartAt I' y).right_inv hw]

/-! ### Maps into a normed space, read in a chart of the source -/

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x y : M}

/-- At a point `y` of the source of the extended chart at `x`, the manifold derivative of a map
into a normed space is the Fréchet derivative of its coordinate expression
`f ∘ (extChartAt I x).symm` at the chart image of `y`, composed with the manifold derivative of
the chart, provided the coordinate expression is Fréchet differentiable there. The chart need not
be centred at `y`. -/
theorem mfderiv_eq_fderiv_comp_mfderiv_extChartAt (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    mfderiv I 𝓘(𝕜, F) f y = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)).comp
      (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) := by
  have he : HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) y (mfderiv I 𝓘(𝕜, E) (extChartAt I x) y) :=
    (mdifferentiableAt_extChartAt (by simpa using hy)).hasMFDerivAt
  have hfeq : f =ᶠ[𝓝 y] (f ∘ (extChartAt I x).symm) ∘ extChartAt I x := by
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hy] with z hz
    rw [Function.comp_apply, Function.comp_apply, (extChartAt I x).left_inv hz]
  exact ((hg.hasFDerivAt.hasMFDerivAt.comp y he).congr_of_eventuallyEq_abuse hfeq).mfderiv

/-- Read in a chart, a map into a normed space whose manifold derivative at `y` is injective has
injective Fréchet derivative at the chart image of `y`, provided the coordinate expression is
Fréchet differentiable there. -/
theorem fderiv_comp_extChartAt_symm_injective (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y))
    (hf : Function.Injective (mfderiv I 𝓘(𝕜, F) f y)) :
    Function.Injective (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL] at hf
  exact Function.Injective.of_comp_right (g := L) hf L.surjective

/-- Read in a chart whose source contains `y`, a map into a normed space with differentiable
coordinate expression has zero manifold derivative at `y` exactly when that coordinate expression
has zero Fréchet derivative at the chart image of `y`. -/
theorem mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero
    (hy : y ∈ (extChartAt I x).source)
    (hg : DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y)) :
    mfderiv I 𝓘(𝕜, F) f y = 0 ↔
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x y) = 0 := by
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extChartAt hy
  rw [mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy hg, ← hL]
  -- Precomposition with the invertible chart derivative `L` detects the zero map.
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun h ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := L.surjective v
    exact DFunLike.congr_fun h w
  · exact DFunLike.congr_fun h (L w)

omit [IsManifold I 1 M] in
/-- The derivative of an extended chart of the `C¹` maximal atlas, read as a map into the model
space, is invertible at every point of the chart source. -/
theorem isInvertible_mvfderiv_extend {e : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (hx : x ∈ e.source) :
    (mvfderiv I (e.extend I) x).IsInvertible := by
  -- `mvfderiv` is `mfderiv` followed by the identification `fromTangentSpace` of the tangent
  -- space of `E` with `E`; both factors are invertible.
  unfold mvfderiv
  exact ContinuousLinearMap.IsInvertible.comp ⟨NormedSpace.fromTangentSpace (e.extend I x), rfl⟩
    (isInvertible_mfderiv_extend he hx)

/-- Read in a chart whose source contains `y`, two maps into a normed space have the same
differential at `y` when, near the chart image of `y`, their coordinate expressions agree with maps
`f'` and `g'` that are differentiable there with the same Fréchet derivative. Taking
`f' = f ∘ (extChartAt I x).symm` and `g' = g ∘ (extChartAt I x).symm` compares the coordinate
expressions themselves. -/
theorem mvfderiv_eq_of_fderiv_comp_extChartAt_symm_eq {g : M → F} {f' g' : E → F}
    (hy : y ∈ (extChartAt I x).source)
    (hf : f ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x y)] f')
    (hg : g ∘ (extChartAt I x).symm =ᶠ[𝓝 (extChartAt I x y)] g')
    (hf' : DifferentiableAt 𝕜 f' (extChartAt I x y))
    (hg' : DifferentiableAt 𝕜 g' (extChartAt I x y))
    (h : fderiv 𝕜 f' (extChartAt I x y) = fderiv 𝕜 g' (extChartAt I x y)) :
    mvfderiv I f y = mvfderiv I g y := by
  simp only [mvfderiv,
    mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy (hf'.congr_of_eventuallyEq hf),
    mfderiv_eq_fderiv_comp_mfderiv_extChartAt hy (hg'.congr_of_eventuallyEq hg),
    hf.fderiv_eq, hg.fderiv_eq, h]
  -- The two sides differ only in the point indexing the tangent space of `F`, which is `F`.
  rfl

open Filter in
/-- If the critical point of the coordinate expression `fun v ↦ f (q.1, (extChartAt I x).symm v)`
of a `C¹` family is, near `(p, extChartAt I x x)`, uniquely `η q.1`, then the zero of the manifold
derivative of `fun y ↦ f (q.1, y)` near `(p, x)` is uniquely `(extChartAt I x).symm (η q.1)`. -/
theorem eventually_mfderiv_eq_zero_iff_extChartAt_symm {P : Type*} [NormedAddCommGroup P]
    [NormedSpace 𝕜 P] {f : P × M → F} {p : P} {x : M} {η : P → E}
    (hG : ContDiffAt 𝕜 1 (fun q : P × E ↦ f (q.1, (extChartAt I x).symm q.2))
      (p, extChartAt I x x))
    (htarget : ∀ᶠ q in 𝓝 p, η q ∈ (extChartAt I x).target)
    (huniq : ∀ᶠ q in 𝓝 (p, extChartAt I x x),
      fderiv 𝕜 (fun v ↦ f (q.1, (extChartAt I x).symm v)) q.2 = 0 ↔ η q.1 = q.2) :
    ∀ᶠ q in 𝓝 (p, x), mfderiv I 𝓘(𝕜, F) (fun y ↦ f (q.1, y)) q.2 = 0 ↔
      (extChartAt I x).symm (η q.1) = q.2 := by
  let φ := extChartAt I x
  have hmap : ContinuousAt (fun q : P × M ↦ (q.1, φ q.2)) (p, x) :=
    continuousAt_fst.prodMk ((continuousAt_extChartAt (I := I) x).comp continuousAt_snd)
  have hGnear := hmap.eventually (hG.eventually (by norm_num))
  have hsnear : ∀ᶠ q : P × M in 𝓝 (p, x), q.2 ∈ φ.source :=
    continuousAt_snd.preimage_mem_nhds (extChartAt_source_mem_nhds x)
  filter_upwards [hmap.eventually huniq, hGnear, hsnear,
    continuousAt_fst.preimage_mem_nhds htarget] with q hu hg hs ht
  have hslice : DifferentiableAt 𝕜 ((fun y ↦ f (q.1, y)) ∘ φ.symm) (φ q.2) :=
    (hg.comp (φ q.2) (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt one_ne_zero
  rw [mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm_eq_zero hs hslice]
  exact hu.trans (φ.symm_apply_eq hs ht).symm

omit [IsManifold I 1 M] in
/-- At an interior point `x`, a map into a normed space which is `C^n` at `x` has a `C^n`
coordinate expression in the preferred extended chart at `x`. This is the interior-point
counterpart of `ContMDiffAt.contDiffAt_comp_extChartAt_symm`, which assumes a boundaryless
manifold. -/
theorem _root_.ContMDiffAt.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint {n : WithTop ℕ∞}
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) (hx : I.IsInteriorPoint x) :
    ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  -- At an interior point the range of `I` is a neighbourhood of the chart image of `x`.
  contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_iff_source.mp hf).contMDiffAt (mem_interior_iff_mem_nhds.mp hx))

end TauCeti

/-! ### Maps into a normed space on a boundaryless manifold -/

section Boundaryless

variable [I.Boundaryless] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x : M}

namespace TauCeti

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space is `C^n` at `x` exactly when its
coordinate expression in the preferred extended chart at `x` is `C^n` at the chart image of `x`. -/
theorem contMDiffAt_iff_contDiffAt_comp_extChartAt_symm {n : WithTop ℕ∞} :
    ContMDiffAt I 𝓘(𝕜, F) n f x ↔
      ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  rw [contMDiffAt_iff_source, ModelWithCorners.Boundaryless.range_eq_univ,
    contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space is `C^n` at `x` exactly when its
coordinate expression in a chart of the `C^n` maximal atlas containing `x` is `C^n` at the chart
image of `x`. -/
theorem contMDiffAt_iff_contDiffAt_comp_extend_symm {n : WithTop ℕ∞}
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I n M)
    (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(𝕜, F) n f x ↔ ContDiffAt 𝕜 n (f ∘ (e.extend I).symm) (e.extend I x) := by
  rw [← contMDiffWithinAt_univ, contMDiffWithinAt_iff_source_of_mem_maximalAtlas he hx,
    preimage_univ, univ_inter, ModelWithCorners.Boundaryless.range_eq_univ,
    contMDiffWithinAt_univ, contMDiffAt_iff_contDiffAt]

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, the differential of a map into a normed space vanishes exactly
when the derivative of its coordinate expression in a chart of the `C¹` maximal atlas containing
`x` vanishes at the chart image of `x`. Both sides are `0` when the map is not differentiable
at `x`. -/
theorem mvfderiv_eq_zero_iff_fderiv_comp_extend_symm_eq_zero
    {e : OpenPartialHomeomorph M H} (he : e ∈ IsManifold.maximalAtlas I 1 M) (hx : x ∈ e.source) :
    mvfderiv I f x = 0 ↔ fderiv 𝕜 (f ∘ (e.extend I).symm) (e.extend I x) = 0 := by
  have hiff : MDifferentiableAt I 𝓘(𝕜, F) f x ↔
      DifferentiableAt 𝕜 (f ∘ (e.extend I).symm) (e.extend I x) := by
    have h := mdifferentiableWithinAt_iff_source_of_mem_maximalAtlas (s := univ) (f := f)
      (I' := 𝓘(𝕜, F)) he hx
    rwa [preimage_univ, univ_inter, ModelWithCorners.Boundaryless.range_eq_univ,
      mdifferentiableWithinAt_univ, mdifferentiableWithinAt_univ,
      mdifferentiableAt_iff_differentiableAt] at h
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, F) f x
  swap
  · rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf,
      fderiv_zero_of_not_differentiableAt (mt hiff.mpr hf)]
    simp
  have hg := hiff.mp hf
  have hfg : f =ᶠ[𝓝 x] (f ∘ (e.extend I).symm) ∘ e.extend I := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    rw [Function.comp_apply, Function.comp_apply, (e.extend I).left_inv (by rwa [e.extend_source])]
  have hcomp : mvfderiv I f x = mvfderiv I ((f ∘ (e.extend I).symm) ∘ e.extend I) x := by
    simp only [mvfderiv, hfg.mfderiv_eq]
    -- The two sides differ only in the point indexing the tangent space of `F`, which is `F`.
    rfl
  obtain ⟨L, hL⟩ := isInvertible_mfderiv_extend he hx
  rw [hcomp, mvfderiv_comp_of_eq hg.mdifferentiableAt
    ((e.contMDiffAt_extend he hx).mdifferentiableAt one_ne_zero) rfl, mvfderiv_eq_fderiv, ← hL]
  -- Precomposition with the invertible chart derivative `L` neither creates nor kills zeros.
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]; exact ContinuousLinearMap.zero_comp _⟩
  ext u
  rw [← L.apply_symm_apply u]
  exact DFunLike.congr_fun h (L.symm u)

end TauCeti

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space which is `C^n` at `x` has a `C^n`
coordinate expression in the preferred extended chart at `x`. -/
theorem ContMDiffAt.contDiffAt_comp_extChartAt_symm {n : WithTop ℕ∞}
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) :
    ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  TauCeti.contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.mp hf

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- On a product of boundaryless manifolds, a map into a normed space which is `C^n` at `(x, x')`
has a `C^n` coordinate expression in the preferred extended charts at `x` and `x'`, at the pair of
chart images. -/
theorem _root_.ContMDiffAt.contDiffAt_comp_prod_extChartAt_symm [I'.Boundaryless]
    {n : WithTop ℕ∞} {g : M × M' → F} {x' : M'}
    (hg : ContMDiffAt (I.prod I') 𝓘(𝕜, F) n g (x, x')) :
    ContDiffAt 𝕜 n (fun z : E × E' ↦ g ((extChartAt I x).symm z.1, (extChartAt I' x').symm z.2))
      (extChartAt I x x, extChartAt I' x' x') := by
  simpa only [extChartAt_prod, PartialEquiv.prod_coe_symm, PartialEquiv.prod_coe,
    Function.comp_def] using hg.contDiffAt_comp_extChartAt_symm

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space which is differentiable at `x` has a
differentiable coordinate expression in the preferred extended chart at `x`. -/
theorem MDifferentiableAt.differentiableAt_comp_extChartAt_symm
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have h := ((mdifferentiableAt_iff f x).1 hf).2
  rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
    writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp] at h

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- On a boundaryless source, a map between manifolds which is `C^n` at `x` has a `C^n` coordinate
expression in the extended charts at `x` and at `f x`. -/
theorem ContMDiffAt.contDiffAt_writtenInExtChartAt {n : WithTop ℕ∞} {g : M → M'}
    (hg : ContMDiffAt I I' n g x) :
    ContDiffAt 𝕜 n (writtenInExtChartAt I I' x g) (extChartAt I x x) := by
  simpa only [writtenInExtChartAt, I.range_eq_univ, contDiffWithinAt_univ] using
    (contMDiffAt_iff.1 hg).2

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- On a boundaryless source, a map between manifolds which is differentiable at `x` has a
differentiable coordinate expression in the extended charts at `x` and at `f x`. -/
theorem MDifferentiableAt.differentiableAt_writtenInExtChartAt {g : M → M'}
    (hg : MDifferentiableAt I I' g x) :
    DifferentiableAt 𝕜 (writtenInExtChartAt I I' x g) (extChartAt I x x) := by
  simpa only [writtenInExtChartAt, I.range_eq_univ, differentiableWithinAt_univ] using
    ((mdifferentiableAt_iff _ _).1 hg).2

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- On a boundaryless manifold, the manifold derivative of `g : M → M'` at `x` is the Fréchet
derivative of `g` read in the extended charts at `x` and at `y = g x`, with the tangent spaces at
`x` and `g x` identified with the model spaces. Naming the image point `y` allows a self-map
fixing `x` to be read in the single chart at `x`. -/
theorem MDifferentiableAt.mfderiv_eq_fderiv_extChartAt_conj {g : M → M'} {y : M'}
    (hg : MDifferentiableAt I I' g x) (hy : g x = y) :
    mfderiv I I' g x =
      fderiv 𝕜 (extChartAt I' y ∘ g ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  subst hy
  rw [hg.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  -- The tangent-space casts `tangentSpaceCastModel` are the identity maps of the model spaces.
  rfl

omit [IsManifold I 1 M] [IsManifold I' 1 M'] in
/-- On a boundaryless source, the manifold derivative, transported to the model spaces by the
canonical tangent casts, is the Fréchet derivative of the preferred coordinate expression. -/
theorem MDifferentiableAt.tangentSpaceCastModel_mfderiv_apply {g : M → M'}
    (hg : MDifferentiableAt I I' g x) (v : TangentSpace I x) :
    tangentSpaceCastModel I' (g x) (mfderiv I I' g x v) =
      fderiv 𝕜 (writtenInExtChartAt I I' x g) (extChartAt I x x)
        (tangentSpaceCastModel I x v) := by
  rw [hg.mfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply]

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space is differentiable at `x` exactly when
its coordinate expression in the preferred extended chart is differentiable at the chart image
of `x`. -/
theorem TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm :
    MDifferentiableAt I 𝓘(𝕜, F) f x ↔
      DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  refine ⟨MDifferentiableAt.differentiableAt_comp_extChartAt_symm, fun h ↦ ?_⟩
  rw [mdifferentiableAt_iff]
  refine ⟨?_, ?_⟩
  · -- Near `x`, the map is its coordinate expression composed with the chart.
    exact (h.continuousAt.comp (continuousAt_extChartAt x)).congr
      (comp_extChartAt_symm_comp_extChartAt_eventuallyEq f x)
  · rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
      writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, the vector-valued manifold derivative of a map into a normed space
is the Fréchet derivative of its coordinate expression in the preferred extended chart. Both sides
are `0` when the map is not differentiable at the point. -/
theorem TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm :
    mvfderiv I f x = fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  by_cases hf : MDifferentiableAt I 𝓘(𝕜, F) f x
  · rw [hf.mvfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ,
      writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      Function.id_comp]
  · have hd : ¬ DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
      mt (TauCeti.mdifferentiableAt_iff_differentiableAt_comp_extChartAt_symm).mpr hf
    rw [mvfderiv, mfderiv_zero_of_not_mdifferentiableAt hf, fderiv_zero_of_not_differentiableAt hd]
    rfl

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, the differential of a map into a normed space vanishes at `x` if
and only if the Fréchet derivative of its coordinate expression in the preferred extended chart
vanishes at `extChartAt I x x`. Both sides are `0` when the map is not differentiable at the
point. -/
theorem TauCeti.mfderiv_eq_zero_iff_fderiv_comp_extChartAt_symm :
    mfderiv I 𝓘(𝕜, F) f x = 0 ↔
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0 := by
  rw [← TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm]
  refine ⟨fun h ↦ by ext u; simp [mvfderiv, h]; rfl, fun h ↦ ?_⟩
  ext u
  exact congrArg (fun L ↦ L u) h

section SelfModel

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] {g : N → F} {z : N}

namespace ContMDiffAt

/-- On a manifold modelled on its model space, the preferred-chart coordinate expression of a
`C^n` map into a normed space is `C^n` at the chart image of the point. -/
theorem contDiffAt_comp_chartAt_symm {n : WithTop ℕ∞}
    (hg : ContMDiffAt 𝓘(𝕜, E) 𝓘(𝕜, F) n g z) :
    ContDiffAt 𝕜 n (g ∘ (chartAt E z).symm) (chartAt E z z) := by
  simpa only [TauCeti.extChartAt_model_symm_eq_chartAt_symm,
    TauCeti.extChartAt_model_apply_eq_chartAt_apply] using
    hg.contDiffAt_comp_extChartAt_symm

end ContMDiffAt

/-- On a manifold modelled on its model space, the derivative of the preferred-chart coordinate
expression is the vector-valued manifold derivative. Both sides are `0` when the map is not
differentiable at the point. -/
theorem TauCeti.fderiv_comp_chartAt_symm :
    fderiv 𝕜 (g ∘ (chartAt E z).symm) (chartAt E z z) = mvfderiv 𝓘(𝕜, E) g z := by
  rw [TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm,
    TauCeti.extChartAt_model_symm_eq_chartAt_symm, TauCeti.extChartAt_model_apply_eq_chartAt_apply]

/-- On a manifold modelled on its model space, the kernel of the vector-valued manifold derivative
is the kernel of the derivative of the preferred-chart coordinate expression, a subspace of the
model space. -/
theorem TauCeti.ker_mvfderiv_eq_ker_fderiv_comp_chartAt_symm :
    (mvfderiv 𝓘(𝕜, E) g z).ker = (fderiv 𝕜 (g ∘ (chartAt E z).symm) (chartAt E z z)).ker := by
  rw [TauCeti.fderiv_comp_chartAt_symm]
  -- The two sides are the kernel of the same map, viewed as a subspace of the tangent space
  -- `TangentSpace 𝓘(𝕜, E) z` and of `E`; these are the same space by definition.
  rfl

/-- On a manifold modelled on its model space, a map into a normed space whose coordinate
expression in a chart of the `C¹` maximal atlas is differentiable at a coordinate is manifold
differentiable at the corresponding point. -/
theorem TauCeti.mdifferentiableAt_of_differentiableAt_comp_symm {e : OpenPartialHomeomorph N E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 N) {w : E} (hw : w ∈ e.target)
    (hg : DifferentiableAt 𝕜 (g ∘ e.symm) w) :
    MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, F) g (e.symm w) := by
  rw [← e.right_inv hw] at hg
  refine (hg.mdifferentiableAt.comp _
    (mdifferentiableAt_of_mem_maximalAtlas he (e.map_target hw))).congr_of_eventuallyEq ?_
  filter_upwards [e.open_source.mem_nhds (e.map_target hw)] with y hy
  simp [e.left_inv hy]

end SelfModel

namespace TauCeti

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, `mvfderiv I f x`, read on the model space `E`, agrees with the
Fréchet derivative of the preferred coordinate expression at `extChartAt I x x`, even without a
differentiability hypothesis (both vanish when `f` is not differentiable at `x`). -/
theorem mvfderiv_comp_tangentSpaceCastModel_symm (f : M → F) (x : M) :
    (mvfderiv I f x).comp ((tangentSpaceCastModel I x).symm : E →L[𝕜] TangentSpace I x) =
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  ext v
  exact DFunLike.congr_fun (TauCeti.mvfderiv_eq_fderiv_comp_extChartAt_symm (I := I)) v

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, `mvfderiv I f x` evaluated on `v` equals the Fréchet derivative of
the preferred coordinate expression evaluated on `tangentSpaceCastModel I x v`, without any
differentiability assumption. -/
theorem mvfderiv_apply_eq_fderiv_comp_extChartAt_symm (f : M → F) (x : M)
    (v : TangentSpace I x) :
    mvfderiv I f x v =
      fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) (tangentSpaceCastModel I x v) := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, the range of `mvfderiv I f x` equals the range of the Fréchet
derivative of the preferred coordinate expression at `extChartAt I x x`. -/
theorem range_mvfderiv_eq_range_fderiv_comp_extChartAt_symm (f : M → F) (x : M) :
    (mvfderiv I f x).range = (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x)).range := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp_of_range_eq_top]
  exact LinearMap.range_eq_top.mpr (tangentSpaceCastModel I x).symm.surjective

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, injectivity of `mvfderiv I f x` is equivalent to injectivity of the
Fréchet derivative of the preferred coordinate expression at `extChartAt I x x`. -/
theorem injective_fderiv_comp_extChartAt_symm_iff :
    Function.Injective (fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x)) ↔
      Function.Injective (mvfderiv I f x) := by
  rw [← mvfderiv_comp_tangentSpaceCastModel_symm, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe]
  refine ⟨fun h u w huw ↦ ?_, fun h ↦ h.comp (tangentSpaceCastModel I x).symm.injective⟩
  exact (tangentSpaceCastModel I x).injective (h (by simpa using huw))

end TauCeti
end Boundaryless

/-! ### Preferred charts of a composite charted space -/

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [ChartedSpace H X]
  {N : Type*} [TopologicalSpace N] [ChartedSpace X N]

/-- For the composite charts `ChartedSpace.comp H X N` of a space charted over a charted space `X`,
the preferred `X`-valued chart at `x`, read in the composite chart at `x` and the chart of `X` at
its image, is the identity near the image of `x`. -/
theorem writtenInExtChartAt_chartAt_comp_eventuallyEq (x : N) :
    letI := ChartedSpace.comp H X N
    writtenInExtChartAt I I x (chartAt X x) =ᶠ[𝓝[range I] extChartAt I x x] id := by
  let := ChartedSpace.comp H X N
  filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
  exact writtenInExtChartAt_chartAt_comp x hy

/-- For the composite charts `ChartedSpace.comp H X N`, the preferred `X`-valued chart at `x` has
the identity as its manifold derivative at `x`. -/
theorem hasMFDerivAt_chartAt_comp (x : N) :
    letI := ChartedSpace.comp H X N
    HasMFDerivAt I I (chartAt X x) x (ContinuousLinearMap.id 𝕜 (TangentSpace I x)) := by
  let := ChartedSpace.comp H X N
  exact ⟨(chartAt X x).continuousAt (mem_chart_source X x),
    (hasFDerivWithinAt_id _ _).congr_of_eventuallyEq
      (writtenInExtChartAt_chartAt_comp_eventuallyEq x)
      (writtenInExtChartAt_chartAt_comp x (mem_extChartAt_target x))⟩

/-- For the composite charts `ChartedSpace.comp H X N`, the preferred `X`-valued chart at `x` is
`C^n` at `x`, for every `n`. -/
theorem contMDiffAt_chartAt_comp {n : WithTop ℕ∞} (x : N) :
    letI := ChartedSpace.comp H X N
    ContMDiffAt I I n (chartAt X x) x := by
  let := ChartedSpace.comp H X N
  exact contMDiffAt_iff.2 ⟨(chartAt X x).continuousAt (mem_chart_source X x),
    contDiffWithinAt_id.congr_of_eventuallyEq (writtenInExtChartAt_chartAt_comp_eventuallyEq x)
      (writtenInExtChartAt_chartAt_comp x (mem_extChartAt_target x))⟩

section ChartOverlap

/-- On a subset of a chart overlap, the derivative of the extended coordinate change is its
Fréchet derivative within the full model range, including at boundary and corner points. -/
theorem hasFDerivWithinAt_extChartAt_coordChange (α β : M) {s : Set M}
    (hsub : s ⊆ (extChartAt I α).source ∩ (extChartAt I β).source) :
    ∀ y ∈ (extChartAt I α) '' s,
      HasFDerivWithinAt ((extChartAt I α).symm ≫ extChartAt I β)
        (fderivWithin 𝕜 (extChartAt I β ∘ (extChartAt I α).symm) (Set.range I) y)
        ((extChartAt I α) '' s) y := by
  rintro _ ⟨x, hx, rfl⟩
  exact (hasFDerivWithinAt_tangentCoordChange (I := I) (hsub hx)).mono fun y hy ↦ by
    obtain ⟨z, -, rfl⟩ := hy
    exact mem_range_self _

end ChartOverlap

/-- On a subset of the chart target with unique derivatives, the derivative of the inverse chart
within the subset is its derivative within the model range. -/
theorem mfderivWithin_extChartAt_symm_of_subset (x₀ : M) {s : Set E}
    (hs : s ⊆ (extChartAt I x₀).target) (hsu : UniqueDiffOn 𝕜 s) {y : E} (hy : y ∈ s) :
    mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm s y =
      mfderivWithin 𝓘(𝕜, E) I (extChartAt I x₀).symm (range I) y :=
  mfderivWithin_subset (fun _ hz ↦ extChartAt_target_subset_range x₀ (hs hz))
    (hsu y hy).uniqueMDiffWithinAt (mdifferentiableWithinAt_extChartAt_symm (hs hy))

end TauCeti

namespace TauCeti

section NormedFieldCharts

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The derivative of a model-valued map in an arbitrary preferred chart is its actual
manifold derivative composed with the inverse tangent chart. -/
theorem _root_.MDifferentiableAt.fderivWithin_comp_extChartAt_symm {f : M → F} {x : M}
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) (α : M) (hx : x ∈ (extChartAt I α).source) :
    fderivWithin 𝕜 (f ∘ (extChartAt I α).symm) (range I) (extChartAt I α x) =
      -- Use the fixed model fibers to compose the derivative with the tangent chart.
      (show E →L[𝕜] F from mfderiv I 𝓘(𝕜, F) f x).comp
        (tangentCoordChange I α x x) := by
  have ht := (extChartAt I α).map_source hx
  have h := mfderiv_comp_mfderivWithin (I := 𝓘(𝕜, E)) (I' := I) (I'' := 𝓘(𝕜, F))
    (extChartAt I α x) (by simpa only [(extChartAt I α).left_inv hx] using hf)
    (mdifferentiableWithinAt_extChartAt_symm ht)
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α ht)
      |>.uniqueMDiffWithinAt)
  rw [(extChartAt I α).left_inv hx] at h
  have hx' : x ∈ (chartAt H α).source := by simpa only [extChartAt_source] using hx
  rw [← TangentBundle.symmL_trivializationAt hx',
    TangentBundle.symmL_trivializationAt_eq_core hx'] at h
  rw [mfderivWithin_eq_fderivWithin] at h
  -- The tangent spaces of normed model spaces reduce to their underlying normed spaces.
  convert! h using 1

/-- In a preferred chart, a manifold derivative from a normed source gives the ordinary
coordinate derivative by composing with the tangent chart. -/
theorem _root_.HasMFDerivAt.hasFDerivAt_extChartAt_comp {Q : F → M} {z : F} {α : M}
    {e : F →L[𝕜] TangentSpace I (Q z)}
    (hQ : HasMFDerivAt 𝓘(𝕜, F) I Q z
      (e.comp
        (NormedSpace.fromTangentSpace z).toContinuousLinearMap))
    (hx : Q z ∈ (chartAt H α).source) :
    HasFDerivAt (extChartAt I α ∘ Q)
      (((trivializationAt E (TangentSpace I) α).continuousLinearMapAt 𝕜 (Q z)).comp
        e) z := by
  let η := (trivializationAt E (TangentSpace I) α).continuousLinearEquivAt 𝕜 (Q z)
    (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)
  let L := η.toContinuousLinearMap.comp e
  have hη : η.toContinuousLinearMap = tangentCoordChange I (Q z) α (Q z) := by
    rw [Bundle.Trivialization.coe_continuousLinearEquivAt_eq',
      TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hx]
  have hη' : η.toContinuousLinearMap = mfderiv I I (chartAt H α) (Q z) := by
    rw [mfderiv_chartAt_eq_tangentCoordChange hx]
    exact hη
  have hd : HasFDerivAt (extChartAt I α ∘ Q) L z := by
    have h := (hasMFDerivAt_extChartAt (I := I) hx).comp z hQ
    -- Cancel the canonical source tangent identification in the derivative composition.
    refine h.hasFDerivAt.congr_fderiv ?_
    ext v
    rw [← hη']
    rfl
  have he : L =
      ((trivializationAt E (TangentSpace I) α).continuousLinearMapAt 𝕜 (Q z)).comp
        e := by
    rw [← Bundle.Trivialization.coe_continuousLinearEquivAt_eq' _
      (by simpa only [TangentBundle.trivializationAt_baseSet] using hx)]
  exact he ▸ hd

/-- Read in a preferred chart, the derivative of a map from a normed space is its manifold
derivative followed by the manifold derivative of the chart. -/
theorem _root_.MDifferentiableAt.fderiv_extChartAt_comp_apply {Q : F → M} {z : F} {α : M}
    (hQ : MDifferentiableAt 𝓘(𝕜, F) I Q z) (hz : Q z ∈ (extChartAt I α).source) (v : F) :
    fderiv 𝕜 (extChartAt I α ∘ Q) z v =
      mfderiv I 𝓘(𝕜, E) (extChartAt I α) (Q z) (mfderiv 𝓘(𝕜, F) I Q z v) := by
  have hz' : Q z ∈ (chartAt H α).source := by rwa [← extChartAt_source I]
  have h := congr($(mfderiv_comp z (mdifferentiableAt_extChartAt hz') hQ) v)
  rw [mfderiv_eq_fderiv] at h
  -- `mfderiv_eq_fderiv` only inserts the identifications of tangent spaces of `F` and `E`.
  exact h

end NormedFieldCharts

section ManifoldCharts

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' 1 N]

/-- The coordinate expression of a map between manifolds in arbitrary preferred charts at `β`
and `α` has, as its derivative within the model range, the manifold derivative composed with the
tangent coordinate changes of the two charts. -/
theorem _root_.MDifferentiableAt.fderivWithin_extChartAt_comp_extChartAt_symm {f : M → N}
    {x : M} (hf : MDifferentiableAt I I' f x) {β : M} {α : N}
    (hx : x ∈ (extChartAt I β).source) (hfx : f x ∈ (extChartAt I' α).source) :
    fderivWithin 𝕜 (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) (range I) (extChartAt I β x) =
      (tangentCoordChange I' (f x) α (f x) ∘L mfderiv I I' f x ∘L
        tangentCoordChange I β x x : E →L[𝕜] E') := by
  have hfx' : f x ∈ (chartAt H' α).source := by simpa only [extChartAt_source] using hfx
  have hα : MDifferentiableAt I' 𝓘(𝕜, E') (extChartAt I' α) (f x) :=
    mdifferentiableAt_extChartAt hfx'
  have h := (hα.comp x hf).fderivWithin_comp_extChartAt_symm β hx
  rw [mfderiv_comp x hα hf, (hasMFDerivAt_extChartAt hfx').mfderiv,
    mfderiv_chartAt_eq_tangentCoordChange hfx'] at h
  exact h

end ManifoldCharts

section InteriorCharts

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
  {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' n N]

/-- A map between manifolds which is `C^n` at the point with coordinate `y` in the preferred chart
at `β`, and sends it into the source of the preferred chart at `α`, is `C^n` at `y` when read in
these charts, provided `y` lies in the interior of the chart target. -/
theorem _root_.ContMDiffAt.contDiffAt_extChartAt_comp_extChartAt_symm {f : M → N} {β : M}
    {α : N} {y : E} (hf : ContMDiffAt I I' n f ((extChartAt I β).symm y))
    (hy : y ∈ interior (extChartAt I β).target)
    (hfy : f ((extChartAt I β).symm y) ∈ (extChartAt I' α).source) :
    ContDiffAt 𝕜 n (extChartAt I' α ∘ f ∘ (extChartAt I β).symm) y := by
  have hfs : f ((extChartAt I β).symm y) ∈ (chartAt H' α).source := by
    rwa [← extChartAt_source (I := I')]
  have hβs : (extChartAt I β).symm y ∈ (chartAt H β).source := by
    rw [← extChartAt_source (I := I)]
    exact (extChartAt I β).map_target (interior_subset hy)
  have h := ((contMDiffAt_iff_of_mem_source hβs hfs).1 hf).2
  rw [(extChartAt I β).right_inv (interior_subset hy)] at h
  exact h.contDiffAt (Filter.mem_of_superset (isOpen_interior.mem_nhds hy)
    (interior_subset.trans (extChartAt_target_subset_range β)))

end InteriorCharts

section RCLikeCharts

variable {𝕜 E H M E' H' M' : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} [TopologicalSpace M'] [ChartedSpace H' M']

/-- A map out of a manifold without boundary that is `C¹` at `y`, read in the extended charts at
`y` and at `f y`, has a strict derivative at the image of `y`. -/
theorem _root_.ContMDiffAt.hasStrictFDerivAt_extChartAt_conj {f : M → M'} {y : M}
    (hf : ContMDiffAt I I' 1 f y) :
    HasStrictFDerivAt (extChartAt I' (f y) ∘ f ∘ (extChartAt I y).symm)
      (fderiv 𝕜 (extChartAt I' (f y) ∘ f ∘ (extChartAt I y).symm) (extChartAt I y y))
      (extChartAt I y y) :=
  hf.contDiffAt_writtenInExtChartAt.hasStrictFDerivAt_fderiv one_ne_zero

end RCLikeCharts

section ModelSpaceSource

variable {𝕜 E F N : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace N] [ChartedSpace E N]

/-- A map from a normed space into a manifold modelled on a normed space, differentiable at `x`,
read in the preferred chart at its image, is differentiable at `x`. -/
theorem _root_.MDifferentiableAt.differentiableAt_chartAt_comp {g : F → N} {x : F}
    (hg : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, E) g x) :
    DifferentiableAt 𝕜 (chartAt E (g x) ∘ g) x := by
  have h := hg.hasMFDerivAt.2.differentiableWithinAt
  simpa [writtenInExtChartAt, differentiableWithinAt_univ] using h

/-- For a normed source and a manifold modelled on a normed space, the derivative in the
preferred chart at the image is the manifold derivative, using the canonical tangent-space
identifications. -/
theorem _root_.MDifferentiableAt.fderiv_chartAt_comp {g : F → N} {x : F}
    (hg : MDifferentiableAt 𝓘(𝕜, F) 𝓘(𝕜, E) g x) :
    fderiv 𝕜 (chartAt E (g x) ∘ g) x =
      (mfderiv 𝓘(𝕜, F) 𝓘(𝕜, E) g x).comp
        (NormedSpace.fromTangentSpace (𝕜 := 𝕜) x).symm.toContinuousLinearMap := by
  -- For the self model, the extended chart is the chart itself, and tangent spaces of normed
  -- spaces have the canonical identity equivalence with their underlying spaces.
  ext v
  simpa [writtenInExtChartAt] using! congrArg (fun L => L v) hg.mfderiv.symm

end ModelSpaceSource

section ProductCharts

open Filter

variable {𝕜 E F K M N P : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup K] [NormedSpace 𝕜 K]
  [TopologicalSpace M] [ChartedSpace E M] [TopologicalSpace N] [ChartedSpace F N]
  [TopologicalSpace P] [ChartedSpace K P]

/-- The representative of a map differentiable near a point in maximal-atlas product charts is
Fréchet differentiable near the corresponding model-space point. -/
theorem eventually_differentiableAt_chart_comp_of_eventually_mdifferentiableAt
    {G : M × N → P} {u : M × N}
    {e : OpenPartialHomeomorph M E} {d : OpenPartialHomeomorph N F}
    {c : OpenPartialHomeomorph P K}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) 1 N)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, K) 1 P)
    (hu : u.1 ∈ e.source) (hv : u.2 ∈ d.source) (hw : G u ∈ c.source)
    (hG : ∀ᶠ q in 𝓝 u, MDifferentiableAt (𝓘(𝕜, E).prod 𝓘(𝕜, F)) 𝓘(𝕜, K) G q) :
    ∀ᶠ q in 𝓝 (e u.1, d u.2),
      DifferentiableAt 𝕜 (fun q : E × F ↦ c (G (e.symm q.1, d.symm q.2))) q := by
  have hback : Tendsto (fun q : E × F ↦ (e.symm q.1, d.symm q.2))
      (𝓝 (e u.1, d u.2)) (𝓝 u) :=
    (e.tendsto_symm hu).prodMap_nhds (d.tendsto_symm hv)
  have hgc : ContinuousAt G u := hG.self_of_nhds.continuousAt
  filter_upwards [(continuous_fst.tendsto (e u.1, d u.2)).eventually
    (e.open_target.mem_nhds (e.map_source hu)),
    (continuous_snd.tendsto (e u.1, d u.2)).eventually
      (d.open_target.mem_nhds (d.map_source hv)),
    hback.eventually hG,
    (hgc.tendsto.comp hback).eventually (c.open_source.mem_nhds hw)] with q hqe hqd hqG hqc
  have hq := (mdifferentiableAt_of_mem_maximalAtlas hc hqc).comp q
    (hqG.comp q
      (((mdifferentiableAt_symm_of_mem_maximalAtlas he hqe).comp q mdifferentiableAt_fst).prodMk
        ((mdifferentiableAt_symm_of_mem_maximalAtlas hd hqd).comp q mdifferentiableAt_snd)))
  apply mdifferentiableAt_iff_differentiableAt.1
  rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
  exact hq

/-- Pulling a map differentiable near a model-space point back through maximal-atlas product
charts gives a map differentiable near the original point, provided its value lies in the target
of the output chart. -/
theorem eventually_mdifferentiableAt_chart_symm_comp_of_eventually_differentiableAt
    {φ : E × K → F} {u : M × P}
    {e : OpenPartialHomeomorph M E} {d : OpenPartialHomeomorph N F}
    {c : OpenPartialHomeomorph P K}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) 1 M)
    (hd : d ∈ IsManifold.maximalAtlas 𝓘(𝕜, F) 1 N)
    (hc : c ∈ IsManifold.maximalAtlas 𝓘(𝕜, K) 1 P)
    (hu : u.1 ∈ e.source) (hw : u.2 ∈ c.source)
    (hφ : ∀ᶠ q in 𝓝 (e u.1, c u.2), DifferentiableAt 𝕜 φ q)
    (ht : φ (e u.1, c u.2) ∈ d.target) :
    ∀ᶠ p in 𝓝 u, MDifferentiableAt (𝓘(𝕜, E).prod 𝓘(𝕜, K)) 𝓘(𝕜, F)
      (fun p : M × P ↦ d.symm (φ (e p.1, c p.2))) p := by
  have hfront : Tendsto (fun p : M × P ↦ (e p.1, c p.2))
      (𝓝 u) (𝓝 (e u.1, c u.2)) :=
    (e.continuousAt hu).prodMap_nhds (c.continuousAt hw)
  have htarget := (hφ.self_of_nhds.continuousAt.tendsto.comp hfront).eventually
    (d.open_target.mem_nhds ht)
  filter_upwards [hfront.eventually hφ, htarget,
    (continuous_fst.tendsto u).eventually (e.open_source.mem_nhds hu),
    (continuous_snd.tendsto u).eventually (c.open_source.mem_nhds hw)]
    with p hp hpt hpe hpc
  exact (mdifferentiableAt_symm_of_mem_maximalAtlas hd hpt).comp p
    (hp.mdifferentiableAt.comp p
      ((mdifferentiableAt_prod_module_iff _).2
        ⟨(mdifferentiableAt_of_mem_maximalAtlas he hpe).comp p mdifferentiableAt_fst,
          (mdifferentiableAt_of_mem_maximalAtlas hc hpc).comp p mdifferentiableAt_snd⟩))

end ProductCharts

end TauCeti

section ConstancyCoordinates

namespace MDifferentiableAt

variable {f : M → M'}

/-- The chain rule transfers a vanishing manifold differential to the coordinate expression
`extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm`, computed within the model range: at a point `u`
of the chart target whose image `(extChartAt I x).symm u` is a point of differentiability of `f`
with zero differential, mapped into the source of the target chart, the expression is
differentiable within the range with zero derivative. -/
theorem differentiableWithinAt_and_fderivWithin_extChartAt_comp_eq_zero {x : M} {u : E}
    (hu1 : u ∈ (extChartAt I x).target) (hfu : MDifferentiableAt I I' f ((extChartAt I x).symm u))
    (hzero : mfderiv I I' f ((extChartAt I x).symm u) = 0)
    (hu3 : f ((extChartAt I x).symm u) ∈ (extChartAt I' (f x)).source) :
    DifferentiableWithinAt 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I) u ∧
      fderivWithin 𝕜 (extChartAt I' (f x) ∘ f ∘ (extChartAt I x).symm) (range I) u = 0 := by
  let c := extChartAt I x
  let d := extChartAt I' (f x)
  have hc : MDifferentiableWithinAt 𝓘(𝕜, E) I c.symm (range I) u :=
    mdifferentiableWithinAt_extChartAt_symm hu1
  have hd : MDifferentiableAt I' 𝓘(𝕜, E') d (f (c.symm u)) :=
    mdifferentiableAt_extChartAt (by
      simpa only [mem_preimage, d, extChartAt_source] using hu3)
  refine ⟨((hd.comp _ hfu).comp_mdifferentiableWithinAt _ hc).differentiableWithinAt, ?_⟩
  have h := (hd.comp _ hfu).fderivWithin_comp_extChartAt_symm x (c.map_target hu1)
  rw [c.right_inv hu1, mfderiv_comp _ hd hfu, hzero, ContinuousLinearMap.comp_zero] at h
  exact h.trans (ContinuousLinearMap.zero_comp _)

end MDifferentiableAt

end ConstancyCoordinates

namespace TauCeti

section ExtChartAtSelf

omit [IsManifold I 1 M] in
/-- The preferred extended chart at `x` has the identity as its manifold derivative at `x`. This
is `mfderiv_extChartAt_self` without any smoothness hypothesis on the atlas, in the form of a
`HasMFDerivAt` statement. -/
theorem hasMFDerivAt_extChartAt_self (x : M) :
    HasMFDerivAt I 𝓘(𝕜, E) (extChartAt I x) x (ContinuousLinearMap.id 𝕜 E) :=
  ⟨continuousAt_extChartAt x,
    (hasFDerivWithinAt_id (extChartAt I x x) (range I)).congr_of_eventuallyEq
    (Filter.eventuallyEq_of_mem (extChartAt_target_mem_nhdsWithin x)
      fun _ h ↦ writtenInExtChartAt_extChartAt h)
    (writtenInExtChartAt_extChartAt (mem_extChartAt_target x))⟩

omit [IsManifold I 1 M] in
/-- The manifold derivative of the preferred extended chart at its centre is the identity, with no
smoothness hypothesis on the atlas. -/
theorem mfderiv_extChartAt_eq_id (x : M) :
    mfderiv I 𝓘(𝕜, E) (extChartAt I x) x = ContinuousLinearMap.id 𝕜 E :=
  (hasMFDerivAt_extChartAt_self x).mfderiv

end ExtChartAtSelf

section TimeDerivative

/-! ### The derivative along the scalar factor of `M × 𝕜` -/

open Filter

variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace X]
  [ChartedSpace H X] {f : X × 𝕜 → F}

/-- **The derivative along `𝕜` in coordinates.** At the chart image of a point `(x, s)` of the
chart source, the derivative of the coordinate expression of `f : X × 𝕜 → F` in the direction
`(0, 1)` is the derivative of the slice of `f` through `x`. -/
theorem fderiv_comp_extChartAt_symm_apply_zero_one {z : X × 𝕜} {x : X} {s : 𝕜}
    (hx : x ∈ (extChartAt I z.1).source)
    (hf : DifferentiableAt 𝕜 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z).symm) (extChartAt I z.1 x, s)) :
    fderiv 𝕜 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z).symm) (extChartAt I z.1 x, s) (0, 1) =
      deriv (fun s' ↦ f (x, s')) s := by
  have h : HasDerivAt (fun s' : 𝕜 ↦ (extChartAt I z.1 x, s')) ((0 : E), (1 : 𝕜)) s :=
    HasDerivAt.prodMk (hasDerivAt_const _ _) (hasDerivAt_id _)
  rw [← comp_extChartAt_symm_prodMk_left z hx]
  exact ((hf.hasFDerivAt.comp_hasDerivAt s h).deriv).symm

/-- **The derivative along `𝕜` near a point, in coordinates.** Near a point `z₀` at which
`f : X × 𝕜 → F` is `C¹`, the derivative of `f` along `𝕜` at `(x, t)` is the derivative of the
coordinate expression of `f` in the preferred chart at `z₀`, in the direction `(0, 1)`, at the chart
image `(φ x, t)` of `(x, t)`. -/
theorem deriv_prodMk_eventuallyEq_fderiv {z₀ : X × 𝕜}
    (hf : ContDiffAt 𝕜 1 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z₀).symm)
      (extChartAt I z₀.1 z₀.1, z₀.2)) :
    (fun z : X × 𝕜 ↦ deriv (fun s ↦ f (z.1, s)) z.2) =ᶠ[𝓝 z₀]
      fun z ↦ fderiv 𝕜 (f ∘ (extChartAt (I.prod 𝓘(𝕜)) z₀).symm)
        (extChartAt I z₀.1 z.1, z.2) (0, 1) := by
  have hφ : ContinuousAt (fun z : X × 𝕜 ↦ (extChartAt I z₀.1 z.1, z.2)) z₀ :=
    ((continuousAt_extChartAt z₀.1).comp continuousAt_fst).prodMk continuousAt_snd
  filter_upwards [continuousAt_fst.preimage_mem_nhds (extChartAt_source_mem_nhds (I := I) z₀.1),
    hφ.eventually (hf.eventually (by simp))] with z hz hzG
  exact (fderiv_comp_extChartAt_symm_apply_zero_one hz (hzG.differentiableAt one_ne_zero)).symm

variable [I.Boundaryless]

/-- **The derivative along `𝕜` of a `C^(n + 1)` function on `X × 𝕜` is `C^n`.** On a boundaryless
manifold `X`, the map `(x, t) ↦ ∂ₜ f (x, t)` is `C^n`; near each point it is the derivative of the
coordinate expression of `f` in the direction of the last factor, which is unchanged by the charts.
-/
theorem _root_.ContMDiff.contMDiff_deriv_prodMk {n : WithTop ℕ∞}
    (hf : ContMDiff (I.prod 𝓘(𝕜)) 𝓘(𝕜, F) (n + 1) f) :
    ContMDiff (I.prod 𝓘(𝕜)) 𝓘(𝕜, F) n fun z : X × 𝕜 ↦ deriv (fun s ↦ f (z.1, s)) z.2 := by
  intro z₀
  set G := f ∘ (extChartAt (I.prod 𝓘(𝕜)) z₀).symm with hG
  have hG₀ : ContDiffAt 𝕜 (n + 1) G (extChartAt I z₀.1 z₀.1, z₀.2) := by
    simpa [hG, extChartAt_prod_modelSpace_apply] using
      contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.1 (hf z₀)
  -- The chart image `(φ x, t)` of `(x, t)` depends smoothly on `(x, t)` near `z₀`.
  have hφ : ContMDiffAt (I.prod 𝓘(𝕜)) 𝓘(𝕜, E × 𝕜) n
      (fun z : X × 𝕜 ↦ (extChartAt I z₀.1 z.1, z.2)) z₀ :=
    (contMDiffAt_extChartAt.comp z₀ contMDiffAt_fst).prodMk_space contMDiffAt_snd
  refine ContMDiffAt.congr_of_eventuallyEq ?_
    (deriv_prodMk_eventuallyEq_fderiv (hG₀.of_le le_add_self))
  exact ((hG₀.fderiv_right le_rfl).clm_apply contDiffAt_const).contMDiffAt.comp z₀ hφ

/-- **The derivative along `𝕜` of a `C¹` function on `X × 𝕜` is continuous.** On a boundaryless
manifold `X`, the map `(x, t) ↦ ∂ₜ f (x, t)` is continuous; near each point it is the derivative of
the coordinate expression of `f` in the direction of the last factor, which is unchanged by the
charts. -/
theorem _root_.ContMDiff.continuous_deriv_prodMk (hf : ContMDiff (I.prod 𝓘(𝕜)) 𝓘(𝕜, F) 1 f) :
    Continuous fun z : X × 𝕜 ↦ deriv (fun s ↦ f (z.1, s)) z.2 :=
  (hf.contMDiff_deriv_prodMk (n := 0)).continuous

end TimeDerivative

end TauCeti
