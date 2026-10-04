/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

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

* `HasMFDerivAt.hasFDerivWithinAt_of_mem_source`: the derivative of `f` read in the extended
  charts at `x` and `y`.
* `ContMDiffAt.contDiffAt_comp_extChartAt_symm` and
  `MDifferentiableAt.differentiableAt_comp_extChartAt_symm`: on a boundaryless manifold, the
  coordinate expression of a `C^n` (resp. differentiable) map into a normed space is `C^n` (resp.
  differentiable) at the chart image of the point.
* `MDifferentiableAt.mvfderiv_eq_fderiv_comp_extChartAt_symm`: on a boundaryless manifold, the
  vector-valued manifold derivative is the Fréchet derivative of the coordinate expression.
* `TauCeti.writtenInExtChartAt_chartAt_comp_eventuallyEq`, `TauCeti.hasMFDerivAt_chartAt_comp` and
  `TauCeti.contMDiffAt_chartAt_comp`: for a space charted over a charted space `X`, with the
  composite charts, the preferred `X`-valued chart at `x` reads as the identity near `x`, so it is
  smooth at `x` with the identity as its derivative there.
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

/-! ### Maps into a normed space on a boundaryless manifold -/

section Boundaryless

variable [I.Boundaryless] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : M → F} {x : M}

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space which is `C^n` at `x` has a `C^n`
coordinate expression in the preferred extended chart at `x`. -/
theorem _root_.ContMDiffAt.contDiffAt_comp_extChartAt_symm {n : WithTop ℕ∞}
    (hf : ContMDiffAt I 𝓘(𝕜, F) n f x) :
    ContDiffAt 𝕜 n (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have h := (contMDiffAt_iff.1 hf).2
  rwa [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ,
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at h

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, a map into a normed space which is differentiable at `x` has a
differentiable coordinate expression in the preferred extended chart at `x`. -/
theorem _root_.MDifferentiableAt.differentiableAt_comp_extChartAt_symm
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    DifferentiableAt 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have h := ((mdifferentiableAt_iff f x).1 hf).2
  rwa [ModelWithCorners.Boundaryless.range_eq_univ, differentiableWithinAt_univ,
    writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
    Function.id_comp] at h

omit [IsManifold I 1 M] in
/-- On a boundaryless manifold, the vector-valued manifold derivative of a map into a normed space
is the Fréchet derivative of its coordinate expression in the preferred extended chart. -/
theorem _root_.MDifferentiableAt.mvfderiv_eq_fderiv_comp_extChartAt_symm
    (hf : MDifferentiableAt I 𝓘(𝕜, F) f x) :
    mvfderiv I f x = fderiv 𝕜 (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  rw [hf.mvfderiv, ModelWithCorners.Boundaryless.range_eq_univ, fderivWithin_univ,
    writtenInExtChartAt, extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]

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

end TauCeti
