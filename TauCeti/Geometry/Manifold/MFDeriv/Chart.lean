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

## Main results

* `HasMFDerivAt.hasFDerivWithinAt_of_mem_source`: the derivative of `f` read in the extended
  charts at `x` and `y`.
-/

public section

open Set
open scoped Manifold

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
