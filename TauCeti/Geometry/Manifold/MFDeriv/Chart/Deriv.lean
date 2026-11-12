/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# First and second derivatives of one-dimensional maps read in charts

Let `M`, `M'` and `M''` be boundaryless manifolds modelled on the field `𝕜` itself, such as Riemann
surfaces over `ℂ`. A map `f : M → M'` read in the extended charts at `x` and at `f x` is a map
`𝕜 → 𝕜`, with an ordinary derivative and second derivative at the chart coordinate of `x`.

* The derivative of the chart expression is the manifold derivative on the tangent vector `1`
  (`MDifferentiableAt.mfderiv_apply_one_eq_deriv_writtenInExtChartAt`).
* **Chain rules.** Read in the preferred charts, the derivative of `g ∘ f` at `x` is
  `g'(f x) f'(x)` (`TauCeti.Manifold.deriv_writtenInExtChartAt_comp`), while its second derivative
  is `g''(f x) f'(x) ^ 2 + g'(f x) f''(x)`
  (`TauCeti.Manifold.iteratedDeriv_two_writtenInExtChartAt_comp`). So second derivatives in charts
  do not transform linearly under reparametrization of the source or the target; these are the
  transition laws of second jets in charts.
-/

public section

open Set Filter
open scoped Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 𝕜 H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 𝕜 H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 𝕜 H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {g : M' → M''} {x : M}

/-- On a boundaryless source modelled on `𝕜`, the manifold derivative on the tangent vector `1` is
the derivative of the coordinate expression in the extended charts at `x` and at `f x`. -/
theorem MDifferentiableAt.mfderiv_apply_one_eq_deriv_writtenInExtChartAt
    (hf : MDifferentiableAt I I' f x) :
    (mfderiv I I' f x (1 : 𝕜) : 𝕜) = deriv (writtenInExtChartAt I I' x f) (extChartAt I x x) := by
  rw [hf.mfderiv_eq_fderiv_extChartAt_conj rfl]
  rfl

namespace TauCeti.Manifold

/-- On a boundaryless source, the coordinate expression of `g ∘ f` is the composition of the
coordinate expressions of `g` and `f` near the chart coordinate of `x`. -/
private theorem writtenInExtChartAt_comp_eventuallyEq (hf : ContinuousAt f x) :
    writtenInExtChartAt I I'' x (g ∘ f) =ᶠ[𝓝 (extChartAt I x x)]
      writtenInExtChartAt I' I'' (f x) g ∘ writtenInExtChartAt I I' x f := by
  simpa only [preimage_univ, univ_inter, I.range_eq_univ, nhdsWithin_univ] using
    writtenInExtChartAt_comp (I := I) (I' := I') (I'' := I'') (s := univ) (g := g)
      hf.continuousWithinAt

omit [I.Boundaryless] in
/-- The coordinate expression of `f` at `x` sends the chart coordinate of `x` to that of `f x`. -/
private theorem writtenInExtChartAt_extChartAt_self :
    writtenInExtChartAt I I' x f (extChartAt I x x) = extChartAt I' (f x) (f x) := by
  simp [writtenInExtChartAt]

/-- **The chain rule in charts.** Read in the preferred charts, the derivative of `g ∘ f` at `x` is
`g'(f x) f'(x)`. -/
theorem deriv_writtenInExtChartAt_comp [I'.Boundaryless] (hg : MDifferentiableAt I' I'' g (f x))
    (hf : MDifferentiableAt I I' f x) :
    deriv (writtenInExtChartAt I I'' x (g ∘ f)) (extChartAt I x x) =
      deriv (writtenInExtChartAt I' I'' (f x) g) (extChartAt I' (f x) (f x)) *
        deriv (writtenInExtChartAt I I' x f) (extChartAt I x x) := by
  have hg' := hg.differentiableAt_writtenInExtChartAt
  rw [← writtenInExtChartAt_extChartAt_self (I := I) (I' := I') (f := f) (x := x)] at hg' ⊢
  rw [(writtenInExtChartAt_comp_eventuallyEq (I' := I') (I'' := I'') (g := g)
      hf.continuousAt).deriv_eq,
    deriv_comp _ hg' hf.differentiableAt_writtenInExtChartAt]

/-- **The second-order chain rule in charts.** Read in the preferred charts, the second derivative
of `g ∘ f` at `x` is `g''(f x) f'(x) ^ 2 + g'(f x) f''(x)`. -/
theorem iteratedDeriv_two_writtenInExtChartAt_comp [I'.Boundaryless]
    (hg : ContMDiffAt I' I'' 2 g (f x)) (hf : ContMDiffAt I I' 2 f x) :
    iteratedDeriv 2 (writtenInExtChartAt I I'' x (g ∘ f)) (extChartAt I x x) =
      iteratedDeriv 2 (writtenInExtChartAt I' I'' (f x) g) (extChartAt I' (f x) (f x)) *
          deriv (writtenInExtChartAt I I' x f) (extChartAt I x x) ^ 2 +
        deriv (writtenInExtChartAt I' I'' (f x) g) (extChartAt I' (f x) (f x)) *
          iteratedDeriv 2 (writtenInExtChartAt I I' x f) (extChartAt I x x) := by
  have hg' := hg.contDiffAt_writtenInExtChartAt
  rw [← writtenInExtChartAt_extChartAt_self (I := I) (I' := I') (f := f) (x := x)] at hg' ⊢
  rw [(writtenInExtChartAt_comp_eventuallyEq (I' := I') (I'' := I'') (g := g)
      hf.continuousAt).iteratedDeriv_eq,
    iteratedDeriv_comp_two hg' hf.contDiffAt_writtenInExtChartAt]

end TauCeti.Manifold
