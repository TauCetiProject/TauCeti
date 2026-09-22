/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame

/-!
# Covariant differentiation on a parametrized surface

A *parametrized surface* in a manifold `M` is a map `f` of two scalar parameters, here written in
curried form so that `f u` and `fun q ↦ f q v` are the two families of parameter curves through
the point `f u v`.  Each family carries a velocity field: `fun r ↦ γ'(u)` for `γ = fun q ↦ f q r`
is a section of the tangent bundle along the curve `f u`, and symmetrically with the two
parameters exchanged.  These are the fields written `∂f/∂u` and `∂f/∂v` in the classical notation,
and differentiating them covariantly along the *other* parameter curve is the two-parameter
operation on which variational arguments rest.

This file computes that mixed derivative in a chart and proves that it is symmetric in the two
parameters: `D/∂v (∂f/∂u) = D/∂u (∂f/∂v)` for a torsion-free connection.  In a chart the mixed
derivative is `∂²f/∂v∂u + Γ (∂f/∂u, ∂f/∂v)`, so the symmetry comes from two independent
symmetries: iterated partial derivatives of the chart reading commute, and the Christoffel map of
a torsion-free connection is a symmetric bilinear map.  Both partial velocity fields are read
through the moving-chart operator `CovariantDerivative.alongCurve` of `AlongCurve/Basic.lean`.

The symmetry is what lets the radial derivative of a family `exp_p (t • v s)` be exchanged with
its transverse derivative, and in that form it is the step behind the Gauss lemma and the
first-variation formula for the energy of a curve.

## Main results

* `CovariantDerivative.alongCurveInChartWithin_curveVelocity_fst` and
  `CovariantDerivative.alongCurveInChartWithin_curveVelocity_snd`: the moving-chart coordinate
  formula for the field of first-parameter velocities along a second-parameter curve is the
  classical expression `∂²f/∂v∂u + Γ (∂f/∂u, ∂f/∂v)`, and symmetrically with the two parameters
  exchanged.
* `TauCeti.Manifold.differentiableAt_sectionCoord_curveVelocity_fst` and
  `TauCeti.Manifold.differentiableAt_sectionCoord_curveVelocity_snd`: the corresponding
  coordinate readings are differentiable when the surface is `C²`.
* `CovariantDerivative.alongCurve_curveVelocity_comm`: **the symmetry lemma**, that for a
  torsion-free connection the two mixed covariant derivatives of a `C²` parametrized surface
  agree.

## References

* M. P. do Carmo, *Riemannian Geometry*, Birkhauser, 1992, Ch. 3, §3, Lemma 3.4, the symmetry
  lemma preceding the Gauss lemma.
* J. M. Lee, *Introduction to Riemannian Manifolds*, GTM 176, 2nd ed., 2018, Lemma 6.2.
-/

public section

open Bundle Filter Module Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {f : 𝕜 → 𝕜 → M} {u v : 𝕜} {x : M}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- Near `v`, the coordinate reading in the chart at `x` of the field of first-parameter
velocities of the surface `f` along the curve `f u` is the first partial derivative of the surface
read in that chart. -/
private theorem sectionCoord_curveVelocity_fst_eventuallyEq
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 1 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    sectionCoord (F := E) (f u) (fun r ↦ curveVelocity I (fun q ↦ f q r) u) x =ᶠ[𝓝 v]
      fun r ↦ deriv (fun q ↦ extChartAt I x (f q r)) u := by
  obtain ⟨w, hw, hfw⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hf
  obtain ⟨w', hw'w, hw'open, hw'mem⟩ := mem_nhds_iff.mp hw
  have hslice : Continuous fun r : 𝕜 ↦ ((u, r) : 𝕜 × 𝕜) := by fun_prop
  have hmemw : ∀ᶠ r in 𝓝 v, (u, r) ∈ w' :=
    hslice.continuousAt.preimage_mem_nhds (hw'open.mem_nhds hw'mem)
  have hbase : ∀ᶠ r in 𝓝 v, f u r ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    (hf.continuousAt.comp hslice.continuousAt).preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx)
  filter_upwards [hmemw, hbase] with r hr hrbase
  -- At a parameter where the surface is still differentiable, the first parameter curve through
  -- it is differentiable, so its velocity reads in the chart as the derivative of the chart
  -- reading of that curve.
  have hdiff : MDifferentiableAt 𝓘(𝕜, 𝕜) I (fun q ↦ f q r) u :=
    (((hfw.mono hw'w).contMDiffAt (hw'open.mem_nhds hr)).comp u
      (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 1) r)).contMDiffAt)
      |>.mdifferentiableAt one_ne_zero
  have hread := derivWithin_extChartAt_comp (x := x) (s := univ) (fun q ↦ f q r) hrbase
    uniqueDiffWithinAt_univ (hasMFDerivAt_curveVelocity hdiff).hasMFDerivWithinAt
  rw [derivWithin_univ] at hread
  rw [sectionCoord_apply, ← hread, Function.comp_def]

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- A parametrized surface which is `Cⁿ` at `(u, v)` reads in the chart at `x` as a `Cⁿ` map of
its two parameters, as soon as that chart is defined at the point `f u v`. -/
private theorem contDiffAt_extChartAt_comp_surface {n : ℕ∞ω} [IsManifold I n M]
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I n (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    ContDiffAt 𝕜 n (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2)) (u, v) := by
  have hxsrc : f u v ∈ (chartAt H x).source := by
    rwa [TangentBundle.trivializationAt_baseSet] at hx
  have hcomp : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) 𝓘(𝕜, E) n
      (extChartAt I x ∘ fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v) :=
    (contMDiffAt_extChartAt' (I := I) (n := n) hxsrc).comp (u, v) hf
  rw [Function.comp_def] at hcomp
  exact contMDiffAt_iff_contDiffAt.mp hcomp

/-- **The chart formula for the mixed derivative of a parametrized surface.**  Reading the surface
`f` in the extended chart at `x`, the moving-chart coordinate formula for the field of
first-parameter velocities along the second-parameter curve `f u` is the classical second-order
expression `∂²f/∂v∂u + Γ (∂f/∂u, ∂f/∂v)`.  The chart need not be the one centred at the point
`f u v` of the surface. -/
theorem alongCurveInChartWithin_curveVelocity_fst
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 1 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    alongCurveInChartWithin cov (f u) (fun r ↦ curveVelocity I (fun q ↦ f q r) u) univ x v =
      deriv (fun r ↦ deriv (fun q ↦ extChartAt I x (f q r)) u) v +
        christoffelMap (finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
          (f u v) (deriv (fun q ↦ extChartAt I x (f q v)) u)
          (deriv (fun r ↦ extChartAt I x (f u r)) v) := by
  have hcoord := sectionCoord_curveVelocity_fst_eventuallyEq hf hx
  rw [alongCurveInChartWithin_apply, derivWithin_univ, derivWithin_univ, hcoord.deriv_eq,
    hcoord.self_of_nhds, Function.comp_def]

/-- **The chart formula for the mixed derivative of a parametrized surface**, with the two
parameters exchanged: the moving-chart coordinate formula for the field of second-parameter
velocities along the first-parameter curve `fun q ↦ f q v` is `∂²f/∂u∂v + Γ (∂f/∂v, ∂f/∂u)`.
The chart need not be the one centred at the point `f u v` of the surface. -/
theorem alongCurveInChartWithin_curveVelocity_snd
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 1 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    alongCurveInChartWithin cov (fun q ↦ f q v) (fun q ↦ curveVelocity I (f q) v) univ x u =
      deriv (fun q ↦ deriv (fun r ↦ extChartAt I x (f q r)) v) u +
        christoffelMap (finBasis 𝕜 E)
          (cov.isCovariantDerivativeOn (s := (trivializationAt E (TangentSpace I) x).baseSet))
          (f u v) (deriv (fun r ↦ extChartAt I x (f u r)) v)
          (deriv (fun q ↦ extChartAt I x (f q v)) u) :=
  -- The surface with its two parameters exchanged has the first-parameter velocity field of this
  -- statement as its second-parameter one.
  alongCurveInChartWithin_curveVelocity_fst (f := fun a b ↦ f b a) (u := v) (v := u) cov
    (hf.comp (v, u) (contMDiff_iff_contDiff.mpr
      (by fun_prop : ContDiff 𝕜 1 fun z : 𝕜 × 𝕜 ↦ (z.2, z.1))).contMDiffAt) hx

variable [IsManifold I (minSmoothness 𝕜 2) M]

/-- **The symmetry lemma.**  For a torsion-free connection and a parametrized surface `f` which is
smooth enough at `(u, v)` for its chart reading to have a symmetric second derivative, the
covariant derivative along `f u` of the first-parameter velocity field agrees with the covariant
derivative along `fun q ↦ f q v` of the second-parameter velocity field: in the classical
notation, `D/∂v (∂f/∂u) = D/∂u (∂f/∂v)`. -/
theorem alongCurve_curveVelocity_comm
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    (hcov : cov.IsTorsionFree)
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I (minSmoothness 𝕜 2)
      (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v)) :
    alongCurve cov (f u) (fun r ↦ curveVelocity I (fun q ↦ f q r) u) v =
      alongCurve cov (fun q ↦ f q v) (fun q ↦ curveVelocity I (f q) v) u := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hone : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 1 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v) :=
    hf.of_le (le_trans (by norm_num) le_minSmoothness)
  have hbase : f u v ∈ (trivializationAt E (TangentSpace I) (f u v)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f u v)
  have hchart := contDiffAt_extChartAt_comp_surface hf hbase
  rw [alongCurve_apply, alongCurve_apply,
    alongCurveInChartWithin_curveVelocity_fst cov hone hbase,
    alongCurveInChartWithin_curveVelocity_snd cov hone hbase,
    deriv_deriv_comm hchart,
    christoffelMap_comm hcov (finBasis 𝕜 E) (f u v) (mem_extChartAt_source (f u v))]

end CovariantDerivative

namespace TauCeti.Manifold

open CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {f : 𝕜 → 𝕜 → M} {u v : 𝕜} {x : M}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The coordinate reading of the first-parameter velocity field of a `C²` parametrized surface is
differentiable along the second-parameter curve. -/
theorem differentiableAt_sectionCoord_curveVelocity_fst [IsManifold I 2 M]
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 2 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    DifferentiableAt 𝕜
      (sectionCoord (F := E) (f u) (fun r ↦ curveVelocity I (fun q ↦ f q r) u) x) v := by
  have hcoord := sectionCoord_curveVelocity_fst_eventuallyEq (hf.of_le (by norm_num)) hx
  have hchart := contDiffAt_extChartAt_comp_surface hf hx
  have hDf : DifferentiableAt 𝕜 (fderiv 𝕜
      (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2))) (u, v) :=
    (ContDiffAt.hasFDerivAt_fderiv hchart le_rfl).differentiableAt
  have hpartial : DifferentiableAt 𝕜
      (fun r ↦ fderiv 𝕜 (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2))
        (u, r) ((1 : 𝕜), 0)) v := by
    fun_prop
  have heq : (fun r ↦ deriv (fun q ↦ extChartAt I x (f q r)) u) =ᶠ[nhds v]
      fun r ↦ fderiv 𝕜 (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2))
        (u, r) ((1 : 𝕜), 0) := by
    simpa only [timeFDeriv_eq] using
      deriv_parameterCurve_eventuallyEq_timeFDeriv (hchart.of_le (by norm_num))
  exact (hpartial.congr_of_eventuallyEq heq).congr_of_eventuallyEq hcoord

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I] in
/-- The coordinate reading of the second-parameter velocity field of a `C²` parametrized surface
is differentiable along the first-parameter curve. -/
theorem differentiableAt_sectionCoord_curveVelocity_snd [IsManifold I 2 M]
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 2 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord (F := E) (fun q ↦ f q v)
      (fun q ↦ curveVelocity I (f q) v) x) u :=
  differentiableAt_sectionCoord_curveVelocity_fst (f := fun a b ↦ f b a)
    (u := v) (v := u) (x := x)
    (hf.comp (v, u) (contMDiff_iff_contDiff.mpr
      (by fun_prop : ContDiff 𝕜 2 fun z : 𝕜 × 𝕜 ↦ (z.2, z.1))).contMDiffAt) hx

end TauCeti.Manifold
