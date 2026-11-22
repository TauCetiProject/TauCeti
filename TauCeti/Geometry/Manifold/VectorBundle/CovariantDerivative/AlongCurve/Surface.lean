/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ParametricFDeriv
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Acceleration
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Pullback
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.Frame
import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

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
* `ContMDiffAt.differentiableAt_sectionCoord_curveVelocity_fst` and
  `ContMDiffAt.differentiableAt_sectionCoord_curveVelocity_snd`: the corresponding
  coordinate readings are differentiable when the surface is `C²`.
* `CovariantDerivative.alongCurve_curveVelocity_comm`: **the symmetry lemma**, that for a
  torsion-free connection the two mixed covariant derivatives of a `C²` parametrized surface
  agree.
* `CovariantDerivative.sectionCoord_alongCurve_snd_eventuallyEq` and
  `CovariantDerivative.sectionCoord_alongCurve_fst_eventuallyEq`: local chart formulas for the
  along-curve covariant derivatives of a `C¹` field along a parametrized surface along each
  parameter slice.
* `CovariantDerivative.contMDiffAt_alongCurve_fst_slice` and
  `CovariantDerivative.contMDiffAt_alongCurve_snd_slice`: a `C^(m + 1)` field on a parametrized
  surface has `C^m` sliced covariant derivatives along each parameter curve for a locally `C^m`
  connection.
* `ContMDiffAt.contMDiffAt_acceleration_fst_slice`: regularity of the sliced transverse
  acceleration `r ↦ D_q ∂_q f (u, r)` for a jointly `C^n` parametrized surface (`m + 2 ≤ n`).

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
    sectionCoord 𝕜 (F := E) (f u) (fun r ↦ curveVelocity I (fun q ↦ f q r) u) x =ᶠ[𝓝 v]
      fun r ↦ deriv (fun q ↦ extChartAt I x (f q r)) u := by
  obtain ⟨w, hw, hfw⟩ := (contMDiffAt_iff_contMDiffOn_nhds (by simp)).mp hf
  obtain ⟨w', hw'w, hw'open, hw'mem⟩ := mem_nhds_iff.mp hw
  have hslice : Continuous fun r : 𝕜 ↦ ((u, r) : 𝕜 × 𝕜) := by fun_prop
  filter_upwards [hslice.continuousAt.preimage_mem_nhds (hw'open.mem_nhds hw'mem),
    (hf.continuousAt.comp hslice.continuousAt).preimage_mem_nhds
      ((trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds hx)] with r hr hrbase
  have hdiff : MDifferentiableAt 𝓘(𝕜, 𝕜) I (fun q ↦ f q r) u :=
    (((hfw.mono hw'w).contMDiffAt (hw'open.mem_nhds hr)).comp u
      (contMDiff_iff_contDiff.mpr (contDiff_prodMk_left (n := 1) r)).contMDiffAt).mdifferentiableAt
      one_ne_zero
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
    ContDiffAt 𝕜 n (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2)) (u, v) :=
  contMDiffAt_iff_contDiffAt.mp ((contMDiffAt_extChartAt' (I := I) (n := n)
    (by rwa [TangentBundle.trivializationAt_baseSet] at hx)).comp (u, v) hf)

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
  have : CompleteSpace E := FiniteDimensional.completeSpace 𝕜 E
  have hone : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 1 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v) :=
    hf.of_le (le_trans (by norm_num) le_minSmoothness)
  have hbase : f u v ∈ (trivializationAt E (TangentSpace I) (f u v)).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (f u v)
  rw [alongCurve_apply, alongCurve_apply,
    alongCurveInChartWithin_curveVelocity_fst cov hone hbase,
    alongCurveInChartWithin_curveVelocity_snd cov hone hbase,
    deriv_deriv_comm (contDiffAt_extChartAt_comp_surface hf hbase),
    christoffelMap_comm hcov (finBasis 𝕜 E) (f u v) (mem_extChartAt_source (f u v))]

end CovariantDerivative

namespace CovariantDerivative

open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  {f : 𝕜 → 𝕜 → M} {W : ∀ q r, TangentSpace I (f q r)} {u v : 𝕜}

/-- **Chart formula for the second-parameter covariant derivative along a surface.** Near `u`, the
covariant derivative along the second-parameter curve `f q` of a `C¹` field `W` on a parametrized
surface `f`, read in the trivialization at `f u v`, is given by the coordinate formula. -/
theorem sectionCoord_alongCurve_snd_eventuallyEq
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    (hW : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent 1
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    letI e := trivializationAt E (TangentSpace I) (f u v)
    letI Γ := christoffelMap (finBasis 𝕜 E) (cov.isCovariantDerivativeOn (s := e.baseSet))
    sectionCoord 𝕜 (F := E) (fun q ↦ f q v) (fun q ↦ alongCurve cov (f q) (W q) v) (f u v) =ᶠ[𝓝 u]
      fun q ↦
        deriv (fun r ↦ e.continuousLinearMapAt 𝕜 (f q r) (W q r)) v +
          Γ (f q v) (e.continuousLinearMapAt 𝕜 (f q v) (W q v))
            (deriv (fun r ↦ extChartAt I (f u v) (f q r)) v) := by
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 1 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp (u, v) hW
  have hslice : ∀ᶠ q in 𝓝 u, ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent 1
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (q, v) ∧ f q v ∈ e.baseSet :=
    ((continuous_id.prodMk continuous_const).tendsto u).eventually
      (((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hW).and
        (hf.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)))
  filter_upwards [hslice] with q ⟨hq, hqb⟩
  have hcurve : ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (f q r) (W q r)) v :=
    hq.comp v (contMDiff_iff_contDiff.mpr (contDiff_prodMk_right (n := 1) q)).contMDiffAt
  have hfq : MDifferentiableAt 𝓘(𝕜, 𝕜) I (f q) v :=
    ((contMDiff_proj (TangentSpace I)).contMDiffAt.comp v hcurve).mdifferentiableAt one_ne_zero
  have hV : DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := E) (f q) (W q) (f q v)) v :=
    differentiableAt_sectionCoord (f q) (W q) (hcurve.mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _)
  rw [sectionCoord_apply, ← alongCurveWithin_univ,
    ← symmL_alongCurveInChartWithin cov (f q) (W q) hqb hfq.mdifferentiableWithinAt
      hV.differentiableWithinAt,
    e.continuousLinearMapAt_symmL (R := 𝕜) hqb, alongCurveInChartWithin_apply,
    derivWithin_univ, derivWithin_univ, Function.comp_def,
    show sectionCoord 𝕜 (F := E) (f q) (W q) (f u v) =
      fun r ↦ e.continuousLinearMapAt 𝕜 (f q r) (W q r) from
      funext fun r ↦ sectionCoord_apply (f q) (W q) (f u v) r]

/-- **Chart formula for the first-parameter covariant derivative along a surface.** Near `v`, the
covariant derivative along the first-parameter curve `fun q ↦ f q r` of a `C¹` field `W` on a
parametrized surface `f`, read in the trivialization at `f u v`, is given by the coordinate
formula. -/
theorem sectionCoord_alongCurve_fst_eventuallyEq
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    (hW : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent 1
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    letI e := trivializationAt E (TangentSpace I) (f u v)
    letI Γ := christoffelMap (finBasis 𝕜 E) (cov.isCovariantDerivativeOn (s := e.baseSet))
    sectionCoord 𝕜 (F := E) (f u)
        (fun r ↦ alongCurve cov (fun q ↦ f q r) (fun q ↦ W q r) u) (f u v) =ᶠ[𝓝 v]
      fun r ↦
        deriv (fun q ↦ e.continuousLinearMapAt 𝕜 (f q r) (W q r)) u +
          Γ (f u r) (e.continuousLinearMapAt 𝕜 (f u r) (W u r))
            (deriv (fun q ↦ extChartAt I (f u v) (f q r)) u) :=
  sectionCoord_alongCurve_snd_eventuallyEq (f := fun r q ↦ f q r) (W := fun r q ↦ W q r)
    (u := v) (v := u) cov
    (hW.comp (v, u) (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffAt)

/-- **Regularity of the first-parameter covariant derivative along a slice.** If a vector field `W`
along a parametrized surface `f : 𝕜 → 𝕜 → M` has a `C^(m + 1)` lift to the tangent bundle at
`(u, v)` and the connection is `C^m` on the trivialization base set at `f u v`, then its covariant
derivative in the first parameter at `u` has a `C^m` lift along `f u` at `v`. -/
theorem contMDiffAt_alongCurve_fst_slice {m : ℕ∞ω} [IsManifold I (m + 1) M]
    [ContMDiffVectorBundle (m + 1) E (TangentSpace I : M → Type _) I]
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    [ContMDiffCovariantDerivativeOn E m cov.toFun
      (trivializationAt E (TangentSpace I) (f u v)).baseSet]
    (hW : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent (m + 1)
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent m
      (fun r ↦ TotalSpace.mk' E (f u r)
        (alongCurve cov (fun q ↦ f q r) (fun q ↦ W q r) u)) v := by
  set e := trivializationAt E (TangentSpace I) (f u v)
  have hcov := cov.isCovariantDerivativeOn (s := e.baseSet)
  set Γ := christoffelMap (finBasis 𝕜 E) hcov
  have : ContMDiffVectorBundle m E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := m + 1) le_self_add
  have hbase : f u v ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) _
  have hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I (m + 1) (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v) :=
    (contMDiff_proj (TangentSpace I)).contMDiffAt.comp (u, v) hW
  have hfu : ContMDiffAt 𝓘(𝕜, 𝕜) I (m + 1) (f u) v :=
    hf.comp v (contDiff_prodMk_right u).contMDiff.contMDiffAt
  set φ : 𝕜 × 𝕜 → E := fun z ↦ extChartAt I (f u v) (f z.1 z.2)
  set w : 𝕜 × 𝕜 → E := fun z ↦ e.continuousLinearMapAt 𝕜 (f z.1 z.2) (W z.1 z.2)
  have hφ : ContDiffAt 𝕜 (m + 1) φ (u, v) := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (mem_chart_source H (f u v))).comp (u, v) hf)
  have hw : ContDiffAt 𝕜 (m + 1) w (u, v) :=
    hW.contDiffAt_continuousLinearMapAt_trivializationAt
  have hΓv : ContDiffAt 𝕜 m (fun r ↦ Γ (f u r)) v := contMDiffAt_iff_contDiffAt.mp
    (((contMDiffOn_christoffelMap (finBasis 𝕜 E) hcov).contMDiffAt
      (e.open_baseSet.mem_nhds hbase)).comp v (hfu.of_le le_self_add))
  have hcoord : ContDiffAt 𝕜 m
      (fun r ↦ deriv (fun q ↦ w (q, r)) u + Γ (f u r) (w (u, r)) (deriv (fun q ↦ φ (q, r)) u)) v :=
    (TauCeti.contDiffAt_deriv_slice_left hw).add ((hΓv.clm_apply
      ((hw.of_le le_self_add).comp v (contDiff_prodMk_right u).contDiffAt)).clm_apply
      (TauCeti.contDiffAt_deriv_slice_left hφ))
  rw [contMDiffAt_totalSpace_iff]
  refine ⟨hfu.of_le le_self_add, (contMDiffAt_iff_contDiffAt.mpr hcoord).congr_of_eventuallyEq ?_⟩
  filter_upwards [sectionCoord_alongCurve_fst_eventuallyEq cov (hW.of_le le_add_self),
    hfu.continuousAt.preimage_mem_nhds (e.open_baseSet.mem_nhds hbase)] with r hr hrb
  rw [← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) hrb]
  rwa [sectionCoord_apply] at hr

/-- **Regularity of the second-parameter covariant derivative along a slice.** If a vector field
`W` along a parametrized surface `f : 𝕜 → 𝕜 → M` has a `C^(m + 1)` lift to the tangent bundle at
`(u, v)` and the connection is `C^m` on the trivialization base set at `f u v`, then its covariant
derivative in the second parameter at `v` has a `C^m` lift along `fun q ↦ f q v` at `u`. -/
theorem contMDiffAt_alongCurve_snd_slice {m : ℕ∞ω} [IsManifold I (m + 1) M]
    [ContMDiffVectorBundle (m + 1) E (TangentSpace I : M → Type _) I]
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    [ContMDiffCovariantDerivativeOn E m cov.toFun
      (trivializationAt E (TangentSpace I) (f u v)).baseSet]
    (hW : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent (m + 1)
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (W z.1 z.2)) (u, v)) :
    ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent m
      (fun q ↦ TotalSpace.mk' E (f q v) (alongCurve cov (f q) (W q) v)) u :=
  contMDiffAt_alongCurve_fst_slice (f := fun r q ↦ f q r) (W := fun r q ↦ W q r) (u := v) (v := u)
    cov (hW.comp (v, u) (contDiff_snd.prodMk contDiff_fst).contMDiff.contMDiffAt)

end CovariantDerivative

namespace ContMDiffAt

open CovariantDerivative
open TauCeti.Manifold

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {f : 𝕜 → 𝕜 → M} {u v : 𝕜} {x : M}

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The coordinate reading of the first-parameter velocity field of a `C²` parametrized surface is
differentiable along the second-parameter curve. -/
theorem differentiableAt_sectionCoord_curveVelocity_fst [IsManifold I 2 M]
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 2 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    DifferentiableAt 𝕜
      (sectionCoord 𝕜 (F := E) (f u) (fun r ↦ curveVelocity I (fun q ↦ f q r) u) x) v := by
  have hchart := contDiffAt_extChartAt_comp_surface hf hx
  have hDf : DifferentiableAt 𝕜 (fderiv 𝕜
      (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2))) (u, v) :=
    (ContDiffAt.hasFDerivAt_fderiv hchart le_rfl).differentiableAt
  have hpartial : DifferentiableAt 𝕜
      (fun r ↦ fderiv 𝕜 (fun z : 𝕜 × 𝕜 ↦ extChartAt I x (f z.1 z.2))
        (u, r) ((1 : 𝕜), 0)) v := by
    fun_prop
  refine (hpartial.congr_of_eventuallyEq ?_).congr_of_eventuallyEq
    (sectionCoord_curveVelocity_fst_eventuallyEq (hf.of_le (by norm_num)) hx)
  simpa only [timeFDeriv_eq] using
    (hchart.of_le (by norm_num)).deriv_parameterCurve_eventuallyEq_timeFDeriv

omit [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] in
/-- The coordinate reading of the second-parameter velocity field of a `C²` parametrized surface
is differentiable along the first-parameter curve. -/
theorem differentiableAt_sectionCoord_curveVelocity_snd [IsManifold I 2 M]
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I 2 (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hx : f u v ∈ (trivializationAt E (TangentSpace I) x).baseSet) :
    DifferentiableAt 𝕜 (sectionCoord 𝕜 (F := E) (fun q ↦ f q v)
      (fun q ↦ curveVelocity I (f q) v) x) u :=
  (hf.comp (v, u) (contMDiff_iff_contDiff.mpr
    (by fun_prop : ContDiff 𝕜 2 fun z : 𝕜 × 𝕜 ↦ (z.2, z.1))).contMDiffAt)
  |>.differentiableAt_sectionCoord_curveVelocity_fst (f := fun a b ↦ f b a)
    (u := v) (v := u) (x := x)
    hx

/-- **Regularity of the transverse acceleration along a slice.** If a two-parameter family
`f : 𝕜 → 𝕜 → M` is jointly `C^n` at `(u, v)`, `m + 2 ≤ n`, and `cov` is `C^m` on the
trivialization base set at `f u v`, then the covariant accelerations `r ↦ D_q ∂_q f (u, r)` of its
transverse curves form a `C^m` section along `f u` at `v`. -/
theorem contMDiffAt_acceleration_fst_slice [IsManifold I 2 M]
    {m n : ℕ∞ω} [IsManifold I (m + 1) M]
    [ContMDiffVectorBundle (m + 1) E (TangentSpace I : M → Type _) I]
    (cov : _root_.CovariantDerivative I E (fun y : M ↦ TangentSpace I y))
    [ContMDiffCovariantDerivativeOn E m cov.toFun
      (trivializationAt E (TangentSpace I) (f u v)).baseSet]
    (hf : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I n (fun z : 𝕜 × 𝕜 ↦ f z.1 z.2) (u, v))
    (hmn : m + 2 ≤ n) :
    ContMDiffAt 𝓘(𝕜, 𝕜) I.tangent m
      (fun r ↦ TotalSpace.mk' E (f u r) (acceleration cov (fun q ↦ f q r) u)) v := by
  have : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := m + 1) le_add_self
  have hW : ContMDiffAt 𝓘(𝕜, 𝕜 × 𝕜) I.tangent (m + 1)
      (fun z : 𝕜 × 𝕜 ↦ TotalSpace.mk' E (f z.1 z.2) (curveVelocity I (fun q ↦ f q z.2) z.1))
      (u, v) :=
    hf.contMDiffAt_curveVelocity_fst (by rwa [add_assoc, one_add_one_eq_two])
  simpa only [acceleration_def] using contMDiffAt_alongCurve_fst_slice cov hW

end ContMDiffAt
