/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.FixedPoint
public import Mathlib.Geometry.Manifold.VectorField.Pullback
import TauCeti.Analysis.Calculus.Deriv.FixedVector
import TauCeti.Analysis.Calculus.FDeriv.MixedPartial
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The flow near a rest point

Let `v` be a vector field on a boundaryless manifold and `p` a rest point, `v p = 0`. The
trajectory through `p` is constant, so `p` lies in the flow domain at every time and every time-`t`
map of the flow fixes it (`TauCeti.flowOf_eq_self_of_eq_zero`). The differentials
`dφ_t(p) : T_p M → T_p M` of these maps form a one-parameter family of operators on the single
tangent space `T_p M`.

Read `v` in the preferred chart at `p`, as the inverse-chart pullback
`V = VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm v (range I)`. Its derivative
`L = DV` at the chart image of `p` is the linearization of `v` at the rest point. For a `C²` field
the family `dφ_t(p)` has derivative `L` at `t = 0`
(`TauCeti.hasDerivAt_mfderiv_flowOf_of_eq_zero`), so `dφ_t(p) = 1 + t L + o(t)`. The flow is
jointly `C²`, so in the chart it is a `C²` function `Ψ(t, z)` of time and position whose time
derivative at `t = 0` is `V`; the symmetry of its second derivative exchanges the time derivative
of the spatial derivative `D_z Ψ (t, ·)` with the spatial derivative `DV` of the time derivative.

Consequently, if `L` is injective, then for `t ≠ 0` close to `0` the rest point is a
nondegenerate fixed point of the time-`t` map (`TauCeti.eventually_isNondegenerateFixedPt_flowOf`):
`1` is not an eigenvalue of `dφ_t(p)`. For the Hamiltonian vector field of a Morse function this
makes the critical points nondegenerate constant orbits of `ε F` for small `ε > 0`.

## Main results

* `TauCeti.mem_flowDomain_of_eq_zero`, `TauCeti.flowOf_eq_self_of_eq_zero`: the flow is defined at
  a rest point for all time and fixes it.
* `TauCeti.hasDerivAt_mfderiv_flowOf_of_eq_zero`: the differentials of the time-`t` maps at a rest
  point have derivative the linearization of the field at `t = 0`.
* `TauCeti.eventually_isNondegenerateFixedPt_flowOf`: a rest point with injective linearization is
  a nondegenerate fixed point of the time-`t` maps for small `t ≠ 0`.

## References

* M. W. Hirsch, S. Smale, R. L. Devaney, *Differential Equations, Dynamical Systems, and an
  Introduction to Chaos*, 3rd ed., Academic Press, 2013, Chapter 8 (linearization at
  equilibria).
-/

public section

open Filter Function Set
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {v : (x : M) → TangentSpace I x} {p : M}

/-- **The flow is defined at a rest point for all time.** -/
theorem mem_flowDomain_of_eq_zero (hp : v p = 0) (t : ℝ) : (t, p) ∈ flowDomain v := by
  have habs := abs_nonneg t
  rw [mem_flowDomain]
  exact ((isMIntegralCurve_const hp).isMIntegralCurveOn (Ioo (-(|t| + 1)) (|t| + 1))
    |>.subset_maximalIntegralCurveInterval ⟨by linarith, by linarith⟩ rfl)
    ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩

variable [T2Space M] [IsManifold I 1 M]

/-- **The flow fixes a rest point.** Every time-`t` map of the flow of a `C¹` field fixes a point
at which the field vanishes. -/
theorem flowOf_eq_self_of_eq_zero [BoundarylessManifold I M]
    (hv : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0) (t : ℝ) :
    flowOf v t p = p :=
  flowOf_eq_of_isMIntegralCurve hv (isMIntegralCurve_const hp) t

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I 2 M]

/-- In the preferred chart at a rest point, the flow of a `C²` field is a jointly `C²` function of
position and time. -/
private theorem contDiffAt_extChartAt_flowOf
    (hv : CMDiff 2 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0) :
    ContDiffAt ℝ 2 (fun q : E × ℝ ↦ extChartAt I p (flowOf v q.2 ((extChartAt I p).symm q.1)))
      (extChartAt I p p, 0) := by
  have hG : ContMDiffAt (𝓘(ℝ).prod I) I 2 (fun q : ℝ × M ↦ flowOf v q.1 q.2) (0, p) :=
    (contMDiffOn_flowOf (n := 2) one_le_two hv).contMDiffAt
      ((isOpen_flowDomain (hv.of_le one_le_two)).mem_nhds (mem_flowDomain_of_eq_zero hp 0))
  have h := hG.contDiffAt_writtenInExtChartAt
  simp only [writtenInExtChartAt, extChartAt_prod,
    flowOf_eq_self_of_eq_zero (hv.of_le one_le_two) hp, extChartAt_model_space_eq_id,
    PartialEquiv.prod_symm, PartialEquiv.prod_coe, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    Function.comp_def, id] at h
  -- Exchange the order of the two variables.
  exact h.comp (extChartAt I p p, 0) (f := fun q : E × ℝ ↦ (q.2, q.1))
    (contDiff_snd.prodMk contDiff_fst).contDiffAt

/-- **Linearization of the flow at a rest point.** For a `C²` vector field `v` vanishing at `p`, the
differentials `dφ_t(p) : T_p M → T_p M` of the time-`t` maps of the flow have derivative at
`t = 0` the derivative `L` of the coordinate expression of `v` in the preferred chart at `p`, so
`dφ_t(p) = 1 + t L + o(t)`. -/
theorem hasDerivAt_mfderiv_flowOf_of_eq_zero
    (hv : CMDiff 2 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0) :
    HasDerivAt (fun t ↦ (mfderiv I I (flowOf v t) p : E →L[ℝ] E))
      (fderiv ℝ (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm v (range I))
        (extChartAt I p p)) 0 := by
  have hv1 : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) := hv.of_le one_le_two
  -- In the chart, the trajectories start with the coordinate velocity of `v`.
  have hV := eventually_hasDerivAt_extChartAt_family (ψ := fun u x ↦ flowOf v u x) (V := v)
    (t := 0) (y := p) (Eventually.of_forall fun x ↦ flowOf_zero v x)
    (Eventually.of_forall fun x ↦
      ((isMIntegralCurveOn_flowOf hv1 x).isMIntegralCurveAt
        (((isOpen_flowDomain hv1).preimage (continuous_id.prodMk continuous_const)).mem_nhds
          (mem_flowDomain_zero hv1 x))).hasMFDerivAt)
  refine (hasDerivAt_spatialDeriv_of_contDiffAt (contDiffAt_extChartAt_flowOf hv hp) hV)
    |>.congr_of_eventuallyEq (Eventually.of_forall fun t ↦ ?_)
  -- Each time-`t` map fixes `p`, so its differential is read in the single chart at `p`.
  have hd : MDifferentiableAt I I (flowOf v t) p :=
    (contMDiffAt_flowOf_comp le_rfl hv1 contMDiffAt_const contMDiffAt_id
      (mem_flowDomain_of_eq_zero hp t)).mdifferentiableAt one_ne_zero
  exact hd.mfderiv_eq_fderiv_extChartAt_conj (flowOf_eq_self_of_eq_zero hv1 hp t)

/-- **A rest point with injective linearization is a nondegenerate fixed point of the short-time
maps.** Let `v` be a `C²` vector field vanishing at `p` whose coordinate expression in the
preferred chart at `p` has injective derivative at the chart image of `p`. Then for every `t ≠ 0`
close to `0`, the point `p` is a nondegenerate fixed point of the time-`t` map of the flow. -/
theorem eventually_isNondegenerateFixedPt_flowOf
    (hv : CMDiff 2 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M))) (hp : v p = 0)
    (hL : Injective (fderiv ℝ
      (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I p).symm v (range I))
        (extChartAt I p p))) :
    ∀ᶠ t in 𝓝[≠] 0, IsNondegenerateFixedPt I (flowOf v t) p := by
  have hv1 : CMDiff 1 (fun y ↦ (⟨y, v y⟩ : TangentBundle I M)) := hv.of_le one_le_two
  have h0 : (mfderiv I I (flowOf v 0) p : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    rw [show flowOf v 0 = id from funext (flowOf_zero v), mfderiv_id]
    rfl
  filter_upwards [(hasDerivAt_mfderiv_flowOf_of_eq_zero hv hp).eventually_eq_zero_of_apply_eq_self
    (E := E) (A := fun t ↦ (mfderiv I I (flowOf v t) p : E →L[ℝ] E)) h0 hL] with t ht
  exact isNondegenerateFixedPt_iff.2 ⟨flowOf_eq_self_of_eq_zero hv1 hp t,
    (contMDiffAt_flowOf_comp le_rfl hv1 contMDiffAt_const contMDiffAt_id
      (mem_flowDomain_of_eq_zero hp t)).mdifferentiableAt one_ne_zero, ht⟩

end TauCeti
