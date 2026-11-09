/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# The polar Jacobian of the Riemannian exponential map

For a unit radial direction `v` and an angular vector `w` at `p`, the polar Jacobian
`polarJacobian p v w r = ‖d(exp_p)_(r v)(r w)‖` is the length of the angular Jacobi field
supplied by the differential of the exponential map. In geodesic polar coordinates
`F(r, θ) = exp_p(r e(θ))` on a surface, with `e(θ)` the unit circle in angular arclength and
`w = e′(θ)`, it is the coefficient `j` of `F*g = dr² + j² dθ²`.

## Main results

* `TauCeti.Manifold.inner_mfderiv_riemannianExp_polar`: the polar form of the pulled-back metric,
  from the Gauss lemma.
* `TauCeti.Manifold.IsNormalDomain.polarJacobian_pos`: positivity away from the centre inside a
  normal domain.
* `TauCeti.Manifold.hasDerivWithinAt_polarJacobian_zero`: `j(0) = 0` and `j_r(0) = ‖w‖`, as a
  right derivative.
* `TauCeti.Manifold.IsNormalDomain.contDiffOn_polarJacobian` and
  `TauCeti.Manifold.tendsto_deriv_polarJacobian_zero`: smoothness away from the centre, and the
  right limit of the radial derivative at the centre.

All domains of the exponential map remain explicit; no curvature hypothesis is made.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 6 and 10.
* M. P. do Carmo, *Differential Geometry of Curves and Surfaces*, §4-6.
-/

public noncomputable section

open Bundle Filter Function Manifold Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The polar Jacobian `‖d(exp_p)_(r v)(r w)‖` of the exponential map at `p`, for a radial
direction `v` and an angular vector `w`. In geodesic polar coordinates with angular arclength it is
the coefficient `j` of `F*g = dr² + j² dθ²`. -/
def polarJacobian (p : M) (v w : TangentSpace I p) (r : ℝ) : ℝ :=
  ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w)‖

omit [I.Boundaryless] [T2Space M] in
/-- The polar Jacobian is the norm of the angular exponential differential. -/
theorem polarJacobian_eq_norm (p : M) (v w : TangentSpace I p) (r : ℝ) :
    polarJacobian (I := I) p v w r =
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) (r • w)‖ := by rfl

variable {p : M} {v w : TangentSpace I p} {r : ℝ}

omit [I.Boundaryless] [T2Space M] in
/-- The polar Jacobian vanishes at the centre. -/
@[simp] theorem polarJacobian_zero (p : M) (v w : TangentSpace I p) :
    polarJacobian (I := I) p v w 0 = 0 := by
  unfold polarJacobian
  rw [zero_smul, zero_smul]
  exact (congrArg norm (map_zero _)).trans (norm_zero)

omit [I.Boundaryless] [T2Space M] in
/-- The polar Jacobian is nonnegative, including at conjugate vectors. -/
@[simp] theorem polarJacobian_nonneg (p : M) (v w : TangentSpace I p) (r : ℝ) :
    0 ≤ polarJacobian (I := I) p v w r := norm_nonneg _

omit [I.Boundaryless] [T2Space M] in
/-- Factoring out the radial parameter exposes the regular coefficient at the centre. -/
theorem polarJacobian_eq_abs_mul (p : M) (v w : TangentSpace I p) (r : ℝ) :
    polarJacobian (I := I) p v w r =
      |r| * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖ := by
  -- `L` is the differential with domain written as `T_p M` rather than as the tangent space of
  -- `T_p M` at `r • v`; only in this form do the linear-map rewrites match syntactically.
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p (r • v)) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v)
  have hL : ‖L (r • w)‖ = |r| * ‖L w‖ := by rw [L.map_smul, norm_smul, Real.norm_eq_abs]
  rw [polarJacobian_eq_norm]
  exact hL

omit [I.Boundaryless] [T2Space M] in
/-- Positivity of the polar Jacobian before leaving a normal domain. -/
theorem IsNormalDomain.polarJacobian_pos {U : Set (TangentSpace I p)}
    (h : IsNormalDomain I M p U) (hr : r ≠ 0) (hw : w ≠ 0) (hmem : r • v ∈ U) :
    0 < polarJacobian (I := I) p v w r := by
  apply norm_pos_iff.mpr
  intro hz
  have heq : r • w = (0 : TangentSpace I p) :=
    h.injective_mfderiv_riemannianExp hmem (hz.trans (map_zero _).symm)
  exact (smul_ne_zero hr hw) heq

/-- The full polar metric, evaluated on two coordinate tangent vectors.
The angular coefficient is the polar Jacobian. -/
theorem inner_mfderiv_riemannianExp_polar
    (hmem : r • v ∈ expDomain I M p)
    (hv : ‖v‖ = 1) (hvw : ⟪v, w⟫_ℝ = 0) (a b c d : ℝ) :
    ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v)
        (a • v + b • (r • w)),
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v)
        (c • v + d • (r • w))⟫_ℝ =
      a * c + polarJacobian (I := I) p v w r ^ 2 * b * d := by
  -- `L` is the differential with domain written as `T_p M`, as in `polarJacobian_eq_abs_mul`.
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p (r • v)) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v)
  have hrad : ⟪L v, L v⟫_ℝ = 1 :=
    inner_mfderiv_riemannianExp_unit_radial hmem hv
  have hcross : ⟪L v, L (r • w)⟫_ℝ = 0 :=
    inner_mfderiv_riemannianExp_radial_angular hmem hvw
  have hcross' : ⟪L (r • w), L v⟫_ℝ = 0 := by rw [real_inner_comm, hcross]
  have hang : ⟪L (r • w), L (r • w)⟫_ℝ = polarJacobian (I := I) p v w r ^ 2 :=
    (real_inner_self_eq_norm_sq _).trans (congrArg (· ^ 2) (polarJacobian_eq_norm p v w r).symm)
  have hL : ⟪L (a • v + b • (r • w)), L (c • v + d • (r • w))⟫_ℝ =
      a * c + polarJacobian (I := I) p v w r ^ 2 * b * d := by
    rw [L.map_add, L.map_add, L.map_smul a v, L.map_smul b (r • w),
      L.map_smul c v, L.map_smul d (r • w)]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hrad, hcross, hcross', hang, mul_zero, add_zero, zero_add, mul_one]
    ring
  exact hL

/-- The first-order one-sided initial limit of the polar Jacobian. For an angular
arclength vector `w`, its value is one. -/
theorem tendsto_polarJacobian_div (p : M) (v w : TangentSpace I p) :
    Tendsto (fun r : ℝ ↦ polarJacobian (I := I) p v w r / r) (𝓝[>] 0) (𝓝 ‖w‖) := by
  have h := (continuousAt_norm_angular_riemannianExp_zero (I := I) p v w).tendsto
  rw [zero_smul, mfderiv_riemannianExp_apply_zero, riemannianExp_zero] at h
  apply (h.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [polarJacobian_eq_abs_mul, abs_of_pos hr, mul_div_cancel_left₀ _ hr.ne']

/-- The polar Jacobian has the right derivative prescribed by its angular initial vector.
In angular arclength parametrization this is `j_r(0) = 1`. -/
theorem hasDerivWithinAt_polarJacobian_zero (p : M) (v w : TangentSpace I p) :
    HasDerivWithinAt (polarJacobian (I := I) p v w) ‖w‖ (Ici 0) 0 := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Set.Ici_sdiff_left]
  apply (tendsto_polarJacobian_div (I := I) p v w).congr'
  exact Eventually.of_forall fun r ↦ by rw [slope_def_field, polarJacobian_zero, sub_zero,
    sub_zero]

/-- Smoothness of the polar Jacobian away from the centre in a normal domain. -/
theorem IsNormalDomain.contDiffOn_polarJacobian
    {U : Set (TangentSpace I p)} (h : IsNormalDomain I M p U) :
    ContDiffOn ℝ ∞ (polarJacobian (I := I) p v w) {r : ℝ | 0 < r ∧ r • v ∈ U} := by
  have hq : ContDiffOn ℝ ∞ (fun r : ℝ ↦
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖)
      {r : ℝ | 0 < r ∧ r • v ∈ U} :=
    (h.contDiffOn_norm_angular_riemannianExp (w := w)).comp
      (contDiff_id.smul contDiff_const).contDiffOn (fun _ hr ↦ hr.2)
  refine (contDiffOn_id.mul hq).congr ?_
  intro r hr
  exact (polarJacobian_eq_abs_mul p v w r).trans (by rw [abs_of_pos hr.1]; rfl)

/-- The radial derivative of the polar Jacobian tends to the angular initial speed from
the right, even though the polar Jacobian need not be differentiable at the centre. -/
theorem tendsto_deriv_polarJacobian_zero (p : M) (v w : TangentSpace I p) :
    Tendsto (deriv (polarJacobian (I := I) p v w)) (𝓝[>] 0) (𝓝 ‖w‖) := by
  obtain ⟨R, -, h⟩ := exists_isNormalDomain_ball (I := I) p
  have h0 : (0 : ℝ) • v ∈ Metric.ball (0 : TangentSpace I p) R := by
    rw [zero_smul]
    exact h.zero_mem
  have hq : ContDiffAt ℝ ∞ (fun r : ℝ ↦
      ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖) 0 :=
    ((h.contDiffOn_norm_angular_riemannianExp (w := w)).contDiffAt
      (h.isOpen.mem_nhds h0)).comp (f := fun r : ℝ ↦ r • v) 0
      (contDiff_id.smul contDiff_const).contDiffAt
  have hprod : ContDiffAt ℝ ∞ (fun r : ℝ ↦
      r * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖) 0 :=
    contDiffAt_id.mul hq
  have hd : HasDerivAt (fun r : ℝ ↦
      r * ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (r • v) w‖) _ 0 :=
    (hasDerivAt_id' 0).mul (hq.differentiableAt (by simp)).hasDerivAt
  have hlim := (hprod.derivWithin (m := 0) (by simp)).continuousAt.tendsto
  rw [hd.deriv, one_mul, zero_mul, add_zero, zero_smul, mfderiv_riemannianExp_apply_zero,
    riemannianExp_zero] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hr] with t ht
  rw [polarJacobian_eq_abs_mul, abs_of_pos ht]

end TauCeti.Manifold
