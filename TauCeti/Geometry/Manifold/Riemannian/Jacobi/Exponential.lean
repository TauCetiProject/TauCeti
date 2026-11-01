/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Variation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# Jacobi fields and the differential of the exponential map

Let `γ(t) = exp_p (t • v)` be the radial geodesic from `p` with initial velocity `v`, on its
maximal interval. For every `w ∈ T_p M` the field

`J(t) = d(exp_p)_{t v}(t w)`

is the Jacobi field along `γ` with `J(0) = 0` and `D_t J(0) = w`. It is the variation field of the
radial variation `(q, t) ↦ exp_p (t • (v + q • w))` through geodesics, so it solves the Jacobi
equation. At `t = 0` its initial covariant derivative is the transverse derivative of the initial
velocities `v + q • w`, since the two mixed covariant derivatives of a smooth variation agree and
the transverse curve `q ↦ exp_p 0 = p` is constant.

By uniqueness of Jacobi fields, every Jacobi field along `γ` vanishing at `0` with initial
covariant derivative `w` is this field, so the differential of the exponential map is computed by
solving the Jacobi equation. This is the standard route from curvature to the geometry of the
exponential map: conjugate points, normal-coordinate expansions and comparison theorems.

## Main results

* `TauCeti.Manifold.isJacobiFieldOn_mfderiv_riemannianExp_smul`: the field
  `t ↦ d(exp_p)_{t v}(t w)` is a Jacobi field along `t ↦ exp_p (t • v)` on the maximal interval.
* `TauCeti.Manifold.alongCurveWithin_mfderiv_riemannianExp_smul_zero`: its initial covariant
  derivative is `w`.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_mfderiv_riemannianExp_smul`: a Jacobi field along the radial
  geodesic with initial data `(0, w)` is `t ↦ d(exp_p)_{t v}(t w)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Proposition 10.10.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 5, Corollary 2.5.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The differential of the exponential map is a Jacobi field.** For `v w ∈ T_p M`, the field
`t ↦ d(exp_p)_{t v}(t w)` is a Jacobi field along the radial geodesic `t ↦ exp_p (t • v)` on its
maximal interval. -/
theorem isJacobiFieldOn_mfderiv_riemannianExp_smul (p : M) (v w : TangentSpace I p) :
    IsJacobiFieldOn I (fun t ↦ riemannianExp I M p (t • v))
      (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w))
      (geodesicInterval I M p v) := by
  let F : ℝ → ℝ → M := fun q t ↦ riemannianExp I M p (t • (v + q • w))
  have hF : ∀ q t : ℝ, F q t = riemannianExp I M p (t • (v + q • w)) := fun _ _ ↦ rfl
  have h := isJacobiFieldOn_variationField (F := F) isOpen_geodesicInterval
    (fun t ht ↦ (contMDiffAt_riemannianExp_smul_add_smul hF (u := 0)
      (by simpa using mem_geodesicInterval_iff_smul_mem_expDomain.mp ht)).of_le (by norm_num))
    (fun t ht ↦ (eventually_mem_geodesicInterval_add_smul ht).mono fun q hq ↦
      acceleration_riemannianExp_smul_add_smul_eq_zero hF hq)
  have hF0 : F 0 = fun t ↦ riemannianExp I M p (t • v) := funext fun t ↦ by simp [F]
  rw [hF0] at h
  exact h.congr fun t ht ↦ (variationField_riemannianExp_smul_add_smul hF ht).symm

/-- **The initial covariant derivative of the differential of the exponential map.** The Jacobi
field `t ↦ d(exp_p)_{t v}(t w)` along `t ↦ exp_p (t • v)` has covariant derivative `w` at
`t = 0`. -/
theorem alongCurveWithin_mfderiv_riemannianExp_smul_zero (p : M) (v w : TangentSpace I p) :
    alongCurveWithin (leviCivitaConnection I M) (fun t ↦ riemannianExp I M p (t • v))
      (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w))
      (geodesicInterval I M p v) 0 = w := by
  let _ : IsManifold I (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) (by simp)
  set cov := leviCivitaConnection I M
  let F : ℝ → ℝ → M := fun q t ↦ riemannianExp I M p (t • (v + q • w))
  have hF : ∀ q t : ℝ, F q t = riemannianExp I M p (t • (v + q • w)) := fun _ _ ↦ rfl
  have hF0 : F 0 = fun t ↦ riemannianExp I M p (t • v) := funext fun t ↦ by simp [F]
  have hnhds : geodesicInterval I M p v ∈ 𝓝 0 :=
    isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval
  -- On the open maximal interval, the field is the variation field of the radial variation.
  rw [alongCurveWithin_of_mem_nhds _ _ _ hnhds, ← hF0,
    alongCurve_congr cov (F 0) _ (W := variationField I F) (Filter.mem_of_superset hnhds
      fun t ht ↦ (variationField_riemannianExp_smul_add_smul hF ht).symm)]
  -- The two mixed covariant derivatives of the variation agree at `(0, 0)`, and the transverse
  -- curve `q ↦ exp_p 0` is constant with initial radial velocities `v + q • w`.
  have hcomm := alongCurve_curveVelocity_comm cov
    ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
    (f := F) (u := 0) (v := 0) ((contMDiffAt_riemannianExp_smul_add_smul hF (u := 0) (t := 0)
      (by simp)).of_le (by simp))
  have hbase : (fun q ↦ F q 0) = fun _ ↦ p := funext fun q ↦ by simp [F]
  have hvel (q : ℝ) : curveVelocity I (F q) 0 = v + q • w := by
    have hFq : F q = fun t ↦ riemannianExp I M p (t • (v + q • w)) := funext (hF q)
    rw [hFq, curveVelocity_riemannianExp_smul (by simp), zero_smul,
      mfderiv_riemannianExp_apply_zero]
  -- Along the constant curve the covariant derivative is the ordinary derivative in `E`.
  have hd (a b : E) : HasDerivAt (fun q : ℝ ↦ a + q • b) b 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a
  rw [variationField_def, hcomm, hbase, alongCurve_congr cov _ _ (W := fun q ↦ v + q • w)
    (Filter.Eventually.of_forall hvel)]
  exact (alongCurve_const cov p _ 0).trans (hd v w).deriv

/-- **Jacobi fields vanishing at the origin are differentials of the exponential map.** A Jacobi
field `J` along the radial geodesic `t ↦ exp_p (t • v)`, on a preconnected parameter set inside the
maximal interval containing `0`, with `J(0) = 0` and `D_t J(0) = w`, is
`J(t) = d(exp_p)_{t v}(t w)`. -/
theorem IsJacobiFieldOn.eq_mfderiv_riemannianExp_smul {p : M} {v w : TangentSpace I p}
    {J : ∀ t : ℝ, TangentSpace I (riemannianExp I M p (t • v))} {s : Set ℝ} {t : ℝ}
    (hJ : IsJacobiFieldOn I (fun t ↦ riemannianExp I M p (t • v)) J s) (hs : IsPreconnected s)
    (hsub : s ⊆ geodesicInterval I M p v) (h0 : 0 ∈ s) (hJ0 : J 0 = 0)
    (hDJ0 : alongCurveWithin (leviCivitaConnection I M) (fun t ↦ riemannianExp I M p (t • v))
      J s 0 = w) (ht : t ∈ s) :
    J t = mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w) := by
  have hinter : s ∩ geodesicInterval I M p v = s := inter_eq_left.2 hsub
  exact hJ.eq_of_eq_of_alongCurveWithin_eq_inter (isJacobiFieldOn_mfderiv_riemannianExp_smul p v w)
    (by rw [hinter]; exact hs) (by rw [hinter]; exact hJ.uniqueDiffOn) ⟨h0, hsub h0⟩
    (by rw [hJ0, zero_smul ℝ w]; exact (map_zero _).symm)
    (by rw [hDJ0, alongCurveWithin_mfderiv_riemannianExp_smul_zero]) ⟨ht, hsub ht⟩

end TauCeti.Manifold
