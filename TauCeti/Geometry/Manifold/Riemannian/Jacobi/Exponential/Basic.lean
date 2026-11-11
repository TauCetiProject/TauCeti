/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Uniqueness
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Variation
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Surface

/-!
# Jacobi fields and the differential of the exponential map

Let `p` be a point of a Riemannian manifold and `v, w ∈ T_p M`. Along the radial geodesic
`γ(t) = exp_p (t v)`, defined on the maximal geodesic interval of `v`, the field

`J(t) = d(exp_p)_{t v} (t w)`

is the Jacobi field with initial data `J(0) = 0` and `D_t J(0) = w`. It is the variation field of
the family of radial geodesics `t ↦ exp_p (t (v + q w))`, so it is a Jacobi field by
`TauCeti.Manifold.isJacobiFieldOn_variationField`. Its initial covariant derivative is computed by
the symmetry lemma `D_t ∂_q = D_q ∂_t`: at `t = 0` the transverse curve is constant at `p` and the
initial velocities `v + q w` form an affine path in `T_p M` with derivative `w`.

By uniqueness of Jacobi fields with given initial data, every Jacobi field `X` along `γ` with
`X(0) = 0` and `D_t X(0) = w` is `X(t) = d(exp_p)_{t v} (t w)`. Thus the differential of the
exponential map is computed by solving the Jacobi equation. This identification is the link
between the kernel of `d(exp_p)` and Jacobi fields vanishing at two parameters, that is, conjugate
points along `γ`, and it is the input for the expansion of the metric in normal coordinates. No
completeness is assumed: everything happens on the natural domain of `exp_p`.

## Main results

* `TauCeti.Manifold.isJacobiFieldOn_mfderiv_riemannianExp`: `t ↦ d(exp_p)_{t v} (t w)` is a
  Jacobi field along `t ↦ exp_p (t v)` on the maximal geodesic interval of `v`.
* `TauCeti.Manifold.alongCurveWithin_mfderiv_riemannianExp_zero`: its covariant derivative at
  `t = 0` is `w`.
* `TauCeti.Manifold.IsJacobiFieldOn.eq_mfderiv_riemannianExp`: a Jacobi field along the radial
  geodesic with initial data `(0, w)` is `t ↦ d(exp_p)_{t v} (t w)`.

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

/-- The radial variation `t ↦ exp_p (t (v + q w))` whose variation field at `q = 0` is
`t ↦ d(exp_p)_{t v} (t w)`. -/
private abbrev radialFamily (p : M) (v w : TangentSpace I p) (q t : ℝ) : M :=
  riemannianExp I M p (t • (v + q • w))

/-- **The differential of the exponential map along a ray is a Jacobi field.** For
`v, w ∈ T_p M`, the field `t ↦ d(exp_p)_{t v} (t w)` is a Jacobi field along the radial geodesic
`t ↦ exp_p (t v)` on the maximal geodesic interval of `v`. -/
theorem isJacobiFieldOn_mfderiv_riemannianExp (p : M) (v w : TangentSpace I p) :
    IsJacobiFieldOn I (fun t : ℝ ↦ riemannianExp I M p (t • v))
      (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w))
      (geodesicInterval I M p v) := by
  have hF : ∀ q t : ℝ, radialFamily (I := I) p v w q t = riemannianExp I M p (t • (v + q • w)) :=
    fun _ _ ↦ rfl
  have hJ := isJacobiFieldOn_variationField isOpen_geodesicInterval
    (fun t ht ↦ (contMDiffAt_radialVariation hF (u := 0)
      (by simpa using mem_geodesicInterval_iff_smul_mem_expDomain.1 ht)).of_le (by norm_cast))
    (fun t ht ↦ eventually_acceleration_radialVariation_eq_zero hF ht)
  rw [radialVariation_zero hF] at hJ
  exact hJ.congr fun t ht ↦ (variationField_radialVariation hF ht).symm

/-- The variation field of the radial family has covariant derivative `w` at `t = 0`. -/
private theorem alongCurve_variationField_radialFamily_zero (p : M) (v w : TangentSpace I p) :
    alongCurve (leviCivitaConnection I M) (radialFamily (I := I) p v w 0)
      (variationField I (radialFamily (I := I) p v w)) 0 = w := by
  have : IsManifold I (minSmoothness ℝ 2) M := by
    rw [minSmoothness_of_isRCLikeNormedField]
    infer_instance
  set F := radialFamily (I := I) p v w
  have hF : ∀ q t : ℝ, F q t = riemannianExp I M p (t • (v + q • w)) := fun _ _ ↦ rfl
  -- Exchange the two covariant derivatives with the symmetry lemma.
  rw [variationField_def, alongCurve_curveVelocity_comm (leviCivitaConnection I M)
    ((isTorsionFree_iff_torsion_eq_zero _).2 (torsion_leviCivitaConnection_eq_zero I))
    (f := F) (u := 0) (v := 0) ((contMDiffAt_radialVariation hF (by simp)).of_le (by simp))]
  -- At `t = 0` the transverse curve is constant at `p`, with initial velocities `v + q w`.
  -- The fibres `TangentSpace I (F q 0)` and `TangentSpace I p` are both `E`, so the velocities
  -- are read in `TangentSpace I p`.
  have hvel (q : ℝ) : (curveVelocity I (F q) 0 : TangentSpace I p) = v + q • w :=
    curveVelocity_riemannianExp_smul_zero p (v + q • w)
  rw [funext (radialVariation_apply_zero hF)]
  exact (alongCurve_congr _ (fun _ ↦ p) (fun q ↦ curveVelocity I (F q) 0)
    (W := fun q : ℝ ↦ (v + q • w : TangentSpace I p))
    (Eventually.of_forall hvel)).trans (alongCurve_const_of_hasDerivAt _ p
      (by simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v))

/-- **The initial covariant derivative of `t ↦ d(exp_p)_{t v} (t w)` is `w`.** -/
@[simp] theorem alongCurveWithin_mfderiv_riemannianExp_zero (p : M) (v w : TangentSpace I p) :
    alongCurveWithin (leviCivitaConnection I M) (fun t : ℝ ↦ riemannianExp I M p (t • v))
      (fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w))
      (geodesicInterval I M p v) 0 = w := by
  set F := radialFamily (I := I) p v w
  have hF : ∀ q t : ℝ, F q t = riemannianExp I M p (t • (v + q • w)) := fun _ _ ↦ rfl
  have h0 : (0 : ℝ) ∈ geodesicInterval I M p v := zero_mem_geodesicInterval
  -- Near `t = 0` the field is the variation field of the radial family. The differential lives in
  -- `TangentSpace I (exp_p (t • v))` and is read in the fibre `TangentSpace I (F 0 t)`; both
  -- fibres are `E`.
  have hfield : ∀ᶠ t in 𝓝 (0 : ℝ),
      (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w) :
        TangentSpace I (F 0 t)) = variationField I F t := by
    filter_upwards [isOpen_geodesicInterval.mem_nhds h0] with t ht
    exact (variationField_radialVariation hF ht).symm
  -- Rewriting the curve to `F 0` also moves the fibres of the field to those over `F 0`, which
  -- are again `E`.
  rw [alongCurveWithin_of_mem_nhds _ _ _ (isOpen_geodesicInterval.mem_nhds h0),
    ← radialVariation_zero hF]
  exact (alongCurve_congr _ (F 0) _ hfield).trans
    (alongCurve_variationField_radialFamily_zero p v w)

/-- **Jacobi fields along a radial geodesic compute the differential of the exponential map.**
Let `X` be a Jacobi field along `t ↦ exp_p (t v)` on a preconnected parameter set `s` inside the
maximal geodesic interval of `v` and containing `0`. If `X(0) = 0` and `D_t X(0) = w`, then
`X(t) = d(exp_p)_{t v} (t w)` for every `t ∈ s`. -/
theorem IsJacobiFieldOn.eq_mfderiv_riemannianExp {p : M} {v w : TangentSpace I p}
    {X : ∀ t : ℝ, TangentSpace I (riemannianExp I M p (t • v))} {s : Set ℝ}
    (hX : IsJacobiFieldOn I (fun t : ℝ ↦ riemannianExp I M p (t • v)) X s)
    (hs : IsPreconnected s) (hsub : s ⊆ geodesicInterval I M p v) (h0 : (0 : ℝ) ∈ s)
    (hX0 : X 0 = 0)
    (hDX0 : alongCurveWithin (leviCivitaConnection I M) (fun t : ℝ ↦ riemannianExp I M p (t • v))
      X s 0 = w) {t : ℝ} (ht : t ∈ s) :
    X t = mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w) := by
  have hJ := isJacobiFieldOn_mfderiv_riemannianExp p v w
  refine hX.eq_of_eq_of_alongCurveWithin_eq (hJ.mono hX.uniqueDiffOn hsub) hs h0 ?_ ?_ ht
  · simp only [hX0, zero_smul]
    exact (map_zero _).symm
  · rw [hDX0, hJ.alongCurveWithin_subset (hX.uniqueDiffOn 0 h0) hsub h0,
      alongCurveWithin_mfderiv_riemannianExp_zero]

end TauCeti.Manifold
