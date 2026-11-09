/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Model
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Gauss.Basic

/-!
# The exponential metric in constant curvature

If the radial segment from `p` to `exp_p v` has constant sectional curvature `κ`, the
exponential differential multiplies lengths perpendicular to `v` by
`|curvatureSine (κ * ‖v‖²) 1|`. Together with the Gauss lemma this computes its full
pullback metric: radial lengths are unchanged, radial and angular vectors stay orthogonal,
and angular inner products are multiplied by the square of this coefficient.

These identities are valid on the natural exponential domain, even at conjugate vectors.
They do not require completeness or injectivity of the exponential map. The curvature
hypothesis is imposed only along the radial segment. The coefficient includes all signs of
curvature and zero initial velocity.

The resulting pullback metric `exp_p^* g` at `v` is the constant-curvature model metric
for the equality case of Rauch comparison.

## References

* Formal ingredients: the radial Jacobi field in `Jacobi.Exponential.Basic` and its
  constant-curvature length formula in `Jacobi.Model`.
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 10--11
  (Jacobi fields and the metric in geodesic polar coordinates).
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {v : TangentSpace I p} {κ : ℝ}

/-- In constant curvature along a radial segment, the exponential differential scales every
normal vector by the absolute value of the model sine coefficient. The formula remains valid
when that coefficient vanishes. -/
theorem norm_mfderiv_riemannianExp_of_inner_eq_zero_of_hasSectionalCurvatureAt
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ)
    (w : TangentSpace I p) (hw : ⟪w, v⟫_ℝ = 0) :
    ‖mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w‖ =
      |curvatureSine (κ * ‖v‖ ^ 2) 1| * ‖w‖ := by
  have hsub : Icc (0 : ℝ) 1 ⊆ geodesicInterval I M p v :=
    ordConnected_geodesicInterval.out zero_mem_geodesicInterval (mem_expDomain_iff.1 hv)
  have hradial := isJacobiFieldOn_mfderiv_riemannianExp p v w
  have hJ := hradial.mono (uniqueDiffOn_Icc zero_lt_one) hsub
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have hD := hradial.alongCurveWithin_subset
    (uniqueDiffOn_Icc zero_lt_one 0 h0) hsub h0
  rw [alongCurveWithin_mfderiv_riemannianExp_zero] at hD
  have hvel : curveVelocityWithin I
      (fun t : ℝ ↦ riemannianExp I M p (t • v)) (Icc (0 : ℝ) 1) 0 = v := by
    rw [curveVelocityWithin_subset hsub (uniqueDiffOn_Icc zero_lt_one 0 h0)
        (hradial.isGeodesicCurveOn.mdifferentiableOn 0 zero_mem_geodesicInterval),
      curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds
        zero_mem_geodesicInterval), curveVelocity_riemannianExp_smul_zero]
  have hnorm := hJ.norm_eq_abs_curvatureSine_mul_norm isPreconnected_Icc h0 hK
    (by
      rw [zero_smul ℝ w]
      exact (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (0 • v)).map_zero)
    (by rw [hD, hvel, zero_smul, riemannianExp_zero]; exact hw) h1
  -- At time zero the target fibre is over exp_p(0)=p; rewriting that equality transports
  -- both its metric and its vectors back to the original tangent space.
  rw [hD, hvel, sub_zero, one_smul, zero_smul, riemannianExp_zero] at hnorm
  simpa only [one_smul] using hnorm

/-- The exponential pullback metric on angular vectors in constant curvature. The identity
holds even when `curvatureSine (κ * ‖v‖ ^ 2) 1 = 0`. -/
theorem inner_mfderiv_riemannianExp_of_inner_eq_zero_of_hasSectionalCurvatureAt
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ)
    (w z : TangentSpace I p) (hw : ⟪w, v⟫_ℝ = 0) (hz : ⟪z, v⟫_ℝ = 0) :
    ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w,
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z⟫_ℝ =
        curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 * ⟪w, z⟫_ℝ := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  -- Read T_v(T_p M) as T_p M, so linearity uses the original fibre operations.
  change ⟪L w, L z⟫_ℝ = curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 * ⟪w, z⟫_ℝ
  have hsum : ⟪w + z, v⟫_ℝ = 0 := by rw [inner_add_left, hw, hz, add_zero]
  have hn (u : TangentSpace I p) (hu : ⟪u, v⟫_ℝ = 0) :
      ‖L u‖ ^ 2 =
        curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 * ‖u‖ ^ 2 := by
    exact (congrArg (fun r : ℝ ↦ r ^ 2)
      (norm_mfderiv_riemannianExp_of_inner_eq_zero_of_hasSectionalCurvatureAt hv hK u hu)).trans
        (by rw [mul_pow, sq_abs])
  have hpolar := hn (w + z) hsum
  rw [L.map_add, norm_add_sq_real, norm_add_sq_real, hn w hw, hn z hz] at hpolar
  nlinarith only [hpolar]

/-- The full exponential pullback metric in radial-plus-angular coordinates. The coefficients
of the radial vectors are arbitrary, and the angular vectors need only be perpendicular to
`v`; neither unit speed nor a nonzero radial vector is required. -/
theorem inner_mfderiv_riemannianExp_add_radial_of_hasSectionalCurvatureAt
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ)
    (w z : TangentSpace I p) (hw : ⟪w, v⟫_ℝ = 0) (hz : ⟪z, v⟫_ℝ = 0) (a b : ℝ) :
    ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v (a • v + w),
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v (b • v + z)⟫_ℝ =
        a * b * ‖v‖ ^ 2 + curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 * ⟪w, z⟫_ℝ := by
  let L : TangentSpace I p →L[ℝ] TangentSpace I (riemannianExp I M p v) :=
    mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v
  -- Read the normed-space tangent T_v(T_p M) in its canonical original fibre T_p M.
  change ⟪L (a • v + w), L (b • v + z)⟫_ℝ =
    a * b * ‖v‖ ^ 2 + curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 * ⟪w, z⟫_ℝ
  have hrad (u : TangentSpace I p) : ⟪L v, L u⟫_ℝ = ⟪v, u⟫_ℝ :=
    inner_mfderiv_riemannianExp_radial hv
  have hangular : ⟪L w, L z⟫_ℝ = curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 * ⟪w, z⟫_ℝ :=
    inner_mfderiv_riemannianExp_of_inner_eq_zero_of_hasSectionalCurvatureAt hv hK w z hw hz
  have hvz : ⟪v, z⟫_ℝ = 0 := by rw [real_inner_comm, hz]
  have hrw : ⟪L w, L v⟫_ℝ = 0 := by
    rw [real_inner_comm, hrad, real_inner_comm, hw]
  simp only [L.map_add, L.map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hrad, hvz, hrw, hangular,
    real_inner_self_eq_norm_sq, mul_zero, zero_add, add_zero, mul_assoc, mul_left_comm]

/-- The exponential pullback metric on arbitrary vectors, split by the orthogonal projection
onto the radial line. This form includes `v = 0` and needs no chosen decomposition of the
input vectors. -/
theorem inner_mfderiv_riemannianExp_of_hasSectionalCurvatureAt
    (hv : v ∈ expDomain I M p)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, (leviCivitaConnection I M).HasSectionalCurvatureAt
      (isMetricCompatible_leviCivitaConnection I) (riemannianExp I M p (t • v)) κ)
    (w z : TangentSpace I p) :
    ⟪mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v w,
      mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) v z⟫_ℝ =
        ⟪(ℝ ∙ v).starProjection w, (ℝ ∙ v).starProjection z⟫_ℝ +
          curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 *
            ⟪w - (ℝ ∙ v).starProjection w, z - (ℝ ∙ v).starProjection z⟫_ℝ := by
  have hn (u : TangentSpace I p) : ⟪u - (ℝ ∙ v).starProjection u, v⟫_ℝ = 0 :=
    Submodule.starProjection_inner_eq_zero _ _ (Submodule.mem_span_singleton_self v)
  have hp (u : TangentSpace I p) :
      (ℝ ∙ v).starProjection u = (⟪v, u⟫_ℝ / ‖v‖ ^ 2) • v := by
    simpa only [RCLike.ofReal_real_eq_id, id_eq] using
      (Submodule.starProjection_singleton (𝕜 := ℝ) (v := v) u)
  have hmetric := inner_mfderiv_riemannianExp_add_radial_of_hasSectionalCurvatureAt hv hK
    (w - (ℝ ∙ v).starProjection w) (z - (ℝ ∙ v).starProjection z) (hn w) (hn z)
    (⟪v, w⟫_ℝ / ‖v‖ ^ 2) (⟪v, z⟫_ℝ / ‖v‖ ^ 2)
  rw [← hp w, ← hp z, add_sub_cancel, add_sub_cancel] at hmetric
  have hrad : ⟪(ℝ ∙ v).starProjection w, (ℝ ∙ v).starProjection z⟫_ℝ =
      (⟪v, w⟫_ℝ / ‖v‖ ^ 2) * (⟪v, z⟫_ℝ / ‖v‖ ^ 2) * ‖v‖ ^ 2 := by
    rw [hp w, hp z, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, mul_assoc]
  exact hmetric.trans (congrArg (fun r ↦ r + curvatureSine (κ * ‖v‖ ^ 2) 1 ^ 2 *
    ⟪w - (ℝ ∙ v).starProjection w, z - (ℝ ∙ v).starProjection z⟫_ℝ) hrad.symm)

end TauCeti.Manifold
