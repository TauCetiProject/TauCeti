/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Induced
import TauCeti.Geometry.Manifold.Riemannian.MetricBridge
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# The round metric on the unit sphere

The unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1` is an analytic manifold
modelled on `ℝⁿ` (Mathlib's stereographic atlas), and its inclusion into `E` is an analytic
immersion. The *round metric* is the Riemannian metric induced by this immersion: the inner
product of two tangent vectors is the inner product in `E` of their images under the differential
of the inclusion. This file installs it as the `RiemannianBundle` instance on the tangent bundle of
the sphere, together with its analyticity.

With `E = EuclideanSpace ℝ (Fin 4)` this is the round three-sphere `S³`, the spherical one of
Thurston's eight model geometries.

## Main definitions

* `TauCeti.sphereTangentEquiv`: the isometric identification of tangent spaces with the
  orthogonal complements of their radius vectors.
* `TauCeti.sphereTangentProj`: continuous linear tangential projection
  `E →L[ℝ] TangentSpace (𝓡 n) x`.
* `TauCeti.sphereRoundMetric`: the analytic round metric on the unit sphere.
* `TauCeti.instRiemannianBundleSphere`, `TauCeti.instIsContMDiffRiemannianBundleSphere` and
  `TauCeti.instIsContinuousRiemannianBundleSphere`: the corresponding instances.

## Main statements

* `TauCeti.inner_tangentSpace_sphere`: the round inner product of two tangent vectors is the inner
  product of their images in `E`.
* `TauCeti.norm_tangentSpace_sphere`: the round norm of a tangent vector is the norm of its image
  in `E`.
* `TauCeti.inner_coe_mvfderiv_subtypeVal_sphere`: tangent vectors are orthogonal to the radius.
* `TauCeti.inner_mvfderiv_subtypeVal_sphere_self_pos`: nonzero tangent vectors have positive
  squared length in `E`.
* `TauCeti.contMDiff_coe_sphereTangentEquiv`: reading a tangent vector in `E` via
  `sphereTangentEquiv` is `C^m` on the tangent bundle.
* `TauCeti.mfderiv_subtypeVal_sphereTangentProj`, `TauCeti.sphereTangentProj_mfderiv_subtypeVal`,
  and `TauCeti.ker_sphereTangentProj`: ambient projection formula, left-inverse identity, and kernel
  characterization for `TauCeti.sphereTangentProj`.
* `TauCeti.edist_le_riemannianEDist_sphere`: the chordal distance in `E` is at most the round
  distance.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric as an induced metric).
-/

public section

open Bundle Metric Module
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The round metric on the unit sphere of `E`: the analytic Riemannian metric induced by the
inclusion of the sphere into `E`. -/
def sphereRoundMetric :
    ContMDiffRiemannianMetric (𝓡 n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  inducedRiemannianMetric (n := ω) ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
    injective_mvfderiv_subtypeVal_sphere

/-- The round metric evaluates the inner product of `E` on the images of tangent vectors under the
differential of the inclusion. -/
@[simp]
theorem sphereRoundMetric_inner (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    (sphereRoundMetric (E := E)).inner x v w =
      inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) :=
  inducedRiemannianMetric_inner _ _ _ x v w

/-- The unit sphere is a Riemannian manifold for its round metric. -/
instance instRiemannianBundleSphere :
    RiemannianBundle (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  ⟨(sphereRoundMetric (E := E)).toRiemannianMetric⟩

/-- The round metric is analytic. -/
instance instIsContMDiffRiemannianBundleSphere :
    IsContMDiffRiemannianBundle (𝓡 n) ω (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  Bundle.instIsContMDiffRiemannianBundle (sphereRoundMetric (E := E))

/-- The round metric is continuous. -/
instance instIsContinuousRiemannianBundleSphere :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : sphere (0 : E) 1 ↦ TangentSpace (𝓡 n) x) :=
  Bundle.instIsContinuousRiemannianBundle
    (sphereRoundMetric (E := E)).toContinuousRiemannianMetric

/-- The round inner product of two tangent vectors to the sphere is the inner product in `E` of
their images under the differential of the inclusion. -/
@[simp]
theorem inner_tangentSpace_sphere (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    inner ℝ v w =
      inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) :=
  sphereRoundMetric_inner x v w

/-- The round norm of a tangent vector to the sphere is the norm in `E` of its image under the
differential of the inclusion. -/
@[simp]
theorem norm_tangentSpace_sphere (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    ‖v‖ = ‖mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_sphere]

/-- The differential of the unit-sphere inclusion identifies its round tangent space
isometrically with the orthogonal complement of the radius vector. -/
def sphereTangentEquiv (x : sphere (0 : E) 1) :
    TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] (ℝ ∙ (x : E))ᗮ :=
  let L : TangentSpace (𝓡 n) x →ₗᵢ[ℝ] E :=
    { toLinearMap := (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x).toLinearMap
      norm_map' := fun v => (norm_tangentSpace_sphere x v).symm }
  L.equivRange.trans (LinearIsometryEquiv.ofEq _ _ (range_mvfderiv_subtypeVal x))

/-- In ambient coordinates, the tangent-space identification is the differential of
inclusion. -/
@[simp]
theorem coe_sphereTangentEquiv_apply (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    (sphereTangentEquiv x v : E) =
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v := by
  simp only [sphereTangentEquiv, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.coe_ofEq_apply]
  rw [LinearIsometry.equivRange_apply_coe]
  exact mvfderiv_apply_eq_mfderiv_apply _ x v

/-- The image of a tangent vector to the sphere under the differential of the inclusion is the
value of `TauCeti.sphereTangentEquiv` on it. -/
theorem mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v = sphereTangentEquiv x v := by
  rw [coe_sphereTangentEquiv_apply, mvfderiv_apply_eq_mfderiv_apply]

/-- Reading a tangent vector to the unit sphere in the ambient inner product space `E` via
`sphereTangentEquiv` is `C^m` for every `m : ℕ∞ω` (including `m = ω`). -/
theorem contMDiff_coe_sphereTangentEquiv {m : ℕ∞ω} :
    ContMDiff (𝓡 n).tangent 𝓘(ℝ, E) m
      (fun p : TangentBundle (𝓡 n) (sphere (0 : E) 1) ↦
        (sphereTangentEquiv p.proj p.snd : E)) := by
  have htan : ContMDiff (𝓡 n).tangent 𝓘(ℝ, E).tangent m
      (tangentMap (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E)) :=
    (contMDiff_coe_sphere (E := E) (n := n) (m := ω)).contMDiff_tangentMap le_top
  exact ((contMDiff_snd_tangentBundle_modelSpace E 𝓘(ℝ, E)).comp htan).congr fun p ↦
    coe_sphereTangentEquiv_apply p.proj p.snd

/-- The image of a tangent vector under the differential of the sphere inclusion is orthogonal
to the radius vector. -/
theorem inner_coe_mvfderiv_subtypeVal_sphere (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    inner ℝ (x : E) (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v) = 0 := by
  have h := (sphereTangentEquiv x v).property
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right, coe_sphereTangentEquiv_apply] at h
  rwa [mvfderiv_apply_eq_mfderiv_apply]

/-- Tangential projection of an ambient vector in `E` into the native tangent space
`TangentSpace (𝓡 n) x` at `x : sphere (0 : E) 1`, as a continuous linear map. -/
def sphereTangentProj (x : sphere (0 : E) 1) : E →L[ℝ] TangentSpace (𝓡 n) x :=
  (sphereTangentEquiv x).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto

/-- Unfolding of `TauCeti.sphereTangentProj` in terms of `TauCeti.sphereTangentEquiv` and
orthogonal projection onto `(ℝ ∙ (x : E))ᗮ`. -/
theorem sphereTangentProj_apply (x : sphere (0 : E) 1) (u : E) :
    sphereTangentProj (n := n) x u =
      (sphereTangentEquiv x).symm ((ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto u) := by
  simp [sphereTangentProj]

/-- Applying `TauCeti.sphereTangentEquiv` after `TauCeti.sphereTangentProj` recovers the
orthogonal projection onto `(ℝ ∙ (x : E))ᗮ`. -/
theorem sphereTangentEquiv_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    sphereTangentEquiv (n := n) x (sphereTangentProj (n := n) x u) =
      (ℝ ∙ (x : E))ᗮ.orthogonalProjectionOnto u := by
  rw [sphereTangentProj_apply, LinearIsometryEquiv.apply_symm_apply]

/-- Ambient formula for the tangential projection `TauCeti.sphereTangentProj`: pushing the
projected tangent vector forward by the differential of the sphere inclusion subtracts the
radial component `⟪x, u⟫ • x` from `u`. -/
@[simp]
theorem mfderiv_subtypeVal_sphereTangentProj (x : sphere (0 : E) 1) (u : E) :
    mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (sphereTangentProj (n := n) x u) =
      u - inner ℝ (x : E) u • (x : E) := by
  refine (coe_sphereTangentEquiv_apply x _).symm.trans ?_
  simp only [sphereTangentEquiv_sphereTangentProj, Submodule.coe_orthogonalProjectionOnto_apply,
    Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_unit_singleton ℝ (norm_eq_of_mem_sphere x)]

/-- On an ambient vector already orthogonal to the radius vector `x`, `TauCeti.sphereTangentProj`
agrees with `(TauCeti.sphereTangentEquiv x).symm`. -/
@[simp]
theorem sphereTangentProj_of_mem_orthogonal {x : sphere (0 : E) 1} {u : E}
    (hu : u ∈ (ℝ ∙ (x : E))ᗮ) :
    sphereTangentProj (n := n) x u = (sphereTangentEquiv (n := n) x).symm ⟨u, hu⟩ := by
  rw [sphereTangentProj_apply, Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨u, hu⟩]

/-- Left-inverse identity for `TauCeti.sphereTangentProj` against the differential of the sphere
inclusion: projecting the ambient pushforward of a native tangent vector `v` recovers `v`
exactly. -/
@[simp]
theorem sphereTangentProj_mfderiv_subtypeVal (x : sphere (0 : E) 1)
    (v : TangentSpace (𝓡 n) x) :
    sphereTangentProj x (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) = v := by
  have hv : (sphereTangentEquiv x v : E) ∈ (ℝ ∙ (x : E))ᗮ := (sphereTangentEquiv x v).property
  rw [← coe_sphereTangentEquiv_apply]
  simp [sphereTangentProj_of_mem_orthogonal hv, -coe_sphereTangentEquiv_apply]

/-- The radial vector `x` lies in the kernel of `TauCeti.sphereTangentProj x`. -/
@[simp]
theorem sphereTangentProj_coe_self (x : sphere (0 : E) 1) :
    sphereTangentProj (n := n) x (x : E) = 0 := by
  rw [sphereTangentProj_apply,
    Submodule.orthogonalProjectionOnto_orthogonal_apply_eq_zero
      (Submodule.mem_span_singleton_self (x : E)),
    map_zero]

/-- The kernel of `TauCeti.sphereTangentProj x` is the radial line `ℝ ∙ (x : E)`. -/
@[simp]
theorem ker_sphereTangentProj (x : sphere (0 : E) 1) :
    (sphereTangentProj (n := n) x).ker = ℝ ∙ (x : E) := by
  ext u
  simp [sphereTangentProj_apply]

/-- A nonzero tangent vector to the unit sphere has positive squared length in `E`: the
differential of the inclusion is injective. -/
theorem inner_mvfderiv_subtypeVal_sphere_self_pos (x : sphere (0 : E) 1)
    {v : TangentSpace (𝓡 n) x} (hv : v ≠ 0) :
    0 < inner ℝ (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
      (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v) :=
  real_inner_self_pos.2 fun h ↦
    hv (injective_mvfderiv_subtypeVal_sphere x (h.trans (map_zero _).symm))

/-- **The chordal distance is at most the round distance.** The distance in `E` between two points
of the unit sphere is at most their Riemannian distance for the round metric: the inclusion of the
sphere into `E` preserves the length of tangent vectors, so every path on the sphere is at least as
long as the chord between its endpoints. -/
theorem edist_le_riemannianEDist_sphere (x y : sphere (0 : E) 1) :
    edist x y ≤ Manifold.riemannianEDist (𝓡 n) x y := by
  have h := Manifold.edist_le_mul_riemannianEDist (I := 𝓡 n) (C := 1)
    (contMDiff_coe_sphere (E := E) (n := n)) one_ne_zero (fun p v ↦ ?_) x y
  · simpa [Subtype.edist_eq] using h
  rw [ENNReal.coe_one, one_mul, ← ofReal_norm, ← ofReal_norm, ← norm_tangentSpace_sphere]

end TauCeti
