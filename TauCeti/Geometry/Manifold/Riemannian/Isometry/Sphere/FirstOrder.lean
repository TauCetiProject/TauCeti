/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent
import TauCeti.Geometry.Manifold.VectorField.Regularity

/-!
# Extending first-order data on the round sphere

A point of the unit sphere and an isometry of its tangent space determine a unique ambient
linear isometry: act on the radial line by sending the point to the target point, and on
its orthogonal complement by the prescribed tangent map. In particular, at any chosen point,
a Riemannian isometry of round spheres has the same value and differential as the restriction
of an ambient linear isometry.

This supplies the algebraic part of the classification of round-sphere isometries. On a
connected sphere, combining it with determination of a Riemannian isometry by its value and
differential identifies the full isometry group with the ambient orthogonal group.

The construction uses `TauCeti.sphereTangentEquiv`, the differential of the sphere inclusion,
and `LinearIsometryEquiv.extendOrthogonalComplement`.

## Main definitions and results

* `LinearIsometryEquiv.extendSphereTangent`: extend a tangent isometry to the ambient spaces.
* `LinearIsometryEquiv.unitSphereEquiv_extendSphereTangent_apply_self`: the sphere
  restriction sends the source point to the target point.
* `LinearIsometryEquiv.mfderiv_unitSphereEquiv_extendSphereTangent`: the sphere
  restriction has the prescribed manifold differential.
* `LinearIsometryEquiv.eq_extendSphereTangent`: characterize the extension by its value
  and action on tangent vectors.
* `TauCeti.RiemannianIsometry.exists_linearIsometryEquiv_apply_eq_and_mfderiv_eq`:
  match a Riemannian isometry at a point to first order by an ambient linear isometry.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Springer (2018),
  Proposition 5.22 (determination of an isometry by its value and differential).
-/

public section

noncomputable section

open Bundle Metric Module
open scoped ContDiff Manifold

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]
  {x : sphere (0 : E) 1} {y : sphere (0 : F) 1}

/-- Extend an isometry of round-sphere tangent spaces to the ambient spaces, sending
its source point to its target point. -/
def extendSphereTangent (e : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 k) y) : E ≃ₗᵢ[ℝ] F :=
  extendOrthogonalComplement
    ((TauCeti.sphereTangentEquiv (n := n) x).symm.trans
      (e.trans (TauCeti.sphereTangentEquiv (n := k) y)))
    (by simp) (by simp)

/-- The extension sends the source point to the target point. -/
@[simp]
theorem extendSphereTangent_apply_self
    (e : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 k) y) :
    e.extendSphereTangent (x : E) = y := by
  simp only [extendSphereTangent, extendOrthogonalComplement_apply_self]

/-- On tangent vectors read through the sphere inclusion, the extension agrees with
the prescribed tangent isometry. -/
@[simp]
theorem extendSphereTangent_apply_mfderiv
    (e : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 k) y)
    (v : TangentSpace (𝓡 n) x) :
    e.extendSphereTangent (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) =
      mfderiv (𝓡 k) 𝓘(ℝ, F) ((↑) : sphere (0 : F) 1 → F) y (e v) := by
  rw [← TauCeti.coe_sphereTangentEquiv_apply x v]
  simp only [extendSphereTangent, extendOrthogonalComplement_apply_coe, trans_apply,
    symm_apply_apply]
  exact TauCeti.coe_sphereTangentEquiv_apply y (e v)

/-- The sphere restriction of the extension sends the source point to the target point. -/
@[simp]
theorem unitSphereEquiv_extendSphereTangent_apply_self
    (e : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 k) y) :
    unitSphereEquiv e.extendSphereTangent x = y := by
  apply Subtype.ext
  rw [coe_unitSphereEquiv_apply]
  exact extendSphereTangent_apply_self e

/-- The sphere restriction of the extension has the prescribed tangent isometry as
its manifold differential. -/
@[simp]
theorem mfderiv_unitSphereEquiv_extendSphereTangent
    (e : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 k) y) :
    mfderiv (𝓡 n) (𝓡 k) (unitSphereEquiv e.extendSphereTangent) x =
      e.toContinuousLinearEquiv.toContinuousLinearMap := by
  have hfx := unitSphereEquiv_extendSphereTangent_apply_self e
  ext v
  apply injective_mvfderiv_subtypeVal_sphere y
  have h := mvfderiv_coe_sphere_unitSphereEquiv (n := n) (k := k) e.extendSphereTangent x v
  rw [hfx] at h
  -- `TangentSpace` is a type alias indexed by the base point. After identifying
  -- the points, `erw` sees the common model space beneath these different indices.
  erw [h, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact e.extendSphereTangent_apply_mfderiv v

/-- The ambient extension is uniquely characterized by its radial value and its
prescribed action on tangent vectors. -/
theorem eq_extendSphereTangent
    (e : TangentSpace (𝓡 n) x ≃ₗᵢ[ℝ] TangentSpace (𝓡 k) y) (f : E →ₗᵢ[ℝ] F)
    (hfx : f (x : E) = y)
    (hf : ∀ v : TangentSpace (𝓡 n) x,
      f (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v) =
        mfderiv (𝓡 k) 𝓘(ℝ, F) ((↑) : sphere (0 : F) 1 → F) y (e v)) :
    f = e.extendSphereTangent.toLinearIsometry := by
  rw [extendSphereTangent]
  apply eq_extendOrthogonalComplement _ _ _ f hfx
  intro v
  obtain ⟨w, rfl⟩ := (TauCeti.sphereTangentEquiv (n := n) x).surjective v
  simpa only [trans_apply, symm_apply_apply, TauCeti.coe_sphereTangentEquiv_apply] using hf w

end LinearIsometryEquiv

namespace TauCeti.RiemannianIsometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

/-- At any point, a Riemannian isometry of round spheres has the same value and
manifold differential as the restriction of an ambient linear isometry. -/
theorem exists_linearIsometryEquiv_apply_eq_and_mfderiv_eq
    (Φ : RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1))
    (x : sphere (0 : E) 1) :
    ∃ f : E ≃ₗᵢ[ℝ] F, LinearIsometryEquiv.unitSphereEquiv f x = Φ x ∧
      mfderiv (𝓡 n) (𝓡 k) (LinearIsometryEquiv.unitSphereEquiv f) x =
        mfderiv (𝓡 n) (𝓡 k) Φ x := by
  refine ⟨(Φ.mfderivToLinearIsometryEquiv x).extendSphereTangent,
    LinearIsometryEquiv.unitSphereEquiv_extendSphereTangent_apply_self _, ?_⟩
  rw [LinearIsometryEquiv.mfderiv_unitSphereEquiv_extendSphereTangent]
  ext v
  exact mfderivToLinearIsometryEquiv_apply Φ x v

end TauCeti.RiemannianIsometry
