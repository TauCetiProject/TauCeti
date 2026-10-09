/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action
public import TauCeti.Geometry.Manifold.Riemannian.Sphere

/-!
# Linear isometries act on the round sphere by Riemannian isometries

A linear isometry `e : E ≃ₗᵢ[ℝ] F` restricts to a diffeomorphism between the unit spheres, and
since the round metric is induced by the inclusion into the ambient space, whose differential `e`
intertwines, this restriction is a Riemannian isometry for the round metrics. For `F = E` this gives
an injective homomorphism from the linear isometry group `O(E)` to the isometry group of the round
sphere.

The linear isometries already act transitively on the unit sphere
(`LinearIsometryEquiv.isPretransitive_unitSphere`), so the round sphere is a homogeneous Riemannian
manifold. With `E = EuclideanSpace ℝ (Fin 4)` this is the spherical model geometry
`(S³, Isom(S³))`, one of Thurston's eight three-dimensional geometries.

## Main definitions

* `LinearIsometryEquiv.unitSphereRiemannianIsometry`: the restriction of a linear isometry to the
  unit spheres, as a Riemannian isometry for the round metrics.
* `LinearIsometryEquiv.unitSphereIsomHom`: the injective homomorphism `O(E) →* Isom(S(E))`.

## Main statements

* `LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv`: the differential of the restriction
  to the spheres, read in the ambient space, is the linear isometry itself. Use
  `LinearIsometryEquiv.coe_unitSphereRiemannianIsometry` to apply it to the Riemannian isometry.
* `LinearIsometryEquiv.unitSphereIsomHom_injective`: the homomorphism `O(E) →* Isom(S(E))` is
  injective.
* `TauCeti.isPretransitive_isom_sphere`: the isometry group of the round sphere acts transitively
  on it.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapters 2
  and 3 (the round sphere as a homogeneous Riemannian manifold, with isometries from `O(n + 1)`).
* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §3.8
  (the eight model geometries).
-/

public section

open Metric Module
open scoped ContDiff Manifold

noncomputable section

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {n k : ℕ} [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

/-- The restriction of a linear isometry to the unit spheres is a Riemannian isometry for the round
metrics. -/
def unitSphereRiemannianIsometry (e : E ≃ₗᵢ[ℝ] F) :
    TauCeti.RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1) where
  toDiffeomorph := unitSphereDiffeomorph (n := n) (k := k) e ∞
  inner_mfderiv' x v w := by
    have hcoe : ⇑(unitSphereDiffeomorph (n := n) (k := k) e ∞) = unitSphereEquiv e := by
      rw [← Diffeomorph.coe_toEquiv, unitSphereDiffeomorph_toEquiv]
    rw [TauCeti.inner_tangentSpace_sphere, TauCeti.inner_tangentSpace_sphere, hcoe]
    exact (congrArg₂ (inner ℝ) (mvfderiv_coe_sphere_unitSphereEquiv (k := k) e x v)
      (mvfderiv_coe_sphere_unitSphereEquiv (k := k) e x w)).trans (e.inner_map_map _ _)

/-- The underlying diffeomorphism is the restriction `unitSphereDiffeomorph e ∞`. -/
@[simp]
theorem unitSphereRiemannianIsometry_toDiffeomorph (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereRiemannianIsometry (n := n) (k := k) e).toDiffeomorph =
      unitSphereDiffeomorph e ∞ :=
  (rfl)

/-- The isometry sends a point of the sphere to its image under the linear isometry. -/
@[simp]
theorem coe_unitSphereRiemannianIsometry_apply (e : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) :
    ((unitSphereRiemannianIsometry (n := n) (k := k) e x : sphere (0 : F) 1) : F) = e x :=
  coe_unitSphereDiffeomorph_apply e x

/-- The isometry induced by `e` has the underlying function `unitSphereEquiv e`. This is not a
simp lemma: the simp normal form of `unitSphereRiemannianIsometry e x` for `F = E` is `e • x`
(`unitSphereRiemannianIsometry_apply`). -/
theorem coe_unitSphereRiemannianIsometry (e : E ≃ₗᵢ[ℝ] F) :
    ⇑(unitSphereRiemannianIsometry (n := n) (k := k) e) = unitSphereEquiv e :=
  funext fun x ↦ Subtype.ext (by simp)

/-- For `F = E`, the isometry induced by `e` acts on the sphere as `e` does. -/
@[simp]
theorem unitSphereRiemannianIsometry_apply (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    unitSphereRiemannianIsometry (n := n) (k := n) e x = e • x :=
  Subtype.ext (by simp)

/-- The inverse of the isometry induced by `e` is the isometry induced by `e.symm`. -/
@[simp]
theorem unitSphereRiemannianIsometry_symm (e : E ≃ₗᵢ[ℝ] F) :
    (unitSphereRiemannianIsometry (n := n) (k := k) e).symm =
      unitSphereRiemannianIsometry e.symm :=
  TauCeti.RiemannianIsometry.ext fun x ↦ Subtype.ext <| by
    rw [TauCeti.RiemannianIsometry.coe_symm, unitSphereRiemannianIsometry_toDiffeomorph,
      unitSphereDiffeomorph_symm, coe_unitSphereDiffeomorph_apply,
      coe_unitSphereRiemannianIsometry_apply]

/-- The composite of the isometries induced by `e` and `e'` is the isometry induced by
`e.trans e'`. -/
@[simp]
theorem unitSphereRiemannianIsometry_trans {G : Type*} [NormedAddCommGroup G]
    [InnerProductSpace ℝ G] {l : ℕ} [Fact (finrank ℝ G = l + 1)] (e : E ≃ₗᵢ[ℝ] F)
    (e' : F ≃ₗᵢ[ℝ] G) :
    (unitSphereRiemannianIsometry (n := n) (k := k) e).trans
        (unitSphereRiemannianIsometry (k := l) e') =
      unitSphereRiemannianIsometry (e.trans e') :=
  TauCeti.RiemannianIsometry.ext fun x ↦ Subtype.ext (by simp)

/-- An ambient linear isometry is determined by its restriction as a round-sphere isometry. -/
theorem unitSphereRiemannianIsometry_injective :
    Function.Injective (unitSphereRiemannianIsometry (E := E) (F := F) (n := n) (k := k)) := by
  intro f g h
  have hlin : f.toLinearMap = g.toLinearMap :=
    TauCeti.LinearMap.eq_of_eqOn_unitSphere fun x hx => by
      have hval := congrArg (fun Φ => (Φ ⟨x, hx⟩ : F)) h
      simpa only [LinearEquiv.coe_toLinearMap, coe_toLinearEquiv,
        coe_unitSphereRiemannianIsometry_apply] using hval
  ext x
  exact LinearMap.congr_fun hlin x

/-- The homomorphism from the linear isometry group `O(E)` to the isometry group of the round unit
sphere of `E`, restricting a linear isometry to the sphere. -/
def unitSphereIsomHom : (E ≃ₗᵢ[ℝ] E) →* TauCeti.Isom (𝓡 n) (sphere (0 : E) 1) where
  toFun := unitSphereRiemannianIsometry
  map_one' := TauCeti.RiemannianIsometry.ext fun x ↦ Subtype.ext (by simp)
  map_mul' _ _ := TauCeti.RiemannianIsometry.ext fun x ↦ Subtype.ext (by simp)

/-- The homomorphism `O(E) →* Isom(S(E))` sends `e` to its restriction to the sphere. -/
@[simp]
theorem unitSphereIsomHom_apply (e : E ≃ₗᵢ[ℝ] E) :
    unitSphereIsomHom (n := n) e = unitSphereRiemannianIsometry e :=
  (rfl)

/-- The isometry of the round sphere induced by a linear isometry acts on the sphere as the linear
isometry does. -/
theorem unitSphereIsomHom_smul (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    unitSphereIsomHom (n := n) e • x = e • x :=
  Subtype.ext (by simp)

/-- Forgetting the metric, the restriction of linear isometries to the round sphere is the
inclusion `O(E) →* Diff(S(E))` of `LinearIsometryEquiv.unitSphereDiffHom`. -/
theorem toDiff_comp_unitSphereIsomHom :
    TauCeti.RiemannianIsometry.toDiff.comp (unitSphereIsomHom (E := E) (n := n)) =
      unitSphereDiffHom ∞ :=
  MonoidHom.ext fun e ↦ by simp

/-- The homomorphism `O(E) →* Isom(S(E))` is injective: a linear isometry is determined by its
values on the unit sphere. -/
theorem unitSphereIsomHom_injective :
    Function.Injective (unitSphereIsomHom (E := E) (n := n)) := by
  intro e e' h
  apply unitSphereRiemannianIsometry_injective (n := n) (k := n)
  simpa only [unitSphereIsomHom_apply] using h

end LinearIsometryEquiv

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The round sphere is a homogeneous Riemannian manifold: its isometry group acts transitively,
since already the linear isometries of `E` do. -/
instance isPretransitive_isom_sphere :
    MulAction.IsPretransitive (Isom (𝓡 n) (sphere (0 : E) 1)) (sphere (0 : E) 1) :=
  .of_smul_eq LinearIsometryEquiv.unitSphereIsomHom fun {e x} ↦ e.unitSphereIsomHom_smul x

end TauCeti
