/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.LinearIsometryEquiv.Topology
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Topology
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Classification
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The orthogonal group is homeomorphic to the round-sphere isometry group

The algebraic identification `LinearIsometryEquiv.unitSphereIsomMulEquiv` is a homeomorphic
group isomorphism for the operator norm topology on ambient linear isometries and the weak
Whitney topology on Riemannian isometries of the sphere. This includes the zero-dimensional
sphere, which consists of two points.

More generally, restriction and ambient extension are continuous for isometries between
unit spheres in different finite-dimensional real inner product spaces. Continuity of the
extension is detected on vectors: its value on a nonzero vector is its sphere value scaled
by the norm of that vector.

## References

* W. P. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, §3.8
  (the spherical model geometry and its full isometry group).
* M. Hirsch, *Differential Topology*, Springer GTM 33, Chapter 2 (Whitney topologies).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff TauCeti.LinearIsometryEquivOperatorNorm
  TauCeti.DiffeomorphWeakWhitney TauCeti.RiemannianIsometryWeakWhitney

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n k : ℕ}
  [Fact (finrank ℝ E = n + 1)] [Fact (finrank ℝ F = k + 1)]

local instance : ProperSpace E := FiniteDimensional.proper ℝ E

namespace LinearIsometryEquiv

/-- Restriction of ambient linear isometries to round spheres is continuous for the operator
norm and Whitney topologies. -/
theorem continuous_unitSphereRiemannianIsometry :
    Continuous (unitSphereRiemannianIsometry (E := E) (F := F) (n := n) (k := k)) := by
  apply TauCeti.RiemannianIsometry.continuous_weakWhitney_iff.mpr
  apply Diffeomorph.continuous_weakWhitney_iff.mpr
  simpa only [unitSphereRiemannianIsometry_toDiffeomorph] using
    (isEmbedding_toContinuousLinearMap.continuous.toContMDiffMap_unitSphereDiffeomorph
      (n := n) (k := k) (m := ∞))

end LinearIsometryEquiv

namespace TauCeti.RiemannianIsometry

/-- Ambient extension of round-sphere isometries is continuous in the operator norm. -/
theorem continuous_toLinearIsometryEquiv :
    Continuous (toLinearIsometryEquiv :
      RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1) → E ≃ₗᵢ[ℝ] F) := by
  apply LinearIsometryEquiv.continuous_operatorNorm_iff_apply.mpr
  intro v
  by_cases hv : v = 0
  · subst v
    simpa only [map_zero] using (continuous_const : Continuous fun _ :
      RiemannianIsometry (𝓡 n) (𝓡 k) (sphere (0 : E) 1) (sphere (0 : F) 1) => (0 : F))
  · let x : sphere (0 : E) 1 :=
      ⟨‖v‖⁻¹ • v, by rw [mem_sphere_zero_iff_norm]; exact norm_smul_inv_norm hv⟩
    have hvx : v = ‖v‖ • (x : E) := by
      simp [x, smul_smul, norm_ne_zero_iff.mpr hv]
    have hvalue (Φ : RiemannianIsometry (𝓡 n) (𝓡 k)
        (sphere (0 : E) 1) (sphere (0 : F) 1)) :
        Φ.toLinearIsometryEquiv v = ‖v‖ • (Φ x : F) := by
      calc
        Φ.toLinearIsometryEquiv v = Φ.toLinearIsometryEquiv (‖v‖ • (x : E)) :=
          congrArg Φ.toLinearIsometryEquiv hvx
        _ = ‖v‖ • Φ.toLinearIsometryEquiv (x : E) := map_smul _ _ _
        _ = ‖v‖ • (Φ x : F) := by rw [toLinearIsometryEquiv_apply]
    simp_rw [hvalue]
    exact (continuous_subtype_val.comp (continuous_eval_const x)).const_smul ‖v‖

end TauCeti.RiemannianIsometry

namespace LinearIsometryEquiv

/-- The full isometry group of the round unit sphere is homeomorphically isomorphic to the
ambient orthogonal group, including the two-point sphere. -/
def unitSphereIsomContinuousMulEquiv :
    (E ≃ₗᵢ[ℝ] E) ≃ₜ* TauCeti.Isom (𝓡 n) (sphere (0 : E) 1) where
  toMulEquiv := unitSphereIsomMulEquiv
  continuous_toFun := by
    rw [MulEquiv.toFun_eq_coe]
    exact (continuous_unitSphereRiemannianIsometry (E := E) (F := E) (n := n) (k := n)).congr
      fun e => ((unitSphereIsomMulEquiv_apply e).trans (unitSphereIsomHom_apply e)).symm
  continuous_invFun := by
    rw [MulEquiv.invFun_eq_symm]
    exact (TauCeti.RiemannianIsometry.continuous_toLinearIsometryEquiv
      (E := E) (F := E) (n := n) (k := n)).congr
        fun Φ => (unitSphereIsomMulEquiv_symm_apply Φ).symm

/-- The homeomorphic group isomorphism restricts an ambient linear isometry to the sphere. -/
@[simp]
theorem unitSphereIsomContinuousMulEquiv_apply (e : E ≃ₗᵢ[ℝ] E) :
    unitSphereIsomContinuousMulEquiv (n := n) e = unitSphereRiemannianIsometry e :=
  (unitSphereIsomMulEquiv_apply e).trans (unitSphereIsomHom_apply e)

/-- Its inverse takes the unique ambient extension of a sphere isometry. -/
@[simp]
theorem unitSphereIsomContinuousMulEquiv_symm_apply
    (Φ : TauCeti.Isom (𝓡 n) (sphere (0 : E) 1)) :
    unitSphereIsomContinuousMulEquiv.symm Φ = Φ.toLinearIsometryEquiv :=
  unitSphereIsomMulEquiv_symm_apply Φ

end LinearIsometryEquiv
