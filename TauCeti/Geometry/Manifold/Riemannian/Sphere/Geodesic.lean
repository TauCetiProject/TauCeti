/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Sphere.Trigonometric
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Immersion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Great-circle geodesics of the round sphere

For orthogonal unit vectors `p, q`, the curve `cos(t) p + sin(t) q` is a unit-speed
geodesic for the native round metric. Its ambient acceleration is minus its position,
so the Gauss formula makes its intrinsic acceleration zero. Uniqueness identifies these
curves with the Riemannian exponential map, without a completeness assumption or a change
from the sphere's native manifold structure.

For every tangent vector `v`, including zero, `coe_riemannianExp_sphere` gives
`exp_p(v) = cos(‖v‖) p + (sin(‖v‖) / ‖v‖) dι_p(v)` in the ambient space.
The antipodal shift by `π` is recorded as `Function.Antiperiodic`, whose standard API
also gives period `2π`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5,
  geodesics of the round sphere.
-/

public section

open Bundle CovariantDerivative Metric Module Set
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The oriented great circle through two orthogonal unit vectors, parametrized by angle. -/
def sphereGreatCircle (p q : sphere (0 : E) 1) (hpq : inner ℝ (p : E) (q : E) = 0)
    (t : ℝ) : sphere (0 : E) 1 :=
  ⟨Real.cos t • (p : E) + Real.sin t • (q : E),
    mem_sphere_zero_iff_norm.mpr (norm_cos_smul_add_sin_smul p q hpq t)⟩

/-- The ambient coordinates of a great circle. -/
@[simp] theorem coe_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (t : ℝ) :
    (sphereGreatCircle p q hpq t : E) = Real.cos t • (p : E) + Real.sin t • (q : E) :=
  (rfl)

/-- A great circle starts at its first defining unit vector. -/
@[simp] theorem sphereGreatCircle_zero (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) : sphereGreatCircle p q hpq 0 = p := by
  ext
  simp

/-- At angle `π / 2` a great circle reaches its second defining unit vector. -/
@[simp] theorem sphereGreatCircle_pi_div_two (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) :
    sphereGreatCircle p q hpq (Real.pi / 2) = q := by
  ext
  simp

/-- Great circles are analytic in their angle parameter. -/
theorem contMDiff_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) :
    ContMDiff 𝓘(ℝ) (𝓡 n) ω (sphereGreatCircle p q hpq) := by
  exact ((Real.contDiff_cos.smul contDiff_const).add
    (Real.contDiff_sin.smul contDiff_const)).contMDiff.codRestrict_sphere _

private theorem hasDerivAt_coe_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (t : ℝ) :
    HasDerivAt (fun r ↦ (sphereGreatCircle p q hpq r : E))
      (-Real.sin t • (p : E) + Real.cos t • (q : E)) t :=
  ((Real.hasDerivAt_cos t).smul_const (p : E)).add
    ((Real.hasDerivAt_sin t).smul_const (q : E))

/-- The great-circle velocity in ambient coordinates. -/
theorem mvfderiv_coe_curveVelocity_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (t : ℝ) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (sphereGreatCircle p q hpq t)
        (curveVelocity (𝓡 n) (sphereGreatCircle p q hpq) t) =
      -Real.sin t • (p : E) + Real.cos t • (q : E) := by
  have hγ := (contMDiff_sphereGreatCircle (n := n) p q hpq).mdifferentiable (by simp) t
  exact (hasDerivAt_comp_curve
    ((contMDiff_coe_sphere (m := 1)).mdifferentiableAt (by simp))
    (hasMFDerivAt_curveVelocity hγ)).unique (hasDerivAt_coe_sphereGreatCircle p q hpq t)

/-- Great circles have unit speed for the installed round metric. -/
@[simp 1100] theorem norm_curveVelocity_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (t : ℝ) :
    ‖curveVelocity (𝓡 n) (sphereGreatCircle p q hpq) t‖ = 1 := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_curveVelocity_sphereGreatCircle]
  have h := norm_cos_smul_add_sin_smul p q hpq (t + Real.pi / 2)
  simpa [Real.cos_add, Real.sin_add, neg_smul] using h

/-- Every great circle is a geodesic for the native round metric, defined for all real time. -/
theorem isGeodesicCurve_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) :
    IsGeodesicCurve (𝓡 n) (sphereGreatCircle p q hpq) := by
  set γ := sphereGreatCircle p q hpq
  have hγ : ContMDiff 𝓘(ℝ) (𝓡 n) 2 γ :=
    (contMDiff_sphereGreatCircle p q hpq).of_le (by simp)
  have hlift : ContMDiff 𝓘(ℝ) (𝓡 n).tangent 1 (curveVelocityLift (𝓡 n) γ) := by
    simpa only [contMDiffOn_univ, curveVelocityLiftWithin_univ] using
      hγ.contMDiffOn.contMDiffOn_curveVelocityLiftWithin (m := 1) (by norm_num)
        uniqueMDiffOn_univ
  have hlift_eq : curveVelocityLift (𝓡 n) γ =
      fun r ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (γ r) (curveVelocity (𝓡 n) γ r) :=
    funext fun r ↦ curveVelocityLift_apply _ _
  rw [hlift_eq] at hlift
  rw [isGeodesicCurve_iff]
  refine ⟨hγ, fun t ↦ ?_⟩
  rw [acceleration_def]
  apply ext_inner_right ℝ
  intro w
  have hcoord := differentiableAt_sectionCoord γ (curveVelocity (𝓡 n) γ)
    (hlift.mdifferentiableAt (by simp) (x := t))
    (FiberBundle.mem_baseSet_trivializationAt _ _ (γ t))
  have hvel : (fun r ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (γ r)
      (curveVelocity (𝓡 n) γ r)) =
      fun r ↦ -Real.sin r • (p : E) + Real.cos r • (q : E) :=
    funext fun r ↦ by
      rw [mvfderiv_coe_curveVelocity_sphereGreatCircle]
  have ha : HasDerivAt (fun r ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (γ r)
      (curveVelocity (𝓡 n) γ r)) (-(γ t : E)) t := by
    rw [hvel]
    convert (((Real.hasDerivAt_sin t).neg.smul_const (p : E)).add
      ((Real.hasDerivAt_cos t).smul_const (q : E))) using 1
    simp [γ, neg_add_rev, neg_smul, add_comm]
  rw [(isLeviCivitaConnection_leviCivitaConnection (I := 𝓡 n)).inner_alongCurve_eq_inner
    contMDiff_coe_sphere.contMDiffAt inner_tangentSpace_sphere
    (hγ.mdifferentiableAt (by simp)) hcoord ha,
    inner_neg_left, inner_coe_mvfderiv_subtypeVal_sphere, neg_zero, inner_zero_left]

/-- The initial velocity of a great circle is its second defining unit vector, read through
the differential of the sphere inclusion. -/
theorem isGeodesicCurveOnFrom_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (v : TangentSpace (𝓡 n) p)
    (hv : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v = (q : E)) :
    IsGeodesicCurveOnFrom (𝓡 n) (sphereGreatCircle p q hpq) univ p v := by
  refine ⟨isGeodesicCurveOn_univ.mpr
    (isGeodesicCurve_sphereGreatCircle (n := n) p q hpq), mem_univ _, ?_⟩
  have h0 := sphereGreatCircle_zero p q hpq
  have htransport {x y : sphere (0 : E) 1} (h : x = y) (u : TangentSpace (𝓡 n) x) :
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) y
          (cast (congrArg (TangentSpace (𝓡 n)) h) u) =
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u := by
    subst y
    rfl
  have hvel : cast (congrArg (TangentSpace (𝓡 n)) h0)
      (curveVelocityWithin (𝓡 n) (sphereGreatCircle p q hpq) univ 0) = v := by
    have h := mvfderiv_coe_curveVelocity_sphereGreatCircle (n := n) p q hpq 0
    have hcoord : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E)
        (sphereGreatCircle p q hpq 0)
        (curveVelocityWithin (𝓡 n) (sphereGreatCircle p q hpq) univ 0) = (q : E) := by
      simpa only [Real.sin_zero, Real.cos_zero, neg_zero, zero_smul, one_smul,
        zero_add, curveVelocityWithin_univ] using h
    apply injective_mvfderiv_subtypeVal_sphere p
    exact (htransport h0 _).trans (hcoord.trans hv.symm)
  exact TotalSpace.ext h0 ((cast_heq _ _).symm.trans (heq_of_eq hvel))

/-- The exponential map along a unit tangent direction is its great circle.
The parameter is arbitrary, including negative times and repeated traversals. -/
theorem riemannianExp_smul_eq_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) (v : TangentSpace (𝓡 n) p)
    (hv : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v = (q : E)) (t : ℝ) :
    riemannianExp (𝓡 n) (sphere (0 : E) 1) p (t • v) = sphereGreatCircle p q hpq t := by
  have h := (isGeodesicCurveOnFrom_sphereGreatCircle p q hpq v hv).comp_mul_left t
    uniqueDiffOn_univ (mapsTo_univ _ _) (mem_univ _)
  simpa only [riemannianExp_def, Function.comp_apply, mul_one] using
    h.eq_maximalGeodesic_of_univ 1

/-- The round-sphere exponential in ambient coordinates. At the zero tangent vector the
totalized coefficient `sin ‖v‖ / ‖v‖` is zero, and the formula still gives the base point.
This includes the zero-dimensional sphere. -/
@[simp] theorem coe_riemannianExp_sphere (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    (riemannianExp (𝓡 n) (sphere (0 : E) 1) p v : E) =
      Real.cos ‖v‖ • (p : E) + (Real.sin ‖v‖ / ‖v‖) •
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v := by
  by_cases hv : v = 0
  · subst v
    simp only [riemannianExp_zero, norm_zero, Real.cos_zero, Real.sin_zero, div_zero,
      one_smul, zero_smul, add_zero]
  have ha : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  let u : TangentSpace (𝓡 n) p := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    dsimp only [u]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ ha]
  let q : sphere (0 : E) 1 :=
    ⟨mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p u,
      mem_sphere_zero_iff_norm.mpr (by
        rw [← norm_tangentSpace_sphere, hu])⟩
  have hpq : inner ℝ (p : E) (q : E) = 0 :=
    inner_coe_mvfderiv_subtypeVal_sphere p u
  have hvu : ‖v‖ • u = v := smul_inv_smul₀ ha v
  have h := congrArg Subtype.val
    (riemannianExp_smul_eq_sphereGreatCircle p q hpq u rfl ‖v‖)
  rw [hvu] at h
  simpa only [coe_sphereGreatCircle, q, u, map_smul, smul_smul, div_eq_mul_inv] using h

/-- A great circle reaches the antipodal point after an additional angle `π`. -/
theorem antiperiodic_sphereGreatCircle (p q : sphere (0 : E) 1)
    (hpq : inner ℝ (p : E) (q : E) = 0) :
    Function.Antiperiodic (sphereGreatCircle p q hpq) Real.pi := by
  intro t
  ext
  simp [Real.cos_add_pi, Real.sin_add_pi, neg_smul, neg_add_rev, add_comm]

end TauCeti
