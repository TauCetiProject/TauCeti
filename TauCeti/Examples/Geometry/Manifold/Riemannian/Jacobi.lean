/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ConstantCurvature
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ConstantGeodesic
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Euclidean
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature

/-!
# Examples: Jacobi fields in flat space, on the round sphere and along a constant geodesic

Three model computations for the Jacobi equation `D_t² J + R(J, γ') γ' = 0`.

* Flat space. Along a unit-speed affine geodesic of an inner-product space the field
  `J t = u + t • w` is a Jacobi field with initial value `u` and initial covariant derivative `w`,
  including `u = w = 0`. The field `t ↦ t² • e` has residual `2 • e`, so it is not a Jacobi field
  for `e ≠ 0`: vanishing at one parameter does not impose the equation.
* The unit sphere. A normal Jacobi field along a unit-speed geodesic of the unit sphere `Sⁿ`
  vanishing at `a` has norm `|sin (t - a)| ‖D_t J (a)‖`, so it vanishes again at `a + π`. Two
  zeros are impossible in nonpositive curvature, so the sphere shows that the curvature sign
  cannot be dropped there.
* A constant geodesic. Along a constant curve the Jacobi fields are the affine fields, so a
  quadratic field with nonzero coefficient is not a Jacobi field even on `[0, 1]`.

## Used results

* `TauCeti.Manifold.isJacobiFieldOn_add_smul_model_space`,
  `TauCeti.Manifold.alongCurveWithin_add_smul_model_space` and
  `TauCeti.Manifold.not_isJacobiFieldOn_sq_smul_model_space`: affine and quadratic fields in an
  inner-product space.
* `TauCeti.Manifold.IsJacobiFieldOn.norm_eq_abs_sin_mul_norm` and
  `TauCeti.hasConstantSectionalCurvature_sphere`: the norm of a normal Jacobi field in constant
  curvature `1`, and the curvature of the unit sphere.
* `TauCeti.Manifold.isJacobiFieldOn_const_iff`: Jacobi fields along a constant geodesic.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press (1963),
  §14.
-/

open Bundle CovariantDerivative Metric Set
open scoped ContDiff InnerProductSpace Manifold Real

namespace TauCeti.Manifold

/- Along a unit-speed affine geodesic of an inner-product space, `t ↦ u + t • w` is a Jacobi field
with initial value `u` and initial covariant derivative `w`. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (p v u w : F) (hv : ‖v‖ = 1) :
    IsJacobiFieldOn 𝓘(ℝ, F) (fun t ↦ p + t • v)
        (fun t ↦ (u + t • w : TangentSpace 𝓘(ℝ, F) (p + t • v))) univ ∧
      (∀ t, ‖curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t‖ = 1) ∧
      u + (0 : ℝ) • w = u ∧
      alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun t ↦ p + t • v)
        (fun t ↦ (u + t • w : TangentSpace 𝓘(ℝ, F) (p + t • v))) univ 0 = w := by
  refine ⟨isJacobiFieldOn_add_smul_model_space p v u w, fun t ↦ ?_, by simp,
    alongCurveWithin_add_smul_model_space _ u w 0⟩
  have hline : HasDerivAt (fun r : ℝ ↦ p + r • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add p
  rw [norm_tangentSpace_vectorSpace, curveVelocityWithin_eq_derivWithin, derivWithin_univ,
    hline.deriv]
  exact hv

/- In an inner-product space, `t ↦ t² • e` with `e ≠ 0` is not a Jacobi field along any affine
geodesic. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (p v : F) {e : F} (he : e ≠ 0) :
    ¬IsJacobiFieldOn 𝓘(ℝ, F) (fun t ↦ p + t • v)
      (fun t ↦ (t ^ 2 • e : TangentSpace 𝓘(ℝ, F) (p + t • v))) univ :=
  not_isJacobiFieldOn_sq_smul_model_space p v he

section Sphere

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ}
  [Fact (Module.finrank ℝ F = n + 1)] {γ : ℝ → sphere (0 : F) 1}
  {J : ∀ t, TangentSpace (𝓡 n) (γ t)} {s : Set ℝ} {a t : ℝ}

/- A normal Jacobi field along a unit-speed geodesic of the unit sphere, vanishing at `a`, has
norm `|sin (t - a)| ‖D_t J (a)‖`. -/
example (hJ : IsJacobiFieldOn (𝓡 n) γ J s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hnormal : ∀ r ∈ s, ⟪J r, curveVelocityWithin (𝓡 n) γ s r⟫_ℝ = 0)
    (hspeed : ‖curveVelocityWithin (𝓡 n) γ s a‖ = 1) (hJa : J a = 0) (ht : t ∈ s) :
    ‖J t‖ = |Real.sin (t - a)| *
      ‖(leviCivitaConnection (𝓡 n) (sphere (0 : F) 1)).alongCurveWithin γ J s a‖ := by
  simpa [hspeed] using hJ.norm_eq_abs_sin_mul_norm hs ha
    (fun r _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt (γ r)) hnormal
    (by norm_num) (by intro h; simp [h] at hspeed) hJa ht

/- Such a field vanishes again after time `π`, whenever the geodesic is defined that long. -/
example (hJ : IsJacobiFieldOn (𝓡 n) γ J s) (hs : IsPreconnected s) (ha : a ∈ s)
    (hnormal : ∀ r ∈ s, ⟪J r, curveVelocityWithin (𝓡 n) γ s r⟫_ℝ = 0)
    (hspeed : ‖curveVelocityWithin (𝓡 n) γ s a‖ = 1) (hJa : J a = 0) (hb : a + π ∈ s) :
    J (a + π) = 0 := by
  have h := hJ.norm_eq_abs_sin_mul_norm hs ha
    (fun r _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt (γ r)) hnormal
    (by norm_num) (by intro h; simp [h] at hspeed) hJa hb
  rw [← norm_eq_zero]
  simpa [hspeed] using h

end Sphere

/- Along a constant geodesic, a quadratic field with nonzero coefficient is not a Jacobi field on
`[0, 1]`. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    {x : M} {w : TangentSpace I x} (hw : w ≠ 0) :
    ¬IsJacobiFieldOn I (fun _ : ℝ ↦ x) (fun t : ℝ ↦ t ^ 2 • w) (Icc 0 1) := by
  intro h
  obtain ⟨u, v, heq⟩ := (isJacobiFieldOn_const_iff (I := I) (M := M)
    (uniqueDiffOn_Icc one_pos) isPreconnected_Icc (left_mem_Icc.2 zero_le_one)).mp h
  have hu : u = 0 := by simpa using (heq (left_mem_Icc.2 zero_le_one)).symm
  have hv : v = w := by simpa [hu] using (heq (right_mem_Icc.2 zero_le_one)).symm
  have hmid : (1 / 4 : ℝ) • w = (1 / 2 : ℝ) • w := by
    have hm := heq (show (1 / 2 : ℝ) ∈ Icc 0 1 by norm_num)
    norm_num [hu, hv] at hm
    exact hm
  have hz : ((1 / 4 : ℝ) - 1 / 2) • w = 0 := by rw [sub_smul, sub_eq_zero.mpr hmid]
  exact hw ((smul_eq_zero.mp hz).resolve_left (by norm_num))

end TauCeti.Manifold
