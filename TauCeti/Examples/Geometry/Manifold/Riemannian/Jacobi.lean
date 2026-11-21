/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Euclidean

import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ConstantCurvature
import TauCeti.Geometry.Manifold.Riemannian.Jacobi.ConstantGeodesic
import TauCeti.Geometry.Manifold.Riemannian.Sphere.Curvature
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Examples: Jacobi fields in flat space, on the round sphere and along a constant geodesic

Model computations and conditional sphere formulas for the Jacobi equation
`D_t² J + R(J, γ') γ' = 0`.

* Flat space. Along a unit-speed affine geodesic of an inner-product space the field
  `J t = u + t • w` is a Jacobi field with initial value `u` and initial covariant derivative `w`,
  including `u = w = 0`. The field `t ↦ t² • e` has residual `2 • e`, so it is not a Jacobi field
  for `e ≠ 0`: vanishing at one parameter does not impose the equation.
* The unit sphere. A normal Jacobi field along a unit-speed geodesic of the unit sphere `Sⁿ`
  vanishing at `a` has norm `|sin (t - a)| ‖D_t J (a)‖`, so it vanishes again at `a + π`.
  These are conditional formulas for an assumed Jacobi field; they do not construct a nonzero
  field or establish conjugacy on the sphere.
* A constant geodesic. Along a constant curve the Jacobi fields are the affine fields, so a
  quadratic field with nonzero coefficient is not a Jacobi field even on `[0, 1]`.

## Used results

* `TauCeti.Manifold.IsGeodesicCurveOn.isJacobiFieldOn_add_smul_model_space`,
  `TauCeti.Manifold.alongCurveWithin_add_smul_model_space` and
  `TauCeti.Manifold.jacobiResidual_model_space`: affine fields and residuals in flat space.
* `TauCeti.Manifold.IsJacobiFieldOn.norm_eq_abs_sin_mul_norm` and
  `TauCeti.hasConstantSectionalCurvature_sphere`: the norm of a normal Jacobi field in positive
  constant curvature, specialized here to curvature `1` on the unit sphere.
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
        (fun t ↦ (u + t • w : TangentSpace 𝓘(ℝ, F) (p + t • v))) univ 0 = w ∧
      (∀ t, alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
        (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
          (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (p + r • v))) univ) univ t = 0) ∧
      (∀ t, (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (p + t • v) (u + t • w)
        (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t)
        (curveVelocityWithin 𝓘(ℝ, F) (fun r ↦ p + r • v) univ t) = 0) := by
  refine ⟨(isGeodesicCurveOnFrom_add_smul p v).isGeodesicCurveOn
    |>.isJacobiFieldOn_add_smul_model_space u w, fun t ↦ ?_, by simp,
    alongCurveWithin_add_smul_model_space _ uniqueDiffWithinAt_univ u w, ?_, ?_⟩
  · have hline : HasDerivAt (fun r : ℝ ↦ p + r • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add p
    rw [norm_tangentSpace_vectorSpace, curveVelocityWithin_eq_derivWithin, derivWithin_univ,
      hline.deriv]
    exact (congrArg norm (NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) (p + t • v) v)).trans hv
  · have hD : alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) (fun r ↦ p + r • v)
        (fun r ↦ (u + r • w : TangentSpace 𝓘(ℝ, F) (p + r • v))) univ = fun _ ↦ w :=
      funext fun _ ↦ alongCurveWithin_add_smul_model_space _ uniqueDiffWithinAt_univ u w
    intro t
    simp only [hD, alongCurveWithin_leviCivitaConnection_model_space]
    exact congrFun (derivWithin_const (𝕜 := ℝ) univ w) t
  · simp only [curvatureTensor_leviCivitaConnection_model_space, LinearMap.zero_apply,
      implies_true]

/-- The quadratic field has residual `2 • e` along any curve, within any parameter set
with unique derivatives. -/
public theorem jacobiResidual_sq_smul_model_space
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (γ : ℝ → F) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {t : ℝ} (ht : t ∈ s) (e : F) :
    alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
        (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
          (fun r ↦ (r ^ 2 • e : TangentSpace 𝓘(ℝ, F) (γ r))) s) s t +
      (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (γ t) (t ^ 2 • e)
        (curveVelocityWithin 𝓘(ℝ, F) γ s t)
        (curveVelocityWithin 𝓘(ℝ, F) γ s t) = (2 : ℝ) • e := by
  rw [jacobiResidual_model_space]
  have hD : EqOn (derivWithin (fun r : ℝ ↦ r ^ 2 • e) s) (fun r ↦ (2 * r) • e) s := by
    intro r hr
    simpa using ((hasDerivAt_pow 2 r).smul_const e).hasDerivWithinAt.derivWithin (hs r hr)
  rw [derivWithin_congr hD (hD ht)]
  have h := (((hasDerivAt_id t).const_mul (2 : ℝ)).smul_const e).hasDerivWithinAt.derivWithin
    (hs t ht)
  rw [mul_one] at h
  exact h

/- A quadratic field vanishes at zero but has nonzero residual everywhere on any nonempty
parameter set with unique derivatives, along any curve. In particular it is not Jacobi along a
unit-speed affine geodesic. -/
example {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (γ : ℝ → F) {s : Set ℝ} (hs : UniqueDiffOn ℝ s) (hne : s.Nonempty)
    {e : F} (he : e ≠ 0) :
    (∀ t ∈ s, alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
        (alongCurveWithin (leviCivitaConnection 𝓘(ℝ, F) F) γ
          (fun r ↦ (r ^ 2 • e : TangentSpace 𝓘(ℝ, F) (γ r))) s) s t +
      (leviCivitaConnection 𝓘(ℝ, F) F).curvatureTensor (γ t) (t ^ 2 • e)
        (curveVelocityWithin 𝓘(ℝ, F) γ s t)
        (curveVelocityWithin 𝓘(ℝ, F) γ s t) = (2 : ℝ) • e) ∧
      (2 : ℝ) • e ≠ 0 ∧ (0 : ℝ) ^ 2 • e = 0 ∧
      ¬IsJacobiFieldOn 𝓘(ℝ, F) γ
        (fun t ↦ (t ^ 2 • e : TangentSpace 𝓘(ℝ, F) (γ t))) s := by
  have hne' : (2 : ℝ) • e ≠ 0 := smul_ne_zero two_ne_zero he
  refine ⟨fun t ht ↦ jacobiResidual_sq_smul_model_space γ hs ht e, hne', by simp, fun hJ ↦ ?_⟩
  obtain ⟨t, ht⟩ := hne
  exact hne' ((jacobiResidual_sq_smul_model_space γ hs ht e).symm.trans (hJ.equation t ht))

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
  have heq : a + π = a + π / (√(1 : ℝ) * ‖curveVelocityWithin (𝓡 n) γ s a‖) := by
    simp [hspeed]
  rw [heq] at hb ⊢
  exact hJ.apply_add_pi_div_eq_zero hs ha
    (fun r _ ↦ hasConstantSectionalCurvature_sphere.hasSectionalCurvatureAt (γ r)) hnormal
    one_pos (by intro h; simp [h] at hspeed) hJa hb

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
