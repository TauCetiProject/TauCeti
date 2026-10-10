/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional
import Mathlib.Analysis.Calculus.Deriv.Inv
import all TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
import all TauCeti.Geometry.Manifold.VectorBundle.Tangent

/-!
# Curvature of the upper-half-space metric

The metric `(‖dx‖² + dt²) / t²` has constant-curvature tensor with parameter `-1`.
The computation uses the Levi-Civita connection on constant coordinate fields and its
Leibniz rule, then reads the result in the hyperbolic tangent metric. It applies to every
finite-dimensional real inner product space of horizontal coordinates, including dimension zero.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 3
  (the upper-half-space model) and Theorem 8.34 (its constant sectional curvature).
-/

public section

noncomputable section

open Bundle Manifold CovariantDerivative VectorField Set
open scoped Manifold ContDiff Topology

namespace TauCeti.UpperHalfSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "P" => WithLp 2 (E × ℝ)
local notation "J" => 𝓘(ℝ, P)
local notation "∇" => leviCivitaConnection J (UpperHalfSpace E)

omit [FiniteDimensional ℝ E] in
private theorem mvfderiv_inv_height (x : UpperHalfSpace E) (u : P) :
    mvfderiv J (fun y : UpperHalfSpace E => (height y)⁻¹) x (constantField u x) =
      -(height x)⁻¹ ^ 2 * u.snd := by
  have hi : HasDerivAt (fun t : ℝ => t⁻¹) (-(height x ^ 2)⁻¹)
      ((WithLp.sndL 2 ℝ E ℝ) (coe x)) := by
    simpa using hasDerivAt_inv (height_pos x).ne'
  have hs : HasFDerivAt (fun p : P => p.snd⁻¹)
      (-(height x ^ 2)⁻¹ • WithLp.sndL 2 ℝ E ℝ) (coe x) := by
    simpa only [Function.comp_def, WithLp.sndL_apply] using
      hi.comp_hasFDerivAt (coe x) (WithLp.sndL 2 ℝ E ℝ).hasFDerivAt
  have heq : (fun y : UpperHalfSpace E => (height y)⁻¹) =
      (fun p : P => p.snd⁻¹) ∘ coe := by
    funext y
    simp
  rw [heq, mvfderiv_comp_apply x hs.differentiableAt.mdifferentiableAt
    (contMDiff_coe.mdifferentiableAt (by simp))]
  have hcoe : mfderiv J J (coe : UpperHalfSpace E → P) x =
      ((tangentSpaceCastModel J x).trans
        (NormedSpace.fromTangentSpace (coe x)).symm).toContinuousLinearMap :=
    TauCeti.Manifold.mfderiv_subtype_val (I := J) (show upperHalfSpaceOpens E from x)
  rw [hcoe, mvfderiv_eq_fderiv, hs.fderiv]
  simp [constantField_apply, inv_pow]

private def connectionNumerator (u v : P) : P :=
  inner ℝ u v • WithLp.toLp 2 (0, 1) - u.snd • v - v.snd • u

private theorem connection_const (u v : P) :
    (fun y => ∇ (constantField v) y (constantField u y)) =
      (fun y : UpperHalfSpace E => (height y)⁻¹) • constantField (connectionNumerator u v) := by
  funext y
  apply (tangentSpaceCastModel J y).injective
  simpa only [Pi.smul_apply', map_smul, constantField_apply,
    ContinuousLinearEquiv.apply_symm_apply, connectionNumerator] using
    leviCivitaConnection_const_apply y u v

private theorem second_connection_const (x : UpperHalfSpace E) (u v w : P) :
    tangentSpaceCastModel J x
      (∇ (fun y => ∇ (constantField w) y (constantField v y)) x (constantField u x)) =
      (height x)⁻¹ ^ 2 •
        (connectionNumerator u (connectionNumerator v w) - u.snd • connectionNumerator v w) := by
  rw [connection_const]
  have hne : (WithLp.sndL 2 ℝ E ℝ) (coe x) ≠ 0 := by
    simpa using (height_pos x).ne'
  have hg : MDifferentiableAt J 𝓘(ℝ) (fun y : UpperHalfSpace E => (height y)⁻¹) x := by
    simpa only [Function.comp_def, Pi.inv_apply, WithLp.sndL_apply, snd_coe] using
      (((WithLp.sndL 2 ℝ E ℝ).contDiff.contDiffAt.inv hne).contMDiffAt.comp x
        (contMDiff_coe x)).mdifferentiableAt (by simp)
  rw [∇.isCovariantDerivativeOn.leibniz
    ((contMDiff_constantField _ x).mdifferentiableAt (by simp)) hg]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul]
  rw [mvfderiv_inv_height]
  simp only [constantField_apply, ContinuousLinearEquiv.apply_symm_apply]
  rw [leviCivitaConnection_const_apply]
  simp only [connectionNumerator, smul_sub, smul_smul]
  module

omit [FiniteDimensional ℝ E] in
private theorem connectionNumerator_curvature (u v w : P) :
    connectionNumerator u (connectionNumerator v w) - u.snd • connectionNumerator v w -
      (connectionNumerator v (connectionNumerator u w) - v.snd • connectionNumerator u w) =
      inner ℝ u w • v - inner ℝ v w • u := by
  have hvert (a : P) : inner ℝ a (WithLp.toLp 2 (0, (1 : ℝ)) : P) = a.snd := by simp
  simp only [connectionNumerator, inner_sub_right, real_inner_smul_right, hvert,
    WithLp.sub_snd, WithLp.smul_snd, WithLp.toLp_snd, smul_eq_mul,
    mul_one, smul_sub, smul_smul]
  rw [real_inner_comm v u]
  module

/-- The upper-half-space curvature tensor is the constant-curvature tensor with parameter `-1`,
with inner products taken in the hyperbolic tangent metric. -/
@[simp] theorem curvatureTensor_eq (x : UpperHalfSpace E) (u v w : TangentSpace J x) :
    ∇.curvatureTensor x u v w =
      (-1 : ℝ) • (inner ℝ v w • u - inner ℝ u w • v) := by
  let a := tangentSpaceCastModel J x u
  let b := tangentSpaceCastModel J x v
  let c := tangentSpaceCastModel J x w
  have hu : constantField a x = u := by simp [a]
  have hv : constantField b x = v := by simp [b]
  have hw : constantField c x = w := by simp [c]
  rw [← hu, ← hv, ← hw, ∇.curvatureTensor_apply x
    (contMDiff_constantField a) (contMDiff_constantField b) (contMDiff_constantField c),
    ∇.curvatureOperator_apply, mlieBracket_constantField, map_zero, sub_zero]
  apply (tangentSpaceCastModel J x).injective
  rw [map_sub, second_connection_const, second_connection_const, ← smul_sub,
    connectionNumerator_curvature]
  -- `inner_def` identifies the hyperbolic tangent metric with the height-scaled coordinate metric.
  simp only [map_smul, map_sub]
  rw [inner_def, inner_def]
  simp only [constantField_apply, ContinuousLinearEquiv.apply_symm_apply,
    div_eq_mul_inv, inv_pow, smul_sub, smul_smul]
  module

/-- Every tangent two-plane of the upper-half-space model has sectional curvature `-1`. -/
theorem hasConstantSectionalCurvature :
    ∇.HasConstantSectionalCurvature (isMetricCompatible_leviCivitaConnection J) (-1) :=
  ∇.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
    (isMetricCompatible_leviCivitaConnection J) (-1) curvatureTensor_eq

end TauCeti.UpperHalfSpace
