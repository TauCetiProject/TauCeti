/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Euclidean
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar

/-!
# Euclidean space is flat

A finite-dimensional real inner-product space `F`, with its standard Riemannian metric, has
vanishing curvature: its Levi-Civita connection is the ordinary Fréchet derivative, so constant
vector fields are parallel, and evaluating the curvature operator on constant fields gives `0`.
Consequently the Ricci tensor and the scalar curvature of the Euclidean metric vanish too.

This is the flat model of every curvature computation: for instance, on Euclidean space the
conformal Laplacian `aₙ Δ⁺ + Scal` of the Yamabe problem reduces to `aₙ Δ⁺`.

## Main results

* `TauCeti.Manifold.curvatureTensor_leviCivitaConnection_model_space`: the curvature tensor of
  the Euclidean metric vanishes.
* `TauCeti.Manifold.ricciTensor_leviCivitaConnection_model_space` and
  `TauCeti.Manifold.scalarCurvature_leviCivitaConnection_model_space`: so do its Ricci tensor and
  scalar curvature.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (flat metrics and the curvature of Euclidean space).
-/

public section

open Bundle CovariantDerivative
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Euclidean space is flat**: the curvature tensor of the standard Riemannian metric on a
finite-dimensional real inner-product space vanishes. -/
@[simp]
theorem curvatureTensor_leviCivitaConnection_model_space (x : F) :
    (leviCivitaConnection (modelWithCornersSelf ℝ F) F).curvatureTensor x = 0 := by
  -- Extend the three tangent vectors to constant vector fields, which are smooth and parallel.
  let X (a : F) (y : F) : TangentSpace (modelWithCornersSelf ℝ F) y :=
    (tangentSpaceCastModel (modelWithCornersSelf ℝ F) y).symm a
  have hX (a : F) : CMDiff ∞ (T% (X a)) :=
    (contMDiff_vectorSpace_iff_contDiff (n := ∞)).2 contDiff_const
  have hX₀ (v : TangentSpace (modelWithCornersSelf ℝ F) x) :
      X (tangentSpaceCastModel (modelWithCornersSelf ℝ F) x v) x = v := by
    simp [X]
  have hpar (a : F) : leviCivitaConnection (modelWithCornersSelf ℝ F) F (X a) = 0 :=
    funext (leviCivitaConnection_const_model_space a)
  have h0 : (fun y : F ↦ (0 : TangentSpace (modelWithCornersSelf ℝ F) y)) = X 0 := by
    funext y
    simp only [X, map_zero]
  ext u v w
  rw [← hX₀ u, ← hX₀ v, ← hX₀ w,
    (leviCivitaConnection (modelWithCornersSelf ℝ F) F).curvatureTensor_apply x
      (hX _) (hX _) (hX _), curvatureOperator_apply]
  simp only [hpar, Pi.zero_apply, zero_apply]
  rw [h0, hpar]
  simp

/-- The Ricci tensor of the standard Riemannian metric on a finite-dimensional real
inner-product space vanishes. -/
theorem ricciTensor_leviCivitaConnection_model_space (x : F) :
    (leviCivitaConnection (modelWithCornersSelf ℝ F) F).ricciTensor x = 0 :=
  ricciTensor_eq_zero_of_curvatureTensor_eq_zero _ x
    (curvatureTensor_leviCivitaConnection_model_space x)

/-- The scalar curvature of the standard Riemannian metric on a finite-dimensional real
inner-product space vanishes. -/
@[simp]
theorem scalarCurvature_leviCivitaConnection_model_space (x : F) :
    (leviCivitaConnection (modelWithCornersSelf ℝ F) F).scalarCurvature x = 0 :=
  scalarCurvature_eq_zero_of_curvatureTensor_eq_zero _ x
    (curvatureTensor_leviCivitaConnection_model_space x)

end TauCeti.Manifold
