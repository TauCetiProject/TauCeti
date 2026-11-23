/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.RicciFlow.ReducedGeometry.Euclidean.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Curve
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.VectorSpace

/-!
# Identification of the Euclidean backward action

The Euclidean kinetic action is the backward action formed from the standard Riemannian
metric, its native Levi-Civita scalar curvature and native curve velocity. This identifies the
variational model with the metric used by the geodesic and curvature APIs.

For the action convention see J. Morgan and G. Tian, *Ricci Flow and the Poincaré Conjecture*
(2007), Definitions 6.1–6.2. Related formalizations:
https://github.com/frenzymath/lean-eval-submissions and
https://github.com/frenzymath/PoincareConjecture.
-/

public noncomputable section

open Bundle CovariantDerivative MeasureTheory
open scoped Manifold InnerProductSpace

namespace TauCeti.ReducedGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The Euclidean action is the backward Riemannian action of the standard metric, with the
native scalar curvature and velocity. -/
theorem euclideanLAction_eq_riemannian (γ : ℝ → E) (t : ℝ) :
    euclideanLAction γ t = ∫ s in 0..t, Real.sqrt s *
      ((leviCivitaConnection 𝓘(ℝ, E) E).scalarCurvature (γ s) +
        ⟪TauCeti.Manifold.curveVelocity 𝓘(ℝ, E) γ s,
          TauCeti.Manifold.curveVelocity 𝓘(ℝ, E) γ s⟫_ℝ) := by
  simp only [TauCeti.Manifold.scalarCurvature_leviCivitaConnection_model_space,
    TauCeti.Manifold.curveVelocity_eq_deriv, zero_add]
  -- The standard metric's inner product on the model tangent space is the one on `E`.
  change euclideanLAction γ t = ∫ s in 0..t, Real.sqrt s * ⟪deriv γ s, deriv γ s⟫_ℝ
  simp only [real_inner_self_eq_norm_sq, euclideanLAction_eq_integral]

end TauCeti.ReducedGeometry
