/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.ClosedBall.OutwardUnitNormal
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.LeviCivita
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace

/-!
# The second fundamental form of the unit sphere bounding the closed unit ball

For the Euclidean metric on the closed unit ball of a real inner product space `E` of dimension
`n + 1`, the second fundamental form of the boundary sphere is the induced metric `h`:

`II_q(u, w) = ⟨dι u, dι w⟩`,

where `ι : ∂B → B` is the inclusion of the boundary manifold
(`TauCeti.boundarySecondFundamentalForm_closedBall`); as bilinear forms, `II_q = h_q`
(`TauCeti.boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm`). The proof extends
the outward unit normal by the radial vector field `x ↦ x`, the pullback along the inclusion
`B → E` of the identity vector field of `E`. The inclusion is a local Riemannian isometry
(`TauCeti.isLocalRiemannianIsometry_subtypeVal_closedBall`), so the Levi-Civita derivative of the
radial field in the direction `v` is `v`, and `II_q(u, w) = ⟨∇_{dι u} N, dι w⟩` is the induced
metric.

With the outward-normal convention, the unit sphere therefore has `II = h`. Replacing the outward
normal by the inward normal in `II_q(u, w) = ⟨∇_{dι u} N, dι w⟩` instead gives
`⟨∇_{dι u} N, dι w⟩ = -h(u, w)` for every extension `N` of the inward unit normal
(`TauCeti.inner_leviCivitaConnection_closedBall_of_eq_inwardUnitNormal`): that convention would
give the unit ball `II = -h`.
-/

public section

open Bundle Filter Metric Module VectorField TauCeti.Manifold
open scoped ContDiff Manifold RealInnerProductSpace Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]

/-- **The second fundamental form of the unit sphere.** For the Euclidean metric on the closed
unit ball, the second fundamental form of the boundary sphere is the induced metric:
`II_q(u, w) = ⟨dι u, dι w⟩`. -/
theorem boundarySecondFundamentalForm_closedBall
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q) :
    boundarySecondFundamentalForm q u w =
      ⟪mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
          q u,
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
          q w⟫ := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hf := isLocalRiemannianIsometry_subtypeVal_closedBall (n := n + 1) (E := E)
  -- The identity vector field of `E` and its pullback, the radial field of the ball.
  let Y : (z : E) → TangentSpace 𝓘(ℝ, E) z := fun z ↦ z
  have hY (z : E) : MDiffAt (T% Y) z :=
    mdifferentiableAt_vectorSpace_iff_differentiableAt.2 differentiableAt_id
  have hN := hf.mdifferentiableAt_mpullback (x := (q : closedBall (0 : E) 1)) (hY _)
  have hNν : ∀ᶠ p : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) in 𝓝 q,
      mpullback (𝓡∂ (n + 1)) 𝓘(ℝ, E) (Subtype.val : closedBall (0 : E) 1 → E) Y p =
        outwardUnitNormal p :=
    Eventually.of_forall fun p ↦
      (hf.mpullback_apply_eq_iff Y _).2 (mvfderiv_outwardUnitNormal_closedBall p).symm
  rw [boundarySecondFundamentalForm_apply_eq_inner_of_eq_outwardUnitNormal q u w hN hNν,
    ← hf.inner_mfderiv, ← hf.inner_mfderiv, hf.mfderiv_leviCivitaConnection_mpullback (hY _)]
  -- The Levi-Civita derivative of the identity field of `E` is the identity.
  have hΓ := leviCivitaConnection_eq_fderiv_model_space (V := Y)
    (x := ((q : closedBall (0 : E) 1) : E)) differentiableAt_id
    (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, E) Subtype.val (q : closedBall (0 : E) 1)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val q u))
  -- `Y` is the identity function of `E`, so its Fréchet derivative is the identity.
  rw [show fderiv ℝ Y ((q : closedBall (0 : E) 1) : E) = ContinuousLinearMap.id ℝ E by
    simp only [Y]; exact fderiv_fun_id] at hΓ
  exact congrArg (fun v ↦ ⟪v, _⟫) (hΓ.trans (ContinuousLinearMap.id_apply _))

/-- On the closed unit ball the second fundamental form of the boundary equals the induced metric,
`II_q = h_q`, as bilinear forms. -/
theorem boundarySecondFundamentalForm_closedBall_eq_boundaryInducedForm
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1)) :
    boundarySecondFundamentalForm q = boundaryInducedForm q :=
  LinearMap.ext₂ fun u w ↦ by
    rw [boundarySecondFundamentalForm_closedBall, boundaryInducedForm_apply]

/-- **The inward-normal convention gives the wrong sign on the unit ball.** For every vector
field `N` on the closed unit ball, differentiable at `q` and equal to the inward unit normal at
the boundary points near `q`, `⟨∇_{dι u} N, dι w⟩ = -⟨dι u, dι w⟩`: with the inward normal in place
of the outward normal in `II_q(u, w) = ⟨∇_{dι u} N, dι w⟩`, the unit sphere would have
`II = -h`. -/
theorem inner_leviCivitaConnection_closedBall_of_eq_inwardUnitNormal
    (q : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1))
    (u w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) q)
    {N : (y : closedBall (0 : E) 1) → TangentSpace (𝓡∂ (n + 1)) y}
    (hN : MDifferentiableAt (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1))))
      (fun y ↦ (⟨y, N y⟩ : TotalSpace (EuclideanSpace ℝ (Fin (n + 1)))
        (fun y : closedBall (0 : E) 1 ↦ TangentSpace (𝓡∂ (n + 1)) y)))
      (q : closedBall (0 : E) 1))
    (hNν : ∀ᶠ p : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) in 𝓝 q,
      N p = inwardUnitNormal p) :
    ⟪CovariantDerivative.leviCivitaConnection (𝓡∂ (n + 1)) (closedBall (0 : E) 1) N q
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
          q u),
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
        q w⟫ =
      -⟪mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
          q u,
        mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) → closedBall (0 : E) 1)
          q w⟫ := by
  rw [inner_leviCivitaConnection_of_eq_inwardUnitNormal q u w hN hNν,
    boundarySecondFundamentalForm_closedBall]

end TauCeti
