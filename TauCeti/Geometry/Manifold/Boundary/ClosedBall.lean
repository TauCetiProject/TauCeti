/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Boundary
public import TauCeti.Geometry.Manifold.Orientation.ClosedBall
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Manifold.Instances.ClosedBall.Outward

/-!
# The orientation of the sphere as the boundary of the ball

The canonical diffeomorphism from the unit sphere to the intrinsic boundary of the closed
unit ball preserves orientation. Both orientations test a tangent basis by adjoining the
radial vector first and reading the resulting basis in the ambient inner product space.
The comparison holds in ambient dimension one, where the sphere consists of two points.

See John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 15.
-/

public section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

attribute [local instance] isManifold_boundary

/-- The outward-normal orientation of the unit sphere agrees under the canonical diffeomorphism
with the outward-first boundary orientation induced by the ambient orientation of the ball. -/
theorem _root_.Orientation.isOrientationPreservingAt_sphereDiffeomorphBoundaryClosedBall
    (o : Orientation ℝ E (Fin (n + 1))) (x : sphere (0 : E) 1) :
    Manifold.Orientation.IsOrientationPreservingAt o.sphereOrientation
      (boundaryOrientation (Manifold.Orientation.closedBall o))
      sphereDiffeomorphBoundaryClosedBall x := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let e := sphereDiffeomorphBoundaryClosedBall (n := n) (E := E)
  -- Test both orientations on the same basis, even when the empty basis has negative sign.
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) x) (finrank_euclideanSpace_fin (𝕜 := ℝ))
  obtain ⟨D, hD⟩ := e.isInvertible_mfderiv (x := x) (by simp)
  let c := b.map D.toLinearEquiv
  have hc (i) : mfderiv (𝓡 n) (𝓡 n) e x (b i) = c i := by
    simp only [c, Basis.map_apply, ← hD, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv]
  apply (Manifold.Orientation.isOrientationPreservingAt_iff_of_basis b c hc).2
  have hdim : Fintype.card (Fin (n + 1)) = finrank ℝ E :=
    (Fintype.card_fin _).trans (Fact.out : finrank ℝ E = n + 1).symm
  let a := basisOfLinearIndependentOfCardEqFinrank
    (LinearIndependent.finCons_mvfderiv_coe_sphere x b.linearIndependent) hdim
  have ha : ⇑a = Fin.cons (x : E) (fun i ↦
      mvfderiv (𝓡 n) (Subtype.val : sphere (0 : E) 1 → E) x (b i)) :=
    coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hball : Manifold.Orientation.IsOrientationPreservingAt (Manifold.Orientation.closedBall o)
      (Manifold.Orientation.model (I := 𝓘(ℝ, E)) o hdim) Subtype.val (e x).val := by
    apply (Manifold.Orientation.isOrientationPreservingAt_iff ..).2
    refine ⟨subtypeValClosedBallTangentEquiv (n := n + 1) (e x).val, ?_, ?_⟩
    · -- The target tangent space is identified with the ambient normed space.
      exact subtypeValClosedBallTangentEquiv_toContinuousLinearMap (n := n + 1) (e x).val
    · exact (Manifold.Orientation.map_orientationAt_closedBall o _).trans
        (Manifold.Orientation.orientationAt_model o hdim _).symm
  rw [o.orientation_eq_orientationAt_sphereOrientation_iff, ← ha,
    Orientation.volumeForm_apply_pos_iff]
  symm
  -- The target tangent space is definitionally `E`, so `a` is a basis of that space.
  refine (boundaryOrientation_spec_of_isOrientationPreservingAt (e x) hball
    (isOutwardPointing_closedBall_radial _ (e x).property) c a ?_).trans ?_
  · simp only [mvfderiv_apply_eq_mfderiv_apply] at ha
    refine ha.trans ?_
    rw [mfderiv_subtypeVal_closedBall_symm_apply]
    refine congrArg₂ Fin.cons (sphereDiffeomorphBoundaryClosedBall_apply_coe x).symm ?_
    funext i
    rw [← hc]
    have hg := (contMDiff_subtypeVal_closedBall (n := n + 1) (k := 1)).comp
      (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := 1) (closedBall (0 : E) 1)).contMDiff
    have hcomp : (fun y ↦ ((e y).val : E)) = Subtype.val :=
      funext sphereDiffeomorphBoundaryClosedBall_apply_coe
    rw [← hcomp]
    exact mfderiv_comp_apply x (hg.mdifferentiableAt one_ne_zero)
      ((e.contMDiff x).mdifferentiableAt (by simp)) (b i)
  · rw [Manifold.Orientation.orientationAt_model]
    -- The two basis orientations agree definitionally because the model tangent space is `E`.
    exact Iff.rfl

end TauCeti
