/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.PoincareBall.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Sectional.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# Curvature of the Poincaré ball metric

For a finite-dimensional real inner product space `E`, we prove from the Levi-Civita connection
formulas in `PoincareBall.Connection` that the Poincaré ball metric `4 ⟪dx, dy⟫ / (1 - ‖x‖²)²` has
constant-curvature tensor with parameter `-1`, `R(u, v) w = -(⟪v, w⟫ u - ⟪u, w⟫ v)`
(`curvatureTensor_eq`), and deduce its sectional (`hasConstantSectionalCurvature`), Ricci
(`ricciTensor_eq`), and scalar (`scalarCurvature_eq`) curvatures in every finite dimension
`dim E ≥ 0`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  and Theorem 8.34.
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold Set VectorField
open scoped ContDiff Manifold Topology

namespace TauCeti.PoincareBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "J" => 𝓘(ℝ, E)
local notation "∇" => leviCivitaConnection J (PoincareBall E)

omit [FiniteDimensional ℝ E] in
private def connectionLinear (v w : E) : E →L[ℝ] E :=
  (innerSL ℝ v).smulRight w + (innerSL ℝ w).smulRight v - inner ℝ v w • ContinuousLinearMap.id ℝ E

omit [FiniteDimensional ℝ E] in
private theorem connectionLinear_apply (v w p : E) :
    connectionLinear v w p = inner ℝ p v • w + inner ℝ p w • v - inner ℝ v w • p := by
  simp only [connectionLinear, add_apply, sub_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, smul_apply, ContinuousLinearMap.id_apply]
  rw [real_inner_comm v p, real_inner_comm w p]

omit [FiniteDimensional ℝ E] in
private def connectionModel (v w p : E) : E :=
  (2 / (1 - ‖p‖ ^ 2)) • connectionLinear v w p

omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_connectionModel (x : PoincareBall E) (v w : E) :
    HasFDerivAt (connectionModel v w)
      ((2 / (1 - ‖(x : E)‖ ^ 2)) • connectionLinear v w +
        ((4 / (1 - ‖(x : E)‖ ^ 2) ^ 2) • innerSL ℝ (x : E)).smulRight
          (connectionLinear v w (x : E))) (x : E) := by
  set t₀ : ℝ := 1 - ‖(x : E)‖ ^ 2
  have ht₀ : t₀ ≠ 0 := (one_sub_norm_sq_pos x).ne'
  have hsub : HasFDerivAt (fun p : E ↦ 1 - ‖p‖ ^ 2) (0 - 2 • innerSL ℝ (x : E)) (x : E) :=
    (hasFDerivAt_const (1 : ℝ) (x : E)).sub (hasStrictFDerivAt_norm_sq (x : E)).hasFDerivAt
  have hdiv : HasDerivAt (fun t : ℝ ↦ 2 / t) ((0 * t₀ - 2 * 1) / t₀ ^ 2) t₀ :=
    HasDerivAt.fun_div (hasDerivAt_const t₀ (2 : ℝ)) (hasDerivAt_id t₀) ht₀
  have hφ : HasFDerivAt (fun p : E ↦ 2 / (1 - ‖p‖ ^ 2))
      ((4 / t₀ ^ 2) • innerSL ℝ (x : E)) (x : E) := by
    refine (hdiv.comp_hasFDerivAt (x : E) hsub).congr_fderiv ?_
    ext u
    simp only [zero_sub, smul_apply, neg_apply, innerSL_apply_apply, smul_eq_mul]
    field_simp [ht₀]
    ring
  exact hφ.smul (connectionLinear v w).hasFDerivAt

private theorem connection_const_eq (v w : E) :
    (fun y : PoincareBall E ↦ ∇ (constantField w) y (constantField v y)) =
      fun y ↦ (tangentSpaceCastModel J y).symm ((connectionModel v w ∘ coe) y) := by
  funext y
  apply (tangentSpaceCastModel J y).injective
  rw [constantField_apply, leviCivitaConnection_const_apply,
    ContinuousLinearEquiv.apply_symm_apply, Function.comp_apply, connectionModel,
    connectionLinear_apply]

private theorem second_connection_const (x : PoincareBall E) (u v w : E) :
    tangentSpaceCastModel J x
      (∇ (fun y ↦ ∇ (constantField w) y (constantField v y)) x (constantField u x)) =
      (2 / (1 - ‖(x : E)‖ ^ 2)) • connectionLinear v w u +
        (4 / (1 - ‖(x : E)‖ ^ 2) ^ 2) •
          (inner ℝ (x : E) u • connectionLinear v w (x : E) +
            connectionLinear u (connectionLinear v w (x : E)) (x : E)) := by
  have hS := hasFDerivAt_connectionModel x v w
  have hg : MDifferentiableAt J J (connectionModel v w ∘ coe) x :=
    hS.differentiableAt.mdifferentiableAt.comp x (contMDiff_coe.mdifferentiableAt (by simp))
  rw [connection_const_eq v w, constantField_apply, leviCivitaConnection_comp_apply hg u,
    TauCeti.mvfderiv_comp_apply_of_differentiableAt hS.differentiableAt
      (contMDiff_coe.mdifferentiableAt (by simp)),
    mvfderiv_coe_apply, constantField_apply, ContinuousLinearEquiv.apply_symm_apply,
    hS.fderiv, connectionLinear_apply u]
  simp only [connectionModel, Function.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, real_inner_smul_right,
    div_eq_mul_inv, ← inv_pow, smul_add, smul_sub, smul_smul]
  module

omit [FiniteDimensional ℝ E] in
private theorem connectionLinear_curvature_first (u v w : E) :
    connectionLinear v w u - connectionLinear u w v =
      (2 : ℝ) • (inner ℝ u w • v - inner ℝ v w • u) := by
  simp only [connectionLinear_apply]
  rw [real_inner_comm v u]
  module

omit [FiniteDimensional ℝ E] in
private theorem connectionLinear_curvature_second (p u v w : E) :
    inner ℝ p u • connectionLinear v w p + connectionLinear u (connectionLinear v w p) p -
      (inner ℝ p v • connectionLinear u w p + connectionLinear v (connectionLinear u w p) p) =
      (‖p‖ ^ 2 : ℝ) • (inner ℝ u w • v - inner ℝ v w • u) := by
  simp only [connectionLinear_apply, inner_add_right, inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, smul_add, smul_sub, smul_smul, real_inner_comm u v,
    real_inner_comm p u, real_inner_comm p v]
  module

/-- The Riemann curvature tensor of `PoincareBall E` is the constant-curvature tensor with
parameter `-1`, with inner products taken in the hyperbolic tangent metric. -/
@[simp] theorem curvatureTensor_eq (x : PoincareBall E) (u v w : TangentSpace J x) :
    ∇.curvatureTensor x u v w = (-1 : ℝ) • (inner ℝ v w • u - inner ℝ u w • v) := by
  have hcast (z : TangentSpace J x) : constantField (tangentSpaceCastModel J x z) x = z := by simp
  rw [← hcast u, ← hcast v, ← hcast w, ∇.curvatureTensor_apply x
    (contMDiff_constantField _) (contMDiff_constantField _) (contMDiff_constantField _),
    ∇.curvatureOperator_apply, mlieBracket_constantField, map_zero, sub_zero]
  apply (tangentSpaceCastModel J x).injective
  rw [map_sub, second_connection_const, second_connection_const, add_sub_add_comm,
    ← smul_sub, ← smul_sub, connectionLinear_curvature_first, connectionLinear_curvature_second,
    smul_smul, smul_smul, ← add_smul]
  have hcoeff : 2 / (1 - ‖(x : E)‖ ^ 2) * (2 : ℝ) +
      4 / (1 - ‖(x : E)‖ ^ 2) ^ 2 * ‖(x : E)‖ ^ 2 = 4 / (1 - ‖(x : E)‖ ^ 2) ^ 2 := by
    field_simp [(one_sub_norm_sq_pos x).ne']
    ring
  rw [hcoeff]
  simp only [map_smul, map_sub, inner_def, constantField_apply,
    ContinuousLinearEquiv.apply_symm_apply, div_eq_mul_inv, smul_sub, smul_smul]
  module

/-- Every nondegenerate tangent two-plane of `PoincareBall E` has sectional curvature `-1`. -/
theorem hasConstantSectionalCurvature :
    ∇.HasConstantSectionalCurvature (isMetricCompatible_leviCivitaConnection J) (-1) :=
  ∇.hasConstantSectionalCurvature_of_curvatureTensor_eq_smul_inner_sub
    (isMetricCompatible_leviCivitaConnection J) (-1) curvatureTensor_eq

/-- The Ricci tensor of `PoincareBall E` is `-(dim E - 1)` times the hyperbolic metric. In
dimensions zero and one it vanishes. -/
@[simp 1100] theorem ricciTensor_eq (x : PoincareBall E) (u v : TangentSpace J x) :
    ∇.ricciTensor x u v = -((Module.finrank ℝ E : ℝ) - 1) * inner ℝ u v := by
  rw [∇.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub x (-1) (curvatureTensor_eq x)]
  simp only [LinearMap.smul_apply, TauCeti.finrank_tangentSpace, innerₗ_apply_apply, smul_eq_mul]
  ring

/-- The scalar curvature of `PoincareBall E` is `-dim E (dim E - 1)`. -/
@[simp] theorem scalarCurvature_eq (x : PoincareBall E) :
    ∇.scalarCurvature x = -(Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1) := by
  rw [∇.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub x (-1) (curvatureTensor_eq x),
    TauCeti.finrank_tangentSpace]
  ring

end TauCeti.PoincareBall
