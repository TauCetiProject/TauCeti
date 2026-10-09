/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sol.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import all TauCeti.Geometry.Manifold.Riemannian.Sol.Basic

/-!
# Curvature and Ricci curvature of Sol

Compute the curvature tensor of the metric `exp (2z) dx² + exp (-2z) dy² + dz²`
in global coordinates. Its Ricci tensor is `-2 dz ⊗ dz`: its kernel is precisely the
horizontal plane, and its negative direction singles out the vertical line. These
intrinsic subspaces constrain the differential of an isometry of Sol.

The calculation uses `Sol.leviCivitaConnection_const_apply`, the connection's Leibniz
rule, and the basis-independent trace defining Ricci curvature. The curvature
convention is `R(u,v)w = ∇ᵤ∇ᵥw - ∇ᵥ∇ᵤw - ∇_[u,v]w`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (curvature and Ricci contraction).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (Sol and its isometry group).
-/

public section

noncomputable section

open Bundle Manifold CovariantDerivative VectorField Real
open scoped Manifold ContDiff

namespace TauCeti.Sol

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)
local notation "∇" => leviCivitaConnection J Sol

private theorem hasFDerivAt_exp_height (c : ℝ) (p : Sol) :
    HasFDerivAt (fun q : P => exp (c * q.2.2))
      (exp (c * p.z) • c • ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) (toProd p) := by
  exact (((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.const_mul c).exp

private theorem mdifferentiableAt_exp_height (c : ℝ) (p : Sol) :
    MDifferentiableAt J 𝓘(ℝ) (fun q : Sol => exp (c * q.z)) p := by
  -- Sol's coordinates and charts are those of P, so the coordinate derivative applies.
  exact (hasFDerivAt_exp_height c p).differentiableAt.mdifferentiableAt

private theorem mvfderiv_exp_height (c : ℝ) (p : Sol) (u : P) :
    mvfderiv J (fun q : Sol => exp (c * q.z)) p (constantField u p) =
      exp (c * p.z) * c * u.2.2 := by
  -- Identify the inherited global Sol chart with its model-space chart.
  rw [constantField_apply]
  change mvfderiv J (fun q : P => exp (c * q.2.2)) (toProd p) u = _
  rw [mvfderiv_eq_fderiv, (hasFDerivAt_exp_height c p).fderiv]
  -- The model-space tangent identification is the identity continuous linear equivalence.
  change exp (c * p.z) • c • u.2.2 = _
  simp [mul_assoc]

private def horizontalConnection (u v : P) : P :=
  (u.2.2 * v.1 + v.2.2 * u.1, -(u.2.2 * v.2.1 + v.2.2 * u.2.1), 0)

private theorem connection_const (u v : P) :
    (fun q => ∇ (constantField v) q (constantField u q)) =
      constantField (horizontalConnection u v) +
        (fun q : Sol => exp (2 * q.z)) • constantField (0, 0, -u.1 * v.1) +
        (fun q : Sol => exp (-2 * q.z)) • constantField (0, 0, u.2.1 * v.2.1) := by
  funext q
  apply (tangentSpaceCastModel J q).injective
  rw [constantField_apply, leviCivitaConnection_const_apply]
  simp [horizontalConnection, Prod.ext_iff]
  ring

private theorem second_connection_const (p : Sol) (u v w : P) :
    tangentSpaceCastModel J p
      (∇ (fun q => ∇ (constantField w) q (constantField v q)) p (constantField u p)) =
      (u.2.2 * (v.2.2 * w.1 + w.2.2 * v.1) +
          (-exp (2 * p.z) * v.1 * w.1 + exp (-2 * p.z) * v.2.1 * w.2.1) * u.1,
        u.2.2 * (v.2.2 * w.2.1 + w.2.2 * v.2.1) -
          (-exp (2 * p.z) * v.1 * w.1 + exp (-2 * p.z) * v.2.1 * w.2.1) * u.2.1,
        -exp (2 * p.z) * u.1 * (v.2.2 * w.1 + w.2.2 * v.1) -
          exp (-2 * p.z) * u.2.1 * (v.2.2 * w.2.1 + w.2.2 * v.2.1) -
          2 * exp (2 * p.z) * u.2.2 * v.1 * w.1 -
          2 * exp (-2 * p.z) * u.2.2 * v.2.1 * w.2.1) := by
  have hconst (a : P) := (contMDiff_constantField a p).mdifferentiableAt (by simp)
  have hpos := mdifferentiableAt_exp_height 2 p
  have hneg := mdifferentiableAt_exp_height (-2) p
  rw [connection_const,
    ∇.isCovariantDerivativeOn.add
      (mdifferentiableAt_add_section (hconst _) (hpos.smul_section (hconst _)))
      (hneg.smul_section (hconst _)),
    ∇.isCovariantDerivativeOn.add (hconst _) (hpos.smul_section (hconst _)),
    ∇.isCovariantDerivativeOn.leibniz (hconst _) hpos,
    ∇.isCovariantDerivativeOn.leibniz (hconst _) hneg]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul]
  rw [mvfderiv_exp_height, mvfderiv_exp_height]
  simp only [constantField_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply, leviCivitaConnection_const_apply]
  ext <;> simp [horizontalConnection] <;> ring

/-- The curvature tensor of Sol in global coordinates. The first two vectors are the
curvature directions and the third is the vector acted on. -/
@[simp] theorem curvatureTensor_apply (p : Sol) (a b c : TangentSpace J p) :
    let u := tangentSpaceCastModel J p a
    let v := tangentSpaceCastModel J p b
    let w := tangentSpaceCastModel J p c
    tangentSpaceCastModel J p (∇.curvatureTensor p a b c) =
      (w.2.2 * (u.2.2 * v.1 - v.2.2 * u.1) +
          exp (-2 * p.z) * w.2.1 * (v.2.1 * u.1 - u.2.1 * v.1),
        w.2.2 * (u.2.2 * v.2.1 - v.2.2 * u.2.1) +
          exp (2 * p.z) * w.1 * (v.1 * u.2.1 - u.1 * v.2.1),
        -exp (2 * p.z) * w.1 * (u.2.2 * v.1 - v.2.2 * u.1) -
          exp (-2 * p.z) * w.2.1 * (u.2.2 * v.2.1 - v.2.2 * u.2.1)) := by
  obtain ⟨u, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective a
  obtain ⟨v, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective b
  obtain ⟨w, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective c
  dsimp only
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [← constantField_apply, ← constantField_apply, ← constantField_apply]
  rw [∇.curvatureTensor_apply p (contMDiff_constantField u)
    (contMDiff_constantField v) (contMDiff_constantField w), ∇.curvatureOperator_apply]
  have hb : mlieBracket J (constantField u) (constantField v) p = 0 := by
    -- In the inherited model-space chart these are constant fields.
    have hfield (a : P) : constantField a = (fun _ : Sol => a) := by
      funext q
      rw [constantField_apply]
      rfl
    rw [hfield, hfield]
    exact TauCeti.mlieBracket_const_model_space (𝕜 := ℝ) u v (toProd p)
  rw [hb, map_zero, sub_zero, map_sub, second_connection_const, second_connection_const]
  ext <;> simp <;> ring

/-- Ricci curvature of Sol is `-2 dz ⊗ dz`, at every point. The formula uses global
coordinate vectors, without choosing an orthonormal frame. -/
-- Evaluate before the generic Ricci simp rule expands the tensor to a trace.
@[simp↓] theorem ricciTensor_apply (p : Sol) (u v : TangentSpace J p) :
    ∇.ricciTensor p u v =
      -2 * (tangentSpaceCastModel J p u).2.2 * (tangentSpaceCastModel J p v).2.2 := by
  let b := (Module.Basis.singleton Unit ℝ).prod
    ((Module.Basis.singleton Unit ℝ).prod (Module.Basis.singleton Unit ℝ))
  rw [∇.ricciTensor_eq_sum p (b.map (tangentSpaceCastModel J p).symm.toLinearEquiv)]
  simp [b, Module.Basis.map_repr, curvatureTensor_apply]
  ring

end TauCeti.Sol
