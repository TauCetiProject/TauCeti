/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Connection
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
-- The derivative bridge uses the inherited model-space atlas of the type synonym.
import all TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic

/-!
# Curvature of the Sasaki metric on `SL₂ℝ~`

Compute curvature and Ricci curvature for the metric
`exp (-2y) dx² + dy² + (dz + exp (-y) dx)²` in global coordinates. The Ricci tensor is
`-(3/2) (exp (-2y) dx² + dy²) + (1/2) (dz + exp (-y) dx)²`. Its eigenspace with
eigenvalue `1/2` is exactly the vertical fibre direction. Since isometries preserve Ricci
curvature, this identifies the intrinsic direction they must preserve when determining
the full isometry group.

The sign convention is `R(u,v)w = ∇ᵤ∇ᵥw - ∇ᵥ∇ᵤw - ∇_[u,v]w`. The calculation follows
the constant-field and trace argument of `TauCeti.Sol.curvatureTensor_eq`, using
`SL2Tilde.leviCivitaConnection_const_apply` for the actual Sasaki connection.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (curvature and Ricci contraction).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (the geometry `SL₂ℝ~` and its isometry group).
-/

public noncomputable section

open Bundle Manifold CovariantDerivative VectorField Real
open scoped Manifold ContDiff

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)
local notation "∇" => leviCivitaConnection J SL2Tilde

private theorem hasFDerivAt_exp_y (c : ℝ) (p : SL2Tilde) :
    HasFDerivAt (fun q : P => exp (c * q.2.1))
      (exp (c * p.y) • c • ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))) (toProd p) :=
  (((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))).hasFDerivAt.const_mul c).exp

private theorem mdifferentiableAt_exp_y (c : ℝ) (p : SL2Tilde) :
    MDifferentiableAt J 𝓘(ℝ) (fun q : SL2Tilde => exp (c * q.y)) p := by
  -- SL2Tilde inherits the model-space charts, so the coordinate derivative applies.
  exact (hasFDerivAt_exp_y c p).differentiableAt.mdifferentiableAt

private theorem mvfderiv_exp_y (c : ℝ) (p : SL2Tilde) (u : P) :
    mvfderiv J (fun q : SL2Tilde => exp (c * q.y)) p (constantField u p) =
      exp (c * p.y) * c * u.2.1 := by
  -- Read the derivative through the inherited global chart and its identity tangent cast.
  rw [constantField_apply]
  change mvfderiv J (fun q : P => exp (c * q.2.1)) (toProd p) u = _
  rw [mvfderiv_eq_fderiv, (hasFDerivAt_exp_y c p).fderiv]
  -- The model-space tangent identification is the identity equivalence.
  change exp (c * p.y) • c • u.2.1 = _
  simp [mul_assoc]

private def connectionCoeff (p : SL2Tilde) (u v : P) : P :=
  (-(3 / 2 : ℝ) * (u.2.1 * v.1 + v.2.1 * u.1) -
      exp p.y / 2 * (u.2.1 * v.2.2 + v.2.1 * u.2.2),
    2 * exp (-2 * p.y) * u.1 * v.1 +
      exp (-p.y) / 2 * (u.1 * v.2.2 + v.1 * u.2.2),
    exp (-p.y) * (u.1 * v.2.1 + v.1 * u.2.1) +
      (u.2.1 * v.2.2 + v.2.1 * u.2.2) / 2)

private def constantCoeff (u v : P) : P :=
  (-(3 / 2 : ℝ) * (u.2.1 * v.1 + v.2.1 * u.1), 0,
    (u.2.1 * v.2.2 + v.2.1 * u.2.2) / 2)

private def positiveCoeff (u v : P) : P :=
  (-(u.2.1 * v.2.2 + v.2.1 * u.2.2) / 2, 0, 0)

private def negativeCoeff (u v : P) : P :=
  (0, (u.1 * v.2.2 + v.1 * u.2.2) / 2, u.1 * v.2.1 + v.1 * u.2.1)

private def doubleNegativeCoeff (u v : P) : P := (0, 2 * u.1 * v.1, 0)

private theorem connection_const (u v : P) :
    (fun q => ∇ (constantField v) q (constantField u q)) =
      constantField (constantCoeff u v) +
        (fun q : SL2Tilde => exp (1 * q.y)) • constantField (positiveCoeff u v) +
        (fun q : SL2Tilde => exp (-1 * q.y)) • constantField (negativeCoeff u v) +
        (fun q : SL2Tilde => exp (-2 * q.y)) • constantField (doubleNegativeCoeff u v) := by
  funext q
  apply (tangentSpaceCastModel J q).injective
  rw [constantField_apply, leviCivitaConnection_const_apply]
  ext <;> simp [constantCoeff, positiveCoeff, negativeCoeff, doubleNegativeCoeff] <;> ring

private theorem second_connection_const (p : SL2Tilde) (u v w : P) :
    tangentSpaceCastModel J p
      (∇ (fun q => ∇ (constantField w) q (constantField v q)) p (constantField u p)) =
      connectionCoeff p u (connectionCoeff p v w) +
        u.2.1 • (exp (1 * p.y) • positiveCoeff v w +
          (-exp (-1 * p.y)) • negativeCoeff v w +
          (-2 * exp (-2 * p.y)) • doubleNegativeCoeff v w) := by
  have hd (a : P) := (contMDiff_constantField (n := 1) a p).mdifferentiableAt one_ne_zero
  have he (c : ℝ) := mdifferentiableAt_exp_y c p
  have h₁ := (he 1).smul_section (hd (positiveCoeff v w))
  have h₂ := (he (-1)).smul_section (hd (negativeCoeff v w))
  have h₃ := (he (-2)).smul_section (hd (doubleNegativeCoeff v w))
  have h₀₁ := mdifferentiableAt_add_section (hd (constantCoeff v w)) h₁
  rw [connection_const, ∇.isCovariantDerivativeOn.add
    (mdifferentiableAt_add_section h₀₁ h₂) h₃,
    ∇.isCovariantDerivativeOn.add h₀₁ h₂,
    ∇.isCovariantDerivativeOn.add (hd (constantCoeff v w)) h₁,
    ∇.isCovariantDerivativeOn.leibniz (hd (positiveCoeff v w)) (he 1),
    ∇.isCovariantDerivativeOn.leibniz (hd (negativeCoeff v w)) (he (-1)),
    ∇.isCovariantDerivativeOn.leibniz (hd (doubleNegativeCoeff v w)) (he (-2))]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul]
  rw [mvfderiv_exp_y, mvfderiv_exp_y, mvfderiv_exp_y]
  simp only [constantField_apply, ContinuousLinearEquiv.apply_symm_apply,
    leviCivitaConnection_const_apply]
  ext <;> simp [connectionCoeff, constantCoeff, positiveCoeff, negativeCoeff,
    doubleNegativeCoeff] <;> ring

/-- Curvature of the Sasaki metric on `SL₂ℝ~`, in global coordinates. The first two
vectors are the curvature directions and the third is the vector acted on. -/
@[simp] theorem curvatureTensor_eq (p : SL2Tilde) (a b c : TangentSpace J p) :
    let u := tangentSpaceCastModel J p a
    let v := tangentSpaceCastModel J p b
    let w := tangentSpaceCastModel J p c
    tangentSpaceCastModel J p (∇.curvatureTensor p a b c) =
      ((exp (-p.y) * w.1 + w.2.2) / 4 * (u.1 * v.2.2 - u.2.2 * v.1) -
          7 / 4 * w.2.1 * (u.1 * v.2.1 - u.2.1 * v.1),
        (3 / 2 * exp (-2 * p.y) * w.1 - exp (-p.y) / 4 * w.2.2) *
            (u.1 * v.2.1 - u.2.1 * v.1) +
          (exp (-p.y) * w.1 + w.2.2) / 4 * (u.2.1 * v.2.2 - u.2.2 * v.2.1),
        -(exp (-2 * p.y) / 2 * w.1 + exp (-p.y) / 4 * w.2.2) *
            (u.1 * v.2.2 - u.2.2 * v.1) +
          w.2.1 * (2 * exp (-p.y) * (u.1 * v.2.1 - u.2.1 * v.1) -
            (u.2.1 * v.2.2 - u.2.2 * v.2.1) / 4)) := by
  obtain ⟨u, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective a
  obtain ⟨v, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective b
  obtain ⟨w, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective c
  dsimp only
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  rw [← constantField_apply, ← constantField_apply, ← constantField_apply]
  rw [∇.curvatureTensor_apply p (contMDiff_constantField u)
    (contMDiff_constantField v) (contMDiff_constantField w), ∇.curvatureOperator_apply]
  have hb : mlieBracket J (constantField u) (constantField v) p = 0 := by
    -- The constant fields are the model-space constant fields in the inherited atlas.
    rw [funext (constantField_apply u), funext (constantField_apply v)]
    exact TauCeti.mlieBracket_const_model_space (𝕜 := ℝ) u v (toProd p)
  rw [hb, map_zero, sub_zero, map_sub, second_connection_const, second_connection_const]
  have hsq : exp (-(p.y * 2)) = exp (-p.y) * exp (-p.y) := by
    rw [← exp_add]
    congr 1
    ring
  have hinv : exp p.y = (exp (-p.y))⁻¹ := by rw [← exp_neg, neg_neg]
  ext <;> simp [connectionCoeff, positiveCoeff, negativeCoeff, doubleNegativeCoeff, hinv]
  all_goals field_simp
  all_goals ring_nf
  all_goals rw [hsq]
  all_goals ring

/-- Ricci curvature of the Sasaki metric is `-3/2` times the horizontal metric plus
`1/2` times the square of the vertical connection form `dz + exp (-y) dx`. -/
@[simp↓] theorem ricciTensor_eq (p : SL2Tilde) (u v : TangentSpace J p) :
    ∇.ricciTensor p u v =
      -(3 / 2 : ℝ) * (exp (-2 * p.y) * (tangentSpaceCastModel J p u).1 *
        (tangentSpaceCastModel J p v).1 +
        (tangentSpaceCastModel J p u).2.1 * (tangentSpaceCastModel J p v).2.1) +
      1 / 2 * ((tangentSpaceCastModel J p u).2.2 +
        exp (-p.y) * (tangentSpaceCastModel J p u).1) *
        ((tangentSpaceCastModel J p v).2.2 +
          exp (-p.y) * (tangentSpaceCastModel J p v).1) := by
  let b := (Module.Basis.singleton Unit ℝ).prod
    ((Module.Basis.singleton Unit ℝ).prod (Module.Basis.singleton Unit ℝ))
  rw [∇.ricciTensor_eq_sum p (b.map (tangentSpaceCastModel J p).symm.toLinearEquiv)]
  have hsq : exp (-(p.y * 2)) = exp (-p.y) * exp (-p.y) := by
    rw [← exp_add]
    congr 1
    ring
  simp [b, Module.Basis.map_repr, curvatureTensor_eq]
  ring_nf
  rw [hsq]
  ring

/-- The Ricci eigenspace with eigenvalue `1/2` is precisely the vertical fibre direction.
The eigenvalue is taken relative to the Sasaki inner product, rather than the coordinate
Euclidean inner product. -/
-- Recognize the intrinsic eigenvector equation before expanding its two bilinear forms.
@[simp↓] theorem ricciTensor_eq_half_inner_iff (p : SL2Tilde) (u : TangentSpace J p) :
    (∀ v : TangentSpace J p, ∇.ricciTensor p u v = (1 / 2 : ℝ) * inner ℝ u v) ↔
      (tangentSpaceCastModel J p u).1 = 0 ∧
        (tangentSpaceCastModel J p u).2.1 = 0 := by
  constructor
  · intro h
    have hx := h (constantField (1, 0, 0) p)
    have hy := h (constantField (0, 1, 0) p)
    simp only [ricciTensor_eq, inner_def, constantField_apply,
      ContinuousLinearEquiv.apply_symm_apply] at hx hy
    have hx' : exp (-2 * p.y) * (tangentSpaceCastModel J p u).1 = 0 := by
      linarith
    exact ⟨(mul_eq_zero.mp hx').resolve_left (exp_ne_zero _), by linarith⟩
  · rintro ⟨hx, hy⟩ v
    simp [ricciTensor_eq, inner_def, hx, hy, mul_assoc]

/-- Every Riemannian isometry of `SL₂ℝ~` preserves the vertical fibre direction.
Both implications are included: a tangent vector is vertical exactly when its image is. -/
theorem mfderiv_vertical_iff (Φ : Isom J SL2Tilde) (p : SL2Tilde)
    (u : TangentSpace J p) :
    ((tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).1 = 0 ∧
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.1 = 0) ↔
      (tangentSpaceCastModel J p u).1 = 0 ∧
        (tangentSpaceCastModel J p u).2.1 = 0 := by
  rw [← ricciTensor_eq_half_inner_iff, ← ricciTensor_eq_half_inner_iff]
  constructor
  · intro h v
    simpa only [Φ.ricciTensor_mfderiv, Φ.inner_mfderiv] using h (mfderiv J J Φ p v)
  · intro h v
    obtain ⟨w, hw⟩ := (Φ.mfderivToLinearIsometryEquiv p).surjective v
    rw [RiemannianIsometry.mfderivToLinearIsometryEquiv_apply] at hw
    rw [← hw, Φ.ricciTensor_mfderiv, Φ.inner_mfderiv]
    exact h w

end TauCeti.SL2Tilde
