/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.VectorField.LieBracket
import all TauCeti.Geometry.Manifold.Riemannian.SL2Tilde.Basic

/-!
# The Levi-Civita connection of `SL₂ℝ~`

Compute the Levi-Civita derivative of constant coordinate fields for the Sasaki metric
`exp (-2y) dx² + dy² + (dz + exp (-y) dx)²`. The formula applies to arbitrary coordinate
vectors at every point. These coefficients determine the connection in the global chart,
and supply the connection terms for curvature computations and the geodesic equation.

The calculation follows the constant-field Koszul argument in
`TauCeti.Geometry.Manifold.Riemannian.Sol.Connection`, using the existing metric and
`CovariantDerivative.two_inner_leviCivitaConnection_eq_koszul`. Constant fields commute;
their inner products vary only with the logarithmic height coordinate `y`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 5
  (the Koszul formula and Christoffel symbols).
* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (the geometry `SL₂ℝ~` and its Sasaki metric).
-/

public section

open Bundle Manifold CovariantDerivative VectorField Real
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.SL2Tilde

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)

/-- The vector field with constant value `v` in the global coordinates of `SL₂ℝ~`. -/
def constantField (v : P) (p : SL2Tilde) : TangentSpace J p :=
  (tangentSpaceCastModel J p).symm v

/-- A constant coordinate field is the inverse tangent-space cast of its coordinate value. -/
@[simp] theorem constantField_apply (v : P) (p : SL2Tilde) :
    constantField v p = (tangentSpaceCastModel J p).symm v := (rfl)

/-- Constant coordinate fields are analytic sections of the tangent bundle, hence `C^n`
for every differentiability index. -/
theorem contMDiff_constantField {n : ℕ∞ω} (v : P) : ContMDiff J ((J).prod J) n
    (fun q => (⟨q, constantField v q⟩ : TangentBundle J SL2Tilde)) := by
  -- The inherited global charts identify SL2Tilde and its tangent casts with the model space.
  exact (contMDiff_vectorSpace_iff_contDiff (n := n)
    (V := fun _ : P => v)).2 contDiff_const

private theorem mdifferentiableAt_constantField (v : P) (p : SL2Tilde) :
    MDifferentiableAt J ((J).prod J)
      (fun q => (⟨q, constantField v q⟩ : TangentBundle J SL2Tilde)) p :=
  (contMDiff_constantField (n := 1) v p).mdifferentiableAt one_ne_zero

private theorem mvfderiv_inner_constantField (u v w : P) (p : SL2Tilde) :
    mvfderiv J (fun q => inner ℝ (constantField u q) (constantField v q)) p
      (constantField w p) =
      -4 * exp (-2 * p.y) * w.2.1 * u.1 * v.1 -
        exp (-p.y) * w.2.1 * (u.1 * v.2.2 + u.2.2 * v.1) := by
  have heq : (fun q => inner ℝ (constantField u q) (constantField v q)) =
      fun q : SL2Tilde => 2 * exp (-2 * q.y) * u.1 * v.1 + u.2.1 * v.2.1 +
        u.2.2 * v.2.2 + exp (-q.y) * (u.1 * v.2.2 + u.2.2 * v.1) := by
    funext q
    have hsq : exp (-q.y) * exp (-q.y) = exp (-2 * q.y) := by
      rw [← exp_add]
      congr 1
      ring
    simp only [inner_def, constantField, ContinuousLinearEquiv.apply_symm_apply]
    linear_combination u.1 * v.1 * hsq
  rw [heq]
  -- SL2Tilde has the model-space atlas; its tangent casts and toProd are identities.
  change (mvfderiv J (fun q : P => 2 * exp (-2 * q.2.1) * u.1 * v.1 +
    u.2.1 * v.2.1 + u.2.2 * v.2.2 +
    exp (-q.2.1) * (u.1 * v.2.2 + u.2.2 * v.1)) (toProd p)) w = _
  rw [mvfderiv_eq_fderiv]
  -- The model-space tangent cast in mvfderiv_eq_fderiv is the identity.
  change fderiv ℝ (fun q : P => 2 * exp (-2 * q.2.1) * u.1 * v.1 +
    u.2.1 * v.2.1 + u.2.2 * v.2.2 +
    exp (-q.2.1) * (u.1 * v.2.2 + u.2.2 * v.1)) (toProd p) w = _
  let hy := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))
  have hd := hy.hasFDerivAt (x := toProd p)
  have h := (((((hd.const_mul (-2)).exp.const_mul 2).mul_const u.1).mul_const v.1
    |>.add_const (u.2.1 * v.2.1)).add_const (u.2.2 * v.2.2)).add
      (hd.neg.exp.mul_const (u.1 * v.2.2 + u.2.2 * v.1))
  simp only [hy, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', Pi.neg_apply] at h
  have h' : HasFDerivAt (𝕜 := ℝ) (fun q : P => 2 * exp (-2 * q.2.1) * u.1 * v.1 +
      u.2.1 * v.2.1 + u.2.2 * v.2.2 +
      exp (-q.2.1) * (u.1 * v.2.2 + u.2.2 * v.1))
      ((-4 * exp (-2 * p.y) * u.1 * v.1 -
        exp (-p.y) * (u.1 * v.2.2 + u.2.2 * v.1)) • hy) (toProd p) := by
    convert h using 1
    ext <;> simp [hy]
    ring
  rw [h'.fderiv]
  simp only [hy, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  ring

/-- The Levi-Civita derivative of a constant coordinate field for the Sasaki metric of
`SL₂ℝ~`. The field has value `v`, and the differentiation direction has value `u`.
All vectors are read in the existing global chart, without choosing an orthonormal frame. -/
@[simp] theorem leviCivitaConnection_const_apply (p : SL2Tilde) (u v : P) :
    tangentSpaceCastModel J p
      (leviCivitaConnection J SL2Tilde (constantField v) p
        ((tangentSpaceCastModel J p).symm u)) =
      (-(3 / 2 : ℝ) * (u.2.1 * v.1 + v.2.1 * u.1) -
          exp p.y / 2 * (u.2.1 * v.2.2 + v.2.1 * u.2.2),
        2 * exp (-2 * p.y) * u.1 * v.1 +
          exp (-p.y) / 2 * (u.1 * v.2.2 + v.1 * u.2.2),
        exp (-p.y) * (u.1 * v.2.1 + v.1 * u.2.1) +
          (u.2.1 * v.2.2 + v.2.1 * u.2.2) / 2) := by
  let a : P :=
    (-(3 / 2 : ℝ) * (u.2.1 * v.1 + v.2.1 * u.1) -
        exp p.y / 2 * (u.2.1 * v.2.2 + v.2.1 * u.2.2),
      2 * exp (-2 * p.y) * u.1 * v.1 +
        exp (-p.y) / 2 * (u.1 * v.2.2 + v.1 * u.2.2),
      exp (-p.y) * (u.1 * v.2.1 + v.1 * u.2.1) +
        (u.2.1 * v.2.2 + v.2.1 * u.2.2) / 2)
  have heq : leviCivitaConnection J SL2Tilde (constantField v) p (constantField u p) =
      constantField a p := by
    apply ext_inner_right ℝ
    intro w
    obtain ⟨w, rfl⟩ := (tangentSpaceCastModel J p).symm.surjective w
    have h := two_inner_leviCivitaConnection_eq_koszul (I := J) (M := SL2Tilde)
      (mdifferentiableAt_constantField u p) (mdifferentiableAt_constantField v p)
      (mdifferentiableAt_constantField w p)
    rw [TauCeti.Manifold.koszul_apply] at h
    have hb (b c : P) : mlieBracket J (constantField b) (constantField c) p = 0 :=
      TauCeti.mlieBracket_const_model_space b c (toProd p)
    simp only [hb, inner_zero_left, mvfderiv_inner_constantField] at h
    simp only [inner_def, constantField, ContinuousLinearEquiv.apply_symm_apply] at h ⊢
    dsimp only [a]
    have hsq : exp (-2 * p.y) = exp (-p.y) * exp (-p.y) := by
      rw [← exp_add]
      congr 1
      ring
    have hinv : exp (-p.y) * exp p.y = 1 := by rw [← exp_add]; simp
    rw [hsq] at h ⊢
    linear_combination h / 2 +
      (exp (-p.y) * w.1 + w.2.2 / 2) *
        (u.2.1 * v.2.2 + v.2.1 * u.2.2) * hinv
  exact congrArg (tangentSpaceCastModel J p) heq

end TauCeti.SL2Tilde
