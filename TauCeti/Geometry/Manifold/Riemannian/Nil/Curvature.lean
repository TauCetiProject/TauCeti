/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Nil.Connection
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Curvature
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
-- Nil inherits the model-space charts; use them to check regularity of its explicit frame.
import all TauCeti.Geometry.Manifold.Riemannian.Nil.Basic

/-!
# Curvature and the central direction of Nil

Compute the curvature and Ricci tensors of `dx² + dy² + (dz - x dy)²` using the
existing Levi-Civita connection on left-invariant fields. In the orthonormal frame
`∂ₓ`, `∂ᵧ + x ∂_z`, `∂_z`, the Ricci eigenvalues are `-1/2`, `-1/2`, `1/2`.
The positive eigenspace is exactly the central line, so every Riemannian isometry
preserves that line. This constrains arbitrary isometries when comparing them with
the known action of the Heisenberg group and `O(2)`.

The curvature convention is `R(u,v)w = ∇ᵤ∇ᵥw - ∇ᵥ∇ᵤw - ∇_[u,v]w`.
The Ricci contraction follows the coordinate-basis argument in
`TauCeti.Geometry.Manifold.Riemannian.Sol.Curvature`.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983),
  401–487, Section 4 (Nil and its isometry group).
* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 7
  (curvature and Ricci contraction).
-/

public section

noncomputable section

open Bundle Manifold CovariantDerivative VectorField
open scoped Manifold ContDiff

namespace TauCeti.Nil

local notation "P" => ℝ × ℝ × ℝ
local notation "J" => 𝓘(ℝ, P)
local notation "∇" => leviCivitaConnection J Nil
local notation "X" => mulInvariantVectorField (I := J) (G := Nil)

private def connectionCoefficients (u v : P) : P :=
  ((u.2.1 * v.2.2 + v.2.1 * u.2.2) / 2,
    -(u.1 * v.2.2 + v.1 * u.2.2) / 2, (u.1 * v.2.1 - u.2.1 * v.1) / 2)

private theorem connection_invariant (u v : P) :
    (fun p => ∇ (X v) p (X u p)) = X (connectionCoefficients u v) :=
  funext (leviCivitaConnection_mulInvariantVectorField u v)

private theorem contMDiff_invariant (u : P) : ContMDiff J ((J).prod J) ∞
    (fun p => (⟨p, X u p⟩ : TangentBundle J Nil)) := by
  have heq : X u = fun p =>
      (tangentSpaceCastModel J p).symm (u.1, u.2.1, u.2.2 + p.x * u.2.1) := by
    funext p
    rw [ContinuousLinearEquiv.eq_symm_apply, tangentSpaceCastModel_mulInvariantVectorField]
  rw [heq]
  -- The tangent casts and charts are the inherited identities of the model space.
  exact (contMDiff_vectorSpace_iff_contDiff (𝕜 := ℝ) (n := ∞)
    (V := fun p : P => (u.1, u.2.1, u.2.2 + p.1 * u.2.1))).2 (by fun_prop)

private theorem bracket_invariant (u v : P) (p : Nil) :
    mlieBracket J (X u) (X v) p = X (0, 0, u.1 * v.2.1 - u.2.1 * v.1) p := by
  have ht := (isTorsionFree_iff_torsion_eq_zero ∇).2
    (torsion_leviCivitaConnection_eq_zero J)
  rw [← (isTorsionFree_iff ∇).mp ht ((contMDiff_invariant u).mdifferentiable (by simp) p)
    ((contMDiff_invariant v).mdifferentiable (by simp) p)]
  rw [leviCivitaConnection_mulInvariantVectorField, leviCivitaConnection_mulInvariantVectorField]
  apply (tangentSpaceCastModel J p).injective
  simp only [map_sub, tangentSpaceCastModel_mulInvariantVectorField]
  ext <;> simp <;> ring

private theorem curvature_invariant (p : Nil) (u v w : P) :
    ∇.curvatureTensor p (X u p) (X v p) (X w p) =
      X ((-3 * w.2.1 * (u.1 * v.2.1 - u.2.1 * v.1) +
          w.2.2 * (u.1 * v.2.2 - u.2.2 * v.1)) / 4,
        (3 * w.1 * (u.1 * v.2.1 - u.2.1 * v.1) +
          w.2.2 * (u.2.1 * v.2.2 - u.2.2 * v.2.1)) / 4,
        (-w.1 * (u.1 * v.2.2 - u.2.2 * v.1) -
          w.2.1 * (u.2.1 * v.2.2 - u.2.2 * v.2.1)) / 4) p := by
  rw [∇.curvatureTensor_apply p (contMDiff_invariant u)
    (contMDiff_invariant v) (contMDiff_invariant w), ∇.curvatureOperator_apply,
    connection_invariant, connection_invariant, bracket_invariant]
  rw [leviCivitaConnection_mulInvariantVectorField, leviCivitaConnection_mulInvariantVectorField,
    leviCivitaConnection_mulInvariantVectorField]
  apply (tangentSpaceCastModel J p).injective
  simp only [map_sub, tangentSpaceCastModel_mulInvariantVectorField, connectionCoefficients]
  ext <;> simp <;> ring

/-- The curvature tensor of Nil in global coordinates, with vectors first read in the
left-invariant orthonormal frame. The final coordinate adds `x` times the second
frame component to convert back to coordinate vectors. -/
@[simp] theorem curvatureTensor_eq (p : Nil) (a b c : TangentSpace J p) :
    let A := tangentSpaceCastModel J p a
    let B := tangentSpaceCastModel J p b
    let C := tangentSpaceCastModel J p c
    let u := (A.1, A.2.1, A.2.2 - p.x * A.2.1)
    let v := (B.1, B.2.1, B.2.2 - p.x * B.2.1)
    let w := (C.1, C.2.1, C.2.2 - p.x * C.2.1)
    let r := ((-3 * w.2.1 * (u.1 * v.2.1 - u.2.1 * v.1) +
        w.2.2 * (u.1 * v.2.2 - u.2.2 * v.1)) / 4,
      (3 * w.1 * (u.1 * v.2.1 - u.2.1 * v.1) +
        w.2.2 * (u.2.1 * v.2.2 - u.2.2 * v.2.1)) / 4,
      (-w.1 * (u.1 * v.2.2 - u.2.2 * v.1) -
        w.2.1 * (u.2.1 * v.2.2 - u.2.2 * v.2.1)) / 4)
    tangentSpaceCastModel J p (∇.curvatureTensor p a b c) =
      (r.1, r.2.1, r.2.2 + p.x * r.2.1) := by
  have heq (a : TangentSpace J p) : a = X
      ((tangentSpaceCastModel J p a).1, (tangentSpaceCastModel J p a).2.1,
        (tangentSpaceCastModel J p a).2.2 - p.x * (tangentSpaceCastModel J p a).2.1) p := by
    apply (tangentSpaceCastModel J p).injective
    simp
  let u : P := ((tangentSpaceCastModel J p a).1, (tangentSpaceCastModel J p a).2.1,
    (tangentSpaceCastModel J p a).2.2 - p.x * (tangentSpaceCastModel J p a).2.1)
  let v : P := ((tangentSpaceCastModel J p b).1, (tangentSpaceCastModel J p b).2.1,
    (tangentSpaceCastModel J p b).2.2 - p.x * (tangentSpaceCastModel J p b).2.1)
  let w : P := ((tangentSpaceCastModel J p c).1, (tangentSpaceCastModel J p c).2.1,
    (tangentSpaceCastModel J p c).2.2 - p.x * (tangentSpaceCastModel J p c).2.1)
  have ha : X u p = a := (heq a).symm
  have hb : X v p = b := (heq b).symm
  have hc : X w p = c := (heq c).symm
  have h := congrArg (tangentSpaceCastModel J p) (curvature_invariant p u v w)
  rw [ha, hb, hc, tangentSpaceCastModel_mulInvariantVectorField] at h
  exact h

/-- The Ricci tensor of Nil is `(-dx² - dy² + (dz - x dy)²) / 2`.
In particular, the central direction has eigenvalue `1/2`. -/
@[simp↓] theorem ricciTensor_eq (p : Nil) (u v : TangentSpace J p) :
    let a := tangentSpaceCastModel J p u
    let b := tangentSpaceCastModel J p v
    ∇.ricciTensor p u v =
      (-a.1 * b.1 - a.2.1 * b.2.1 +
        (a.2.2 - p.x * a.2.1) * (b.2.2 - p.x * b.2.1)) / 2 := by
  let b := (Module.Basis.singleton Unit ℝ).prod
    ((Module.Basis.singleton Unit ℝ).prod (Module.Basis.singleton Unit ℝ))
  rw [∇.ricciTensor_eq_sum p (b.map (tangentSpaceCastModel J p).symm.toLinearEquiv)]
  simp [b, Module.Basis.map_repr, curvatureTensor_eq]
  ring

/-- The Ricci eigenspace with eigenvalue `1/2` is precisely the central line:
both horizontal coordinate components vanish. -/
@[simp↓] theorem ricciTensor_eq_half_inner_iff (p : Nil) (u : TangentSpace J p) :
    (∀ v : TangentSpace J p, ∇.ricciTensor p u v = inner ℝ u v / 2) ↔
      (tangentSpaceCastModel J p u).1 = 0 ∧ (tangentSpaceCastModel J p u).2.1 = 0 := by
  constructor
  · intro h
    have hx := h ((tangentSpaceCastModel J p).symm (1, 0, 0))
    have hy := h ((tangentSpaceCastModel J p).symm (0, 1, p.x))
    simp [ricciTensor_eq, inner_def] at hx hy
    constructor <;> linarith
  · rintro ⟨hx, hy⟩ v
    simp [ricciTensor_eq, inner_def, hx, hy]

/-- The differential of every Riemannian isometry of Nil preserves the central
line, in both directions, at every point. -/
theorem mfderiv_central_iff (Φ : Isom J Nil) (p : Nil) (u : TangentSpace J p) :
    ((tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).1 = 0 ∧
      (tangentSpaceCastModel J (Φ p) (mfderiv J J Φ p u)).2.1 = 0) ↔
      ((tangentSpaceCastModel J p u).1 = 0 ∧ (tangentSpaceCastModel J p u).2.1 = 0) := by
  rw [← ricciTensor_eq_half_inner_iff, ← ricciTensor_eq_half_inner_iff]
  constructor
  · intro h v
    have hv := h (mfderiv J J Φ p v)
    rwa [Φ.ricciTensor_mfderiv, Φ.inner_mfderiv] at hv
  · intro h v
    obtain ⟨w, rfl⟩ := Φ.mfderiv_surjective p v
    rw [Φ.ricciTensor_mfderiv, Φ.inner_mfderiv]
    exact h w

end TauCeti.Nil
