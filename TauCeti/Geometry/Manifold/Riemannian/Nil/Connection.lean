/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.GroupLieAlgebra
public import TauCeti.Geometry.Manifold.Riemannian.Nil.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Coordinate.ModelSpace
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace
import all TauCeti.Geometry.Manifold.Riemannian.Nil.Basic
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The Levi-Civita connection of Nil

This file computes the Levi-Civita connection of the model geometry `Nil`, the space `ℝ³` with
coordinates `(x, y, z)` and the left-invariant metric `dx² + dy² + (dz - x dy)²`. Writing
`θ(v) = v₃ - x v₂` for the contact form `dz - x dy`, the Christoffel formula of the first kind
shows that at a point with first coordinate `x` the derivative of the constant field `v` in the
direction `u` is

`Γ(u, v) = ½ (u₂ θ(v) + v₂ θ(u), -(u₁ θ(v) + v₁ θ(u)), -(u₁ v₂ + v₁ u₂) - x (u₁ θ(v) + v₁ θ(u)))`.

This is also the Christoffel map of `Nil` in its global chart, the input of the coordinate
formula for the curvature tensor.

The left-invariant vector fields `X_a = mulInvariantVectorField a` of `Nil` are the left
translates `X_a(p) = (a₁, a₂, a₃ + x a₂)` of the tangent vectors `a` at the identity. In
particular `E₁ = ∂_x`, `E₂ = ∂_y + x ∂_z` and `E₃ = ∂_z` form a left-invariant orthonormal frame,
with `[E₁, E₂] = E₃` the only nonzero bracket. The Levi-Civita connection preserves
left-invariant fields:
`∇_{X_a} X_b = X_c` with `c = ½ (a₂ b₃ + b₂ a₃, -(a₁ b₃ + b₁ a₃), a₁ b₂ - a₂ b₁)`. This is the
classical table `∇_{E₁} E₂ = ½ E₃ = -∇_{E₂} E₁`, `∇_{E₁} E₃ = ∇_{E₃} E₁ = -½ E₂`,
`∇_{E₂} E₃ = ∇_{E₃} E₂ = ½ E₁`, with all other entries zero.

## Main results

* `TauCeti.Nil.leviCivitaConnection_const_apply`: the Levi-Civita derivative of a constant field.
* `TauCeti.Nil.christoffelMap_leviCivitaConnection_apply`: the Christoffel map of `Nil` in its
  global chart, in any basis.
* `TauCeti.Nil.tangentSpaceCastModel_mulInvariantVectorField`: the value of the left-invariant
  field `X_a` in the model space.
* `TauCeti.Nil.leviCivitaConnection_mulInvariantVectorField`: the Levi-Civita connection on
  left-invariant fields.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983) 401–487,
  Section 4 (the geometry Nil).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 5 (the Koszul formula and the Christoffel symbols of a metric in coordinates).
-/

public section

open Bundle Manifold CovariantDerivative
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Nil

local notation "R3" => ℝ × ℝ × ℝ

/-! ### The Christoffel map -/

private theorem differentiableAt_form (x : R3) :
    DifferentiableAt ℝ (fun r : R3 ↦ form r.1) x :=
  contDiff_form.differentiable (by simp) x

/-- The derivative of the metric coefficients: only the first coordinate `x` enters the metric,
through the contact form `dz - x dy`. -/
private theorem fderiv_form_apply (x u a b : R3) :
    fderiv ℝ (fun r : R3 ↦ form r.1) x u a b =
      -u.1 * (a.2.1 * (b.2.2 - x.1 * b.2.1) + b.2.1 * (a.2.2 - x.1 * a.2.1)) := by
  have hP : HasFDerivAt (fun r : R3 ↦ form r.1 a b)
      ((-(a.2.1 * (b.2.2 - x.1 * b.2.1) + b.2.1 * (a.2.2 - x.1 * a.2.1))) •
        ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)) x := by
    have ha : HasDerivAt (fun t : ℝ ↦ a.2.2 - t * a.2.1) (-a.2.1) x.1 := by
      simpa using ((hasDerivAt_id x.1).mul_const a.2.1).const_sub a.2.2
    have hb : HasDerivAt (fun t : ℝ ↦ b.2.2 - t * b.2.1) (-b.2.1) x.1 := by
      simpa using ((hasDerivAt_id x.1).mul_const b.2.1).const_sub b.2.2
    have h := ((ha.mul hb).const_add (a.1 * b.1 + a.2.1 * b.2.1)).comp_hasFDerivAt x
      (hasFDerivAt_fst (𝕜 := ℝ) (p := x))
    convert h using 1
    · funext r
      simp [form_apply]
    · congr 1
      ring
  -- Evaluating the derivative of the bilinear field is differentiating its evaluations.
  have h := TauCeti.fderiv_bilin_apply (differentiableAt_form x)
    (differentiableAt_const a) (differentiableAt_const b) u
  simp only [fderiv_const_apply, map_zero, zero_apply, add_zero, hP.fderiv] at h
  rw [← h]
  simp
  ring

/-- The Christoffel map of `Nil` at a point with first coordinate `t`, with the direction `u`
first and the field value `v` second. -/
private def christoffel (t : ℝ) (u v : R3) : R3 :=
  ((u.2.1 * (v.2.2 - t * v.2.1) + v.2.1 * (u.2.2 - t * u.2.1)) / 2,
    -(u.1 * (v.2.2 - t * v.2.1) + v.1 * (u.2.2 - t * u.2.1)) / 2,
    -(u.1 * v.2.1 + v.1 * u.2.1) / 2 -
      t * (u.1 * (v.2.2 - t * v.2.1) + v.1 * (u.2.2 - t * u.2.1)) / 2)

/-- `christoffel` solves the Christoffel formula of the first kind for the metric of `Nil`. -/
private theorem two_mul_form_christoffel (x u v w : R3) :
    2 * form x.1 (christoffel x.1 u v) w =
      fderiv ℝ (fun r : R3 ↦ form r.1) x u v w + fderiv ℝ (fun r : R3 ↦ form r.1) x v w u -
        fderiv ℝ (fun r : R3 ↦ form r.1) x w u v := by
  rw [form_apply, fderiv_form_apply, fderiv_form_apply, fderiv_form_apply, christoffel]
  ring

/- The metric of `Nil` is the metric of `ℝ³` given by the bilinear forms `form x`. Since `Nil` is
a type synonym for `ℝ³` with the same charts, the computation below applies the model-space
results of `TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.VectorSpace`
at the point `toProd p`, with the metric instance of `Nil` read as a metric on `ℝ³`. -/

/-- The Levi-Civita derivative `∇_u V` at `p` of a vector field `V` on `Nil`, read in `ℝ³`, is its
flat derivative plus the Christoffel map `christoffel p.x u (V p)`. -/
private theorem leviCivitaConnection_eq_fderiv_add (p : Nil)
    (V : Π q : Nil, TangentSpace 𝓘(ℝ, R3) q)
    (hV : DifferentiableAt ℝ (fun r : R3 ↦ tangentSpaceCastModel 𝓘(ℝ, R3) (toProd.symm r)
      (V (toProd.symm r))) (toProd p)) (u : R3) :
    tangentSpaceCastModel 𝓘(ℝ, R3) p
        (leviCivitaConnection 𝓘(ℝ, R3) Nil V p ((tangentSpaceCastModel 𝓘(ℝ, R3) p).symm u)) =
      fderiv ℝ (fun r : R3 ↦ tangentSpaceCastModel 𝓘(ℝ, R3) (toProd.symm r)
          (V (toProd.symm r))) (toProd p) u +
        christoffel p.x u (tangentSpaceCastModel 𝓘(ℝ, R3) p (V p)) := by
  let _ : RiemannianBundle (fun x : R3 ↦ TangentSpace 𝓘(ℝ, R3) x) :=
    inferInstanceAs (RiemannianBundle (fun p : Nil ↦ TangentSpace 𝓘(ℝ, R3) p))
  have _ : IsContMDiffRiemannianBundle 𝓘(ℝ, R3) 1 R3 (fun x : R3 ↦ TangentSpace 𝓘(ℝ, R3) x) :=
    inferInstanceAs (IsContMDiffRiemannianBundle 𝓘(ℝ, R3) 1 R3
      (fun p : Nil ↦ TangentSpace 𝓘(ℝ, R3) p))
  have hg (y : R3) (v w : TangentSpace 𝓘(ℝ, R3) y) : inner ℝ v w =
      form y.1 (tangentSpaceCastModel 𝓘(ℝ, R3) y v) (tangentSpaceCastModel 𝓘(ℝ, R3) y w) :=
    (inner_def y v w).trans (form_apply _ _ _).symm
  exact TauCeti.Manifold.leviCivitaConnection_model_space_eq_fderiv_add
    (F := R3) (g := fun r ↦ form r.1) (x := toProd p) (V := V) hg (differentiableAt_form _) hV u
    _ fun w ↦ two_mul_form_christoffel (toProd p) u _ w

/-- The Levi-Civita derivative of the constant field `v` of `Nil` in the direction `u`, at a point
`p` with first coordinate `x`, is
`½ (u₂ θ(v) + v₂ θ(u), -(u₁ θ(v) + v₁ θ(u)), -(u₁ v₂ + v₁ u₂) - x (u₁ θ(v) + v₁ θ(u)))`, where
`θ(v) = v₃ - x v₂`. Tangent vectors are read in the model space `ℝ³`. -/
@[simp]
theorem leviCivitaConnection_const_apply (p : Nil) (u v : R3) :
    tangentSpaceCastModel 𝓘(ℝ, R3) p
      (leviCivitaConnection 𝓘(ℝ, R3) Nil (fun q ↦ (tangentSpaceCastModel 𝓘(ℝ, R3) q).symm v) p
        ((tangentSpaceCastModel 𝓘(ℝ, R3) p).symm u)) =
      ((u.2.1 * (v.2.2 - p.x * v.2.1) + v.2.1 * (u.2.2 - p.x * u.2.1)) / 2,
        -(u.1 * (v.2.2 - p.x * v.2.1) + v.1 * (u.2.2 - p.x * u.2.1)) / 2,
        -(u.1 * v.2.1 + v.1 * u.2.1) / 2 -
          p.x * (u.1 * (v.2.2 - p.x * v.2.1) + v.1 * (u.2.2 - p.x * u.2.1)) / 2) := by
  have h := leviCivitaConnection_eq_fderiv_add p
    (fun q ↦ (tangentSpaceCastModel 𝓘(ℝ, R3) q).symm v) (differentiableAt_const v) u
  simp only [ContinuousLinearEquiv.apply_symm_apply, fderiv_const_apply, zero_apply,
    zero_add] at h
  rw [h, christoffel]

/-- The Christoffel map of `Nil` in its global chart, for any basis of `ℝ³`: with the field value
`v` first and the direction `u` second, it is the derivative of the constant field `v` computed in
`leviCivitaConnection_const_apply`. -/
@[simp]
theorem christoffelMap_leviCivitaConnection_apply {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ R3) (p : Nil) (u v : R3) :
    TauCeti.Manifold.christoffelMap b
      ((leviCivitaConnection 𝓘(ℝ, R3) Nil).isCovariantDerivativeOn
        (s := (trivializationAt R3 (TangentSpace 𝓘(ℝ, R3)) p).baseSet)) p v u =
      ((u.2.1 * (v.2.2 - p.x * v.2.1) + v.2.1 * (u.2.2 - p.x * u.2.1)) / 2,
        -(u.1 * (v.2.2 - p.x * v.2.1) + v.1 * (u.2.2 - p.x * u.2.1)) / 2,
        -(u.1 * v.2.1 + v.1 * u.2.1) / 2 -
          p.x * (u.1 * (v.2.2 - p.x * v.2.1) + v.1 * (u.2.2 - p.x * u.2.1)) / 2) :=
  -- On the type synonym `Nil` of `ℝ³`, the model-space Christoffel map applies at `toProd p`.
  (TauCeti.Manifold.christoffelMap_model_space (F := R3) (x := toProd p) b _ v u).trans
    (leviCivitaConnection_const_apply p u v)

/-! ### Left-invariant vector fields -/

/-- The left-invariant vector field `mulInvariantVectorField a` of `Nil`, the left translate of
the tangent vector `a` at the identity, has value `(a₁, a₂, a₃ + x a₂)` at a point with first
coordinate `x`, read in the model space `ℝ³`. -/
@[simp]
theorem tangentSpaceCastModel_mulInvariantVectorField (a : R3) (p : Nil) :
    tangentSpaceCastModel 𝓘(ℝ, R3) p (mulInvariantVectorField (I := 𝓘(ℝ, R3)) a p) =
      (a.1, a.2.1, a.2.2 + p.x * a.2.1) := by
  -- Both casts are the identity of `ℝ³`, so the value is the left translate of `a` from `1`.
  refine (tangentSpaceCastModel_mfderiv_mul_left p 1 a).trans ?_
  change linearPart p a = _
  simp only [linearPart, xL, yL, zL, ContinuousLinearMap.prod_apply, add_apply,
    smul_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
    ContinuousLinearMap.coe_comp, Function.comp_apply, smul_eq_mul]

/-- **The Levi-Civita connection of Nil on left-invariant fields.** The Levi-Civita derivative of
the left-invariant field `X_b` along `X_a` is the left-invariant field `X_c` with
`c = ½ (a₂ b₃ + b₂ a₃, -(a₁ b₃ + b₁ a₃), a₁ b₂ - a₂ b₁)`. -/
theorem leviCivitaConnection_mulInvariantVectorField (a b : R3) (p : Nil) :
    leviCivitaConnection 𝓘(ℝ, R3) Nil (mulInvariantVectorField (I := 𝓘(ℝ, R3)) b) p
        (mulInvariantVectorField (I := 𝓘(ℝ, R3)) a p) =
      mulInvariantVectorField (I := 𝓘(ℝ, R3)) (G := Nil) ((a.2.1 * b.2.2 + b.2.1 * a.2.2) / 2,
        -(a.1 * b.2.2 + b.1 * a.2.2) / 2, (a.1 * b.2.1 - a.2.1 * b.1) / 2) p := by
  -- Read in `ℝ³`, the field `X_b` is the affine map `r ↦ (b₁, b₂, b₃ + r₁ b₂)`.
  have hV : HasFDerivAt (fun r : R3 ↦ tangentSpaceCastModel 𝓘(ℝ, R3) (toProd.symm r)
      (mulInvariantVectorField (I := 𝓘(ℝ, R3)) b (toProd.symm r)))
      ((0 : R3 →L[ℝ] ℝ).prod ((0 : R3 →L[ℝ] ℝ).prod
        (b.2.1 • ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)))) (toProd p) := by
    have h := (hasFDerivAt_const b.1 (toProd p)).prodMk
      ((hasFDerivAt_const b.2.1 (toProd p)).prodMk
        (((hasFDerivAt_fst (𝕜 := ℝ) (p := toProd p)).mul_const b.2.1).const_add b.2.2))
    convert h using 1
    · funext r
      rw [tangentSpaceCastModel_mulInvariantVectorField]
      simp [x]
  have h := leviCivitaConnection_eq_fderiv_add p (mulInvariantVectorField (I := 𝓘(ℝ, R3)) b)
    hV.differentiableAt (a.1, a.2.1, a.2.2 + p.x * a.2.1)
  apply (tangentSpaceCastModel 𝓘(ℝ, R3) p).injective
  -- The direction `X_a p` is the tangent vector `(a₁, a₂, a₃ + x a₂)`.
  have ha : mulInvariantVectorField (I := 𝓘(ℝ, R3)) a p =
      (tangentSpaceCastModel 𝓘(ℝ, R3) p).symm (a.1, a.2.1, a.2.2 + p.x * a.2.1) := by
    rw [ContinuousLinearEquiv.eq_symm_apply, tangentSpaceCastModel_mulInvariantVectorField]
  rw [ha, h, hV.fderiv, tangentSpaceCastModel_mulInvariantVectorField,
    tangentSpaceCastModel_mulInvariantVectorField, christoffel]
  simp only [ContinuousLinearMap.prod_apply, zero_apply, smul_apply,
    ContinuousLinearMap.coe_fst', smul_eq_mul, Prod.mk_add_mk, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

end TauCeti.Nil
