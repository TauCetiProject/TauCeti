/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion

/-!
# Curvature of a connection plus a one-form

Every connection on a vector bundle `V` differs from a fixed one `∇` by a one-form `A` with values
in the endomorphisms of `V`, and `∇ + A` is Mathlib's `CovariantDerivative.addOneForm`. With the
convention of `addOneForm`, `A(σ, X)` denotes the endomorphism-valued one-form `A` evaluated on the
direction `X` and applied to `σ`, so that `(∇ + A)_X σ = ∇_X σ + A(σ, X)`. This file computes the
curvature of `∇ + A`:

`R^(∇ + A)(X, Y) σ = R^∇(X, Y) σ + ∇_X (A(σ, Y)) - ∇_Y (A(σ, X)) - A(σ, [X, Y])`
`    + A(∇_Y σ, X) - A(∇_X σ, Y) + A(A(σ, Y), X) - A(A(σ, X), Y)`.

The middle terms are the covariant exterior derivative of `A`. On the tangent bundle, for a
torsion-free `∇`, they assemble into the covariant derivative
`(∇_X A)(Z, Y) = ∇_X (A(Z, Y)) - A(∇_X Z, Y) - A(Z, ∇_X Y)` of `A` as a tensor:

`R^(∇ + A)(X, Y) Z = R^∇(X, Y) Z + (∇_X A)(Z, Y) - (∇_Y A)(Z, X)`
`    + A(A(Z, Y), X) - A(A(Z, X), Y)`.

This is the formula through which curvature transforms under a change of connection, for instance
under a conformal change of a Riemannian metric, where `∇` and `∇ + A` are the two Levi-Civita
connections. The identities hold at a point under differentiability hypotheses there only. The
general identity needs no smoothness, metric or finiteness assumption; the tangent-bundle form is
stated through Mathlib's torsion tensor, which is defined on finite-dimensional manifolds.

## Main results

* `CovariantDerivative.curvatureOperator_addOneForm`: the curvature of `∇ + A` on any vector
  bundle.
* `CovariantDerivative.curvatureOperator_addOneForm_of_torsion_eq_zero`: the curvature of
  `∇ + A` on the tangent bundle, for a torsion-free `∇`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 7
  (curvature and the curvature of conformally related metrics).
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.J.
-/

public section

open Bundle VectorField
open scoped Manifold

noncomputable section

namespace CovariantDerivative

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

section Bundle

variable
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul 𝕜 (V x)]
  [FiberBundle F V]

/-- **Curvature of a connection plus a one-form.** If `A` is a one-form with values in the
endomorphisms of `V`, then

`R^(∇ + A)(X, Y) σ = R^∇(X, Y) σ + (∇_X (A(σ, Y)) - ∇_Y (A(σ, X)) - A(σ, [X, Y]))`
`    + (A(∇_Y σ, X) - A(∇_X σ, Y)) + (A(A(σ, Y), X) - A(A(σ, X), Y))`,

where `A(σ, X) = A x (σ x) (X x)`. The hypotheses are the differentiability at the point of the
four sections differentiated by the outer covariant derivatives. -/
theorem curvatureOperator_addOneForm (cov : _root_.CovariantDerivative I F V)
    (A : Π x : M, V x →L[𝕜] TangentSpace I x →L[𝕜] V x)
    {X Y : Π x : M, TangentSpace I x} {σ : Π x : M, V x} {x : M}
    (hXσ : MDiffAt (T% (fun y ↦ cov σ y (X y))) x)
    (hYσ : MDiffAt (T% (fun y ↦ cov σ y (Y y))) x)
    (hAX : MDiffAt (T% (fun y ↦ A y (σ y) (X y))) x)
    (hAY : MDiffAt (T% (fun y ↦ A y (σ y) (Y y))) x) :
    curvatureOperator (cov.addOneForm A) X Y σ x =
      curvatureOperator cov X Y σ x +
        (cov (fun y ↦ A y (σ y) (Y y)) x (X x) - cov (fun y ↦ A y (σ y) (X y)) x (Y x) -
          A x (σ x) (mlieBracket I X Y x)) +
        (A x (cov σ x (Y x)) (X x) - A x (cov σ x (X x)) (Y x)) +
        (A x (A x (σ x) (Y x)) (X x) - A x (A x (σ x) (X x)) (Y x)) := by
  -- The inner covariant derivatives of `∇ + A` are sums of a `∇` term and an `A` term.
  have hinner (Z : Π x : M, TangentSpace I x) :
      (fun y ↦ cov.addOneForm A σ y (Z y)) =
        (fun y ↦ cov σ y (Z y)) + fun y ↦ A y (σ y) (Z y) :=
    (rfl)
  have happly (τ : Π x : M, V x) (v : TangentSpace I x) :
      cov.addOneForm A τ x v = cov τ x v + A x (τ x) v :=
    (rfl)
  rw [curvatureOperator_apply, curvatureOperator_apply, hinner X, hinner Y, happly, happly,
    happly, cov.isCovariantDerivativeOnUniv.add hYσ hAY,
    cov.isCovariantDerivativeOnUniv.add hXσ hAX]
  simp only [add_apply, Pi.add_apply, map_add]
  abel

end Bundle

section Tangent

variable [CompleteSpace 𝕜] [CompleteSpace E] [FiniteDimensional 𝕜 E] [IsManifold I 2 M]

/-- **Curvature of a torsion-free connection plus a one-form.** On the tangent bundle, if `∇` is
torsion free and `A` is a one-form with values in the endomorphisms of `TM`, then

`R^(∇ + A)(X, Y) Z = R^∇(X, Y) Z + (∇_X A)(Z, Y) - (∇_Y A)(Z, X)`
`    + A(A(Z, Y), X) - A(A(Z, X), Y)`,

where `A(Z, Y) = A x (Z x) (Y x)` and
`(∇_X A)(Z, Y) = ∇_X (A(Z, Y)) - A(∇_X Z, Y) - A(Z, ∇_X Y)` is the covariant derivative of `A`. -/
theorem curvatureOperator_addOneForm_of_torsion_eq_zero
    (cov : _root_.CovariantDerivative I E (TangentSpace I : M → Type _)) (hcov : cov.torsion = 0)
    (A : Π x : M, TangentSpace I x →L[𝕜] TangentSpace I x →L[𝕜] TangentSpace I x)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x)
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x)
    (hAX : MDiffAt (T% (fun y ↦ A y (Z y) (X y))) x)
    (hAY : MDiffAt (T% (fun y ↦ A y (Z y) (Y y))) x) :
    curvatureOperator (cov.addOneForm A) X Y Z x =
      curvatureOperator cov X Y Z x +
        (cov (fun y ↦ A y (Z y) (Y y)) x (X x) - A x (cov Z x (X x)) (Y x) -
          A x (Z x) (cov Y x (X x))) -
        (cov (fun y ↦ A y (Z y) (X y)) x (Y x) - A x (cov Z x (Y x)) (X x) -
          A x (Z x) (cov X x (Y x))) +
        (A x (A x (Z x) (Y x)) (X x) - A x (A x (Z x) (X x)) (Y x)) := by
  rw [curvatureOperator_addOneForm cov A hXZ hYZ hAX hAY,
    ← cov.torsion_eq_zero_iff.1 hcov hX hY, map_sub]
  abel

end Tangent

end CovariantDerivative
