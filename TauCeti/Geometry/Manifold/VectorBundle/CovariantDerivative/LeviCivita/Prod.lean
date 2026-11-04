/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Prod
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.WarpedProd

/-!
# The Levi-Civita connection of a product metric

Give `M × N` the product of Riemannian metrics on `M` and `N`. Its Levi-Civita connection
differentiates a product vector field `(Y₁, Y₂)` factor by factor:

`∇_(u, v) (Y₁, Y₂) = (∇_u Y₁, ∇_v Y₂)`.

This is the input for the curvature of a product, which is the product of the curvatures of the
factors (`TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Prod`).

On product fields the Koszul expression of the product metric splits as a sum over the factors,

`K((X₁, X₂), (Y₁, Y₂), (Z₁, Z₂))(x, y) = K(X₁, Y₁, Z₁)(x) + K(X₂, Y₂, Z₂)(y)`.

The product metric is the warped product with constant warping function `1`
(`TauCeti.Manifold.isWarpedProduct_one`), so these formulas are the case `f = 1` of the Koszul
expression and the Levi-Civita connection of a warped product, in which every term involving the
derivative of `f` vanishes.

## Main results

* `TauCeti.Manifold.koszul_prodVectorField`: the Koszul expression of the product metric on product
  fields.
* `TauCeti.Manifold.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField`: the Levi-Civita
  connection of the product metric on product fields, in any direction.
* `TauCeti.Manifold.leviCivitaConnection_prodVectorField`: the same along a product field, as an
  identity of product fields.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 5
  (the Koszul formula, Theorem 5.10).
* B. O'Neill, *Semi-Riemannian Geometry*, Academic Press (1983), Chapter 7 (the connection of a
  warped product, of which a product metric is the case of a constant warping function).
-/

public section

noncomputable section

open Bundle CovariantDerivative FiberBundle Manifold VectorField
open scoped ContDiff Manifold TauCeti

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 2 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsContMDiffRiemannianBundle J 1 F (fun y : N ↦ TangentSpace J y)]
  {X₁ Y₁ Z₁ : Π x : M, TangentSpace I x} {X₂ Y₂ Z₂ : Π y : N, TangentSpace J y} {p : M × N}

/-- On product fields, the Koszul expression of the product metric is the sum of the Koszul
expressions of the factors. -/
theorem koszul_prodVectorField (hX₁ : MDiffAt (T% X₁) p.1) (hY₁ : MDiffAt (T% Y₁) p.1)
    (hZ₁ : MDiffAt (T% Z₁) p.1) (hX₂ : MDiffAt (T% X₂) p.2) (hY₂ : MDiffAt (T% Y₂) p.2)
    (hZ₂ : MDiffAt (T% Z₂) p.2) :
    koszul (I.prod J) (prodVectorField X₁ X₂) (prodVectorField Y₁ Y₂) (prodVectorField Z₁ Z₂) p =
      koszul I X₁ Y₁ Z₁ p.1 + koszul J X₂ Y₂ Z₂ p.2 := by
  simpa [mvfderiv_const] using
    isWarpedProduct_one.koszul_prodVectorField mdifferentiableAt_const hX₁ hY₁ hZ₁ hX₂ hY₂ hZ₂

/-- **The Levi-Civita connection of a product metric** differentiates a product field factor by
factor: `∇_(u, v) (Y₁, Y₂) = (∇_u Y₁, ∇_v Y₂)`. -/
theorem tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField (hY₁ : MDiffAt (T% Y₁) p.1)
    (hY₂ : MDiffAt (T% Y₂) p.2) (v : TangentSpace (I.prod J) p) :
    tangentSpaceProdEquiv p (leviCivitaConnection (I.prod J) (M × N) (prodVectorField Y₁ Y₂) p v) =
      (leviCivitaConnection I M Y₁ p.1 (tangentSpaceProdEquiv p v).1,
        leviCivitaConnection J N Y₂ p.2 (tangentSpaceProdEquiv p v).2) := by
  simpa [mvfderiv_const] using
    isWarpedProduct_one.tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField
      mdifferentiableAt_const hY₁ hY₂ v

/-- The Levi-Civita connection of a product metric, differentiating a product field along another:
`∇_(X₁, X₂) (Y₁, Y₂) = (∇_X₁ Y₁, ∇_X₂ Y₂)`. -/
theorem leviCivitaConnection_prodVectorField (hY₁ : MDiffAt (T% Y₁) p.1)
    (hY₂ : MDiffAt (T% Y₂) p.2) :
    leviCivitaConnection (I.prod J) (M × N) (prodVectorField Y₁ Y₂) p (prodVectorField X₁ X₂ p) =
      prodVectorField (fun x ↦ leviCivitaConnection I M Y₁ x (X₁ x))
        (fun y ↦ leviCivitaConnection J N Y₂ y (X₂ y)) p := by
  apply (tangentSpaceProdEquiv p).injective
  rw [tangentSpaceProdEquiv_leviCivitaConnection_prodVectorField hY₁ hY₂,
    tangentSpaceProdEquiv_prodVectorField, tangentSpaceProdEquiv_prodVectorField]

end TauCeti.Manifold
