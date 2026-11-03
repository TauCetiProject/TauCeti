/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-!
# The second Bianchi identity

Let `∇` be a smooth connection on a vector bundle `V`, with curvature
`R(X, Y) = [∇_X, ∇_Y] - ∇_[X, Y]`, and let `∇ᵀ` be a smooth torsion-free connection on the
tangent bundle. The covariant derivative of the curvature along a vector field `X` is

`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇ᵀ_X Y, Z) σ - R(Y, ∇ᵀ_X Z) σ - R(Y, Z) (∇_X σ)`,

and the second (differential) Bianchi identity states that its cyclic sum over `X, Y, Z`
vanishes. For `V` the tangent bundle and `∇ = ∇ᵀ` this is the classical identity
`(∇_X R)(Y, Z) + (∇_Y R)(Z, X) + (∇_Z R)(X, Y) = 0`; for a general bundle it is the operator form
of `d_∇ R = 0`.

The proof first establishes the identity
`[∇_X, R(Y, Z)] + R(X, [Y, Z]) + (cyclic) = 0`, which holds for every smooth connection: the
third-order terms cancel by the Jacobi identity for commutators of operators, and the
remaining first-order terms by the Jacobi identity for the Lie bracket of vector fields.
Torsion-freeness of `∇ᵀ` then converts the bracket terms into the derivative terms of `∇R`.

## Main results

* `CovariantDerivative.curvatureOperator_commutator_cyclic_eq_zero`: the cyclic sum of
  `[∇_X, R(Y, Z)] σ + R(X, [Y, Z]) σ` vanishes, for any smooth connection.
* `CovariantDerivative.covariantDerivative_curvatureOperator_cyclic_eq_zero`: the second
  Bianchi identity, for a smooth connection on any vector bundle and a smooth torsion-free
  connection on the tangent bundle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, 2018,
  Chapter 7, Proposition 7.5 (the differential Bianchi identity).
-/

public section

open Bundle FiberBundle VectorField
open scoped ContDiff Manifold

namespace CovariantDerivative

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [∀ x, IsTopologicalAddGroup (V x)]
  [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : _root_.CovariantDerivative I F V) [ContMDiffCovariantDerivative cov ∞]
  {X Y Z : Π x : M, TangentSpace I x} {σ : Π x : M, V x}

/-- The cyclic sum of `[∇_X, R(Y, Z)] σ + R(X, [Y, Z]) σ` vanishes for every smooth connection.
This is the torsion-independent core of the second Bianchi identity
`covariantDerivative_curvatureOperator_cyclic_eq_zero`. -/
theorem curvatureOperator_commutator_cyclic_eq_zero
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hσ : CMDiff ∞ (T% σ)) (x : M) :
    (cov (curvatureOperator cov Y Z σ) x (X x) -
        curvatureOperator cov Y Z (fun y ↦ cov σ y (X y)) x +
          curvatureOperator cov X (mlieBracket I Y Z) σ x) +
      (cov (curvatureOperator cov Z X σ) x (Y x) -
        curvatureOperator cov Z X (fun y ↦ cov σ y (Y y)) x +
          curvatureOperator cov Y (mlieBracket I Z X) σ x) +
      (cov (curvatureOperator cov X Y σ) x (Z x) -
        curvatureOperator cov X Y (fun y ↦ cov σ y (Z y)) x +
          curvatureOperator cov Z (mlieBracket I X Y) σ x) = 0 := by
  let _ : IsManifold I (minSmoothness ℝ 3) M :=
    IsManifold.of_le (m := minSmoothness ℝ 3) (n := ∞) (by simp)
  have hsub {τ τ' : Π y : M, V y} (hτ : CMDiff ∞ (T% τ)) (hτ' : CMDiff ∞ (T% τ')) :
      cov (τ - τ') x = cov τ x - cov τ' x :=
    cov.isCovariantDerivativeOnUniv.sub (hτ.mdifferentiable (by simp) x)
      (hτ'.mdifferentiable (by simp) x)
  -- Expand the derivative of a curvature section into its three third-order terms.
  have hexp {A B C : Π y : M, TangentSpace I y}
      (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) :
      cov (curvatureOperator cov B C σ) x (A x) =
        cov (fun y ↦ cov (fun y ↦ cov σ y (C y)) y (B y)) x (A x) -
          cov (fun y ↦ cov (fun y ↦ cov σ y (B y)) y (C y)) x (A x) -
            cov (fun y ↦ cov σ y (mlieBracket I B C y)) x (A x) := by
    have hCσ := cov.contMDiff_apply hC hσ
    have hBσ := cov.contMDiff_apply hB hσ
    have hBC := cov.contMDiff_apply hB hCσ
    have hCB := cov.contMDiff_apply hC hBσ
    have hbrσ := cov.contMDiff_apply (contMDiff_mlieBracket hB hC) hσ
    have hR : curvatureOperator cov B C σ =
        (fun y ↦ cov (fun y ↦ cov σ y (C y)) y (B y)) -
          (fun y ↦ cov (fun y ↦ cov σ y (B y)) y (C y)) -
            fun y ↦ cov σ y (mlieBracket I B C y) := by
      funext y
      rw [curvatureOperator_apply, Pi.sub_apply, Pi.sub_apply]
    rw [hR, hsub (hBC.sub_section hCB) hbrσ, hsub hBC hCB]
    simp only [sub_apply]
  -- The cyclic Jacobi identity for the Lie bracket, seen through `∇σ`.
  have hjac : cov σ x (mlieBracket I X (mlieBracket I Y Z) x) +
      cov σ x (mlieBracket I Y (mlieBracket I Z X) x) +
        cov σ x (mlieBracket I Z (mlieBracket I X Y) x) = 0 := by
    rw [← map_add, ← map_add, jacobi_identity_mlieBracket_apply
      (hX.of_le (by simp)).contMDiffAt (hY.of_le (by simp)).contMDiffAt
      (hZ.of_le (by simp)).contMDiffAt, map_zero]
  rw [hexp hX hY hZ, hexp hY hZ hX, hexp hZ hX hY]
  simp only [curvatureOperator_apply]
  rw [← neg_eq_zero]
  convert hjac using 1
  abel

/-- **The second Bianchi identity.** Let `∇` be a smooth connection on a vector bundle and
`∇ᵀ` a smooth torsion-free connection on the tangent bundle. Writing
`(∇_X R)(Y, Z) σ = ∇_X (R(Y, Z) σ) - R(∇ᵀ_X Y, Z) σ - R(Y, ∇ᵀ_X Z) σ - R(Y, Z) (∇_X σ)`, the
cyclic sum `(∇_X R)(Y, Z) σ + (∇_Y R)(Z, X) σ + (∇_Z R)(X, Y) σ` vanishes. -/
theorem covariantDerivative_curvatureOperator_cyclic_eq_zero
    (covT : _root_.CovariantDerivative I E (TangentSpace I : M → Type _))
    [ContMDiffCovariantDerivative covT ∞] (ht : covT.IsTorsionFree)
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z))
    (hσ : CMDiff ∞ (T% σ)) (x : M) :
    (cov (curvatureOperator cov Y Z σ) x (X x) -
        curvatureOperator cov (fun y ↦ covT Y y (X y)) Z σ x -
          curvatureOperator cov Y (fun y ↦ covT Z y (X y)) σ x -
            curvatureOperator cov Y Z (fun y ↦ cov σ y (X y)) x) +
      (cov (curvatureOperator cov Z X σ) x (Y x) -
        curvatureOperator cov (fun y ↦ covT Z y (Y y)) X σ x -
          curvatureOperator cov Z (fun y ↦ covT X y (Y y)) σ x -
            curvatureOperator cov Z X (fun y ↦ cov σ y (Y y)) x) +
      (cov (curvatureOperator cov X Y σ) x (Z x) -
        curvatureOperator cov (fun y ↦ covT X y (Z y)) Y σ x -
          curvatureOperator cov X (fun y ↦ covT Y y (Z y)) σ x -
            curvatureOperator cov X Y (fun y ↦ cov σ y (Z y)) x) = 0 := by
  -- Torsion-freeness pairs the six derivative terms into the three bracket terms.
  have hpair {A B C : Π y : M, TangentSpace I y}
      (hA : CMDiff ∞ (T% A)) (hB : CMDiff ∞ (T% B)) :
      curvatureOperator cov (fun y ↦ covT B y (A y)) C σ x +
          curvatureOperator cov C (fun y ↦ covT A y (B y)) σ x =
        -curvatureOperator cov C (mlieBracket I A B) σ x := by
    have hAB := covT.contMDiff_apply hA hB
    have hBA := covT.contMDiff_apply hB hA
    have heq : mlieBracket I A B =
        (fun y ↦ covT B y (A y)) + -fun y ↦ covT A y (B y) := by
      funext y
      rw [Pi.add_apply, Pi.neg_apply, ← sub_eq_add_neg]
      exact ((isTorsionFree_iff covT).mp ht
        (hA.mdifferentiable (by simp) y) (hB.mdifferentiable (by simp) y)).symm
    rw [curvatureOperator_antisymm cov C (fun y ↦ covT A y (B y)),
      curvatureOperator_antisymm cov C (mlieBracket I A B), heq,
      curvatureOperator_add_first hAB hBA.neg_section hσ,
      curvatureOperator_neg_first hBA hσ]
    simp only [Pi.neg_apply, Pi.add_apply, neg_neg]
  have h := curvatureOperator_commutator_cyclic_eq_zero cov hX hY hZ hσ x
  have hXY := hpair (C := Z) hX hY
  have hYZ := hpair (C := X) hY hZ
  have hZX := hpair (C := Y) hZ hX
  linear_combination (norm := module) h - hXY - hYZ - hZX

end CovariantDerivative
