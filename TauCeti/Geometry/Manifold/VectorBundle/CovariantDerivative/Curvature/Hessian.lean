/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.SecondCovariantDerivative
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

/-!
# The Ricci identity for the Hessian

For a smooth function `φ` on a Riemannian manifold, the Hessian `Hess φ(u, v) = ⟪∇_u grad φ, v⟫`
(`TauCeti.Manifold.hessian`) is symmetric, but its covariant derivative is not: the third
covariant derivative of `φ` commutes in its last two slots only up to curvature. With

`(∇_Z Hess φ)(X, Y) = Z (Hess φ(X, Y)) - Hess φ(∇_Z X, Y) - Hess φ(X, ∇_Z Y)`

and the curvature convention `R(u, v) w = ∇_u ∇_v w - ∇_v ∇_u w - ∇_[u,v] w`, the identity is

`(∇_Z Hess φ)(X, Y) - (∇_Y Hess φ)(X, Z) = ⟪R(Z, Y) grad φ, X⟫`.

It is the Ricci identity `∇²σ(u, v) - ∇²σ(v, u) = R(u, v) σ`
(`CovariantDerivative.secondCovariantDerivative_sub_swap_of_isTorsionFree`) for `σ = grad φ`,
transported to the Hessian by metric compatibility and the symmetry of `Hess φ`. It is the
commutation rule for third derivatives of functions used in the conformal transformation law of
the Cotton tensor and in Bochner-type formulas.

The identity is stated on smooth vector fields, since the covariant derivative of the Hessian is
evaluated through them.

## Main results

* `TauCeti.Manifold.mvfderiv_hessian_sub_swap`: the Ricci identity for the Hessian.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the Ricci identities).
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The Ricci identity for the Hessian.** For a smooth function `φ` and smooth vector fields
`X`, `Y`, `Z`, the covariant derivative of `Hess φ` is symmetric in its last two slots up to
curvature: `(∇_Z Hess φ)(X, Y) - (∇_Y Hess φ)(X, Z) = ⟪R(Z, Y) grad φ, X⟫`, where
`(∇_Z Hess φ)(X, Y) = Z (Hess φ(X, Y)) - Hess φ(∇_Z X, Y) - Hess φ(X, ∇_Z Y)` and `∇` is the
Levi-Civita connection. -/
theorem mvfderiv_hessian_sub_swap {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    mvfderiv I (fun y ↦ hessian I φ y (X y) (Y y)) x (Z x) -
        mvfderiv I (fun y ↦ hessian I φ y (X y) (Z y)) x (Y x) -
        hessian I φ x (cov X x (Z x)) (Y x) - hessian I φ x (X x) (cov Y x (Z x)) +
        hessian I φ x (cov X x (Y x)) (Z x) + hessian I φ x (X x) (cov Z x (Y x)) =
      inner ℝ (cov.curvatureTensor x (Z x) (Y x) (mgradient I φ x)) (X x) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hG : CMDiff ∞ (T% (mgradient I φ)) := contMDiff_mgradient hφ
  have hφ2 : ContMDiff I 𝓘(ℝ) 2 φ := hφ.of_le (by simp)
  -- By symmetry of the Hessian, `Hess φ(a, b) = ⟪∇_b grad φ, a⟫`.
  have hsym (y : M) (a b : TangentSpace I y) :
      hessian I φ y a b = inner ℝ (cov (mgradient I φ) y b) a := by
    rw [hessian_symm y hφ2.contMDiffAt, hessian_def]
  have hfun (W : Π x : M, TangentSpace I x) : (fun y ↦ hessian I φ y (X y) (W y)) =
      fun y ↦ inner ℝ (cov (mgradient I φ) y (W y)) (X y) := funext fun y ↦ hsym y _ _
  have hcovG {W : Π x : M, TangentSpace I x} (hW : CMDiff ∞ (T% W)) :
      MDiffAt (T% (fun y ↦ cov (mgradient I φ) y (W y))) x :=
    (cov.contMDiff_apply hW hG).mdifferentiableAt (by simp)
  have hXx : MDiffAt (T% X) x := hX.mdifferentiableAt (by simp)
  -- Differentiate `⟪∇_Y grad φ, X⟫` and `⟪∇_Z grad φ, X⟫` by metric compatibility.
  have hZY := (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
    Z (hcovG hY) hXx
  have hYZ := (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
    Y (hcovG hZ) hXx
  -- The remaining second derivatives of `grad φ` combine into the Ricci identity.
  have hR := cov.secondCovariantDerivative_sub_swap_of_isTorsionFree cov
    ((CovariantDerivative.isTorsionFree_iff_torsion_eq_zero cov).2
      (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I)) hG x (Z x) (Y x)
  rw [cov.secondCovariantDerivative_apply cov hG x hY,
    cov.secondCovariantDerivative_apply cov hG x hZ] at hR
  rw [← hR, hfun, hfun, hZY, hYZ]
  simp only [hsym, inner_sub_left]
  simp only [cov]
  ring

end TauCeti.Manifold
