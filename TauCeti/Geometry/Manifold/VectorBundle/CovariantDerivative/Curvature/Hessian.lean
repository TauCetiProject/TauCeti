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
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

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

The module also records two Hessian identities used in the Bochner formula. Metric compatibility
gives `Hess |σ|²(u, v) = 2 ⟪∇²σ(u, v), σ⟫ + 2 ⟪∇_u σ, ∇_v σ⟫` for every smooth section `σ` of a
Riemannian vector bundle with a metric connection `∇`, where `∇²σ(u, v) = ∇_u ∇_W σ - ∇_{∇_u W} σ`
is the second covariant derivative; the case of a vector field is the one used by Bochner. Pairing
`∇²(grad φ)(u, v)` with `w` gives `(∇_u Hess φ)(v, w)`, so since `Hess φ` is symmetric, the
third covariant derivative of `φ` is symmetric in its last two slots.

## Main results

* `TauCeti.Manifold.mvfderiv_hessian_sub_swap`: the Ricci identity for the Hessian.
* `CovariantDerivative.IsMetricCompatible.hessian_norm_sq`: the Hessian of the squared length of
  a smooth section of a Riemannian vector bundle with a metric connection.
* `TauCeti.Manifold.inner_secondCovariantDerivative_mgradient_eq_mvfderiv_hessian`: pairing the
  second covariant derivative of `grad φ` with a vector field is the covariant derivative of the
  Hessian.
* `TauCeti.Manifold.inner_secondCovariantDerivative_mgradient_comm`: the third covariant
  derivative of a smooth function is symmetric in its last two slots.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (the Ricci identities).
-/

public section

open Bundle
open scoped ContDiff InnerProductSpace Manifold

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

namespace CovariantDerivative.IsMetricCompatible

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]
  {cov : _root_.CovariantDerivative I F V} [ContMDiffCovariantDerivative cov ∞]

/-- **The Hessian of the squared length of a section.** For a metric connection `∇` on a
Riemannian vector bundle and a smooth section `σ`,
`Hess |σ|²(u, v) = 2 ⟪∇²σ(u, v), σ⟫ + 2 ⟪∇_u σ, ∇_v σ⟫`, where
`∇²σ(u, v) = ∇_u ∇_W σ - ∇_{∇_u W} σ`, for any smooth vector field `W` with `W x = v`, is the
second covariant derivative of `σ` built with the Levi-Civita connection on the tangent bundle. -/
theorem hessian_norm_sq (hcov : cov.IsMetricCompatible) {σ : Π x : M, V x}
    (hσ : CMDiff ∞ (T% σ)) (x : M) (u v : TangentSpace I x) :
    TauCeti.Manifold.hessian I (fun y ↦ ‖σ y‖ ^ 2) x u v =
      2 * ⟪cov.secondCovariantDerivative (leviCivitaConnection I M) σ x u v, σ x⟫_ℝ +
        2 * ⟪cov σ x u, cov σ x v⟫_ℝ := by
  set covT := leviCivitaConnection I M
  have hσ1 : CMDiff (∞ + 1) (T% σ) := by simpa using hσ
  have hfun : (fun y ↦ ‖σ y‖ ^ 2) = fun y ↦ ⟪σ y, σ y⟫_ℝ :=
    funext fun y ↦ (real_inner_self_eq_norm_sq (σ y)).symm
  -- The directional derivative of `|σ|²` is `⟨∇_w σ, σ⟩ + ⟨σ, ∇_w σ⟩`.
  have hd (w : TangentSpace I x) :
      mvfderiv I (fun y ↦ ⟪σ y, σ y⟫_ℝ) x w = ⟪cov σ x w, σ x⟫_ℝ + ⟪σ x, cov σ x w⟫_ℝ := by
    have hσd : MDiffAt (T% σ) x := hσ.mdifferentiable (by simp) x
    simpa using hcov.mvfderiv_inner_eq (FiberBundle.extend E w) hσd hσd
  obtain ⟨U, _, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ u
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  have hsq : ContMDiffAt I 𝓘(ℝ) 2 (fun y ↦ ‖σ y‖ ^ 2) x := by
    rw [hfun]
    exact ((hσ.inner_bundle hσ).of_le (by simp)).contMDiffAt
  rw [TauCeti.Manifold.hessian_apply_eq_mvfderiv_sub x hsq U W (hW.mdifferentiableAt (by simp)),
    hfun, hcov.mvfderiv_mvfderiv_inner (n := ∞) (by simp) hW hσ1 hσ1 x, hd,
    cov.secondCovariantDerivative_apply covT hσ x hW]
  simp only [covT, inner_sub_right, real_inner_comm (σ x), real_inner_comm (cov σ x (U x))]
  ring

end CovariantDerivative.IsMetricCompatible

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Pairing the second covariant derivative of `grad φ` with a vector field is the covariant
derivative of the Hessian: for smooth vector fields `V` and `W`,
`⟪∇²(grad φ)(u, V), W⟫ = u (Hess φ(V, W)) - Hess φ(∇_u V, W) - Hess φ(V, ∇_u W)`, where `∇` is the
Levi-Civita connection. -/
theorem inner_secondCovariantDerivative_mgradient_eq_mvfderiv_hessian {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {V W : Π x : M, TangentSpace I x} (hV : CMDiff ∞ (T% V))
    {x : M} (hW : MDiffAt (T% W) x) (u : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.secondCovariantDerivative cov (mgradient I φ) x u (V x), W x⟫_ℝ =
      mvfderiv I (fun y ↦ hessian I φ y (V y) (W y)) x u - hessian I φ x (cov V x u) (W x) -
        hessian I φ x (V x) (cov W x u) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  set cov := CovariantDerivative.leviCivitaConnection I M
  have hG : CMDiff ∞ (T% (mgradient I φ)) := contMDiff_mgradient hφ
  have hGV : MDiffAt (T% (fun y ↦ cov (mgradient I φ) y (V y))) x :=
    (cov.contMDiff_apply hV hG).mdifferentiable (by simp) x
  have hd := (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
    (FiberBundle.extend E u) hGV hW
  simp only [FiberBundle.extend_apply_self] at hd
  simp only [hessian_def]
  rw [hd, cov.secondCovariantDerivative_apply cov hG x hV]
  simp only [cov, inner_sub_left]
  ring

/-- The third covariant derivative of a smooth function is symmetric in its last two slots:
`⟪∇²(grad φ)(u, v), w⟫ = ⟪∇²(grad φ)(u, w), v⟫`, since it is the covariant derivative of the
symmetric Hessian. -/
theorem inner_secondCovariantDerivative_mgradient_comm {φ : M → ℝ} (hφ : ContMDiff I 𝓘(ℝ) ∞ φ)
    (x : M) (u v w : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    ⟪cov.secondCovariantDerivative cov (mgradient I φ) x u v, w⟫_ℝ =
      ⟪cov.secondCovariantDerivative cov (mgradient I φ) x u w, v⟫_ℝ := by
  have hφ2 : ContMDiffAt I 𝓘(ℝ) 2 φ x := (hφ.of_le (by simp)).contMDiffAt
  obtain ⟨V, hV, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ v
  obtain ⟨W, hW, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E ∞ w
  have hpair : (fun y ↦ hessian I φ y (V y) (W y)) = fun y ↦ hessian I φ y (W y) (V y) :=
    funext fun y ↦ hessian_symm y (hφ.of_le (by simp)).contMDiffAt _ _
  rw [inner_secondCovariantDerivative_mgradient_eq_mvfderiv_hessian hφ hV
      (hW.mdifferentiableAt (by simp)),
    inner_secondCovariantDerivative_mgradient_eq_mvfderiv_hessian hφ hW
      (hV.mdifferentiableAt (by simp)), hpair,
    hessian_symm x hφ2 (CovariantDerivative.leviCivitaConnection I M V x u),
    hessian_symm x hφ2 (V x)]
  ring

end TauCeti.Manifold
