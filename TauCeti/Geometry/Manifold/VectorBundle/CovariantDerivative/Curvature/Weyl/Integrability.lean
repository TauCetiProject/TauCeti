/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Conformal
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Hessian
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The integrability obstruction of the conformal flattening equation

In dimension at least `3`, a metric `e^(2φ) g` has vanishing Schouten tensor exactly when `φ`
solves the *conformal flattening equation*

`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g`,

where `P` is the Schouten tensor of `g`
(`Bundle.ContMDiffRiemannianMetric.schoutenTensor_leviCivitaConnection_rescale_eq_zero_iff`).
This is a first-order system for the gradient `ξ = grad φ`: its right side
`Φ_ξ(u, v) = P(u, v) + ⟪ξ, u⟫ ⟪ξ, v⟫ - (‖ξ‖² / 2) ⟪u, v⟫` depends only on the point and the value
of `ξ` there (`CovariantDerivative.conformalFlatteningForm`). Differentiating `Φ_ξ` along a
solution, and substituting the equation for the derivative of `ξ`, gives the trilinear form

`D_ξ(u, v, w) = (∇_w P)(u, v) + Φ_ξ(w, u) ⟪ξ, v⟫ + ⟪ξ, u⟫ Φ_ξ(w, v) - Φ_ξ(w, ξ) ⟪u, v⟫`

(`CovariantDerivative.conformalFlatteningDeriv`), again a function of the point and of `ξ` alone.
For a solution `φ`, `D_(grad φ)` is the covariant derivative of `Hess φ`
(`TauCeti.Manifold.mvfderiv_hessian_sub_eq_conformalFlatteningDeriv`).

The Ricci identity says that `(∇_w Hess φ)(u, v) - (∇_v Hess φ)(u, w) = ⟪R(w, v) grad φ, u⟫`, so the
system can only be solved with prescribed value `ξ` at a point where
`D_ξ(u, v, w) - D_ξ(u, w, v) = ⟪R(w, v) ξ, u⟫`. The main computation of this file identifies the
defect in this identity for every vector `ξ`, solution or not:

`D_ξ(u, v, w) - D_ξ(u, w, v) - ⟪R(w, v) ξ, u⟫ = C(u, v, w) + W(w, v, u, ξ)`,

with `C` the Cotton tensor and `W` the Weyl tensor
(`CovariantDerivative.IsMetricCompatible.conformalFlatteningDeriv_sub_swap`). All terms quadratic
and cubic in `ξ` cancel, and the terms linear in `ξ` assemble into `P ⊙ g`, which turns the
curvature term into the Weyl tensor. Consequently the obstruction vanishes for every `ξ` at a point
where `W = 0` and `C = 0`; conversely, if the system has a solution through every value `ξ` at `x`,
then `C = 0` and `W = 0` at `x`. The first statement is the involutivity condition in the proof that
vanishing Weyl tensor (dimension at least `4`) or vanishing Cotton tensor (dimension `3`) implies
local conformal flatness.

## Main declarations

* `CovariantDerivative.conformalFlatteningForm`: the right side `Φ_ξ` of the conformal flattening
  equation.
* `CovariantDerivative.conformalFlatteningDeriv`: its derivative `D_ξ` along a solution.
* `CovariantDerivative.IsMetricCompatible.conformalFlatteningDeriv_sub_swap`:
  `D_ξ(u, v, w) - D_ξ(u, w, v) = ⟪R(w, v) ξ, u⟫ + C(u, v, w) + W(w, v, u, ξ)`.
* `TauCeti.Manifold.cottonTensor_add_weylTensor_eq_zero_of_eventually_hessian_eq`: along a solution
  `φ`, `C(u, v, w) + W(w, v, u, grad φ) = 0`.
* `TauCeti.Manifold.cottonTensor_eq_zero_of_eventually_hessian_eq` and
  `TauCeti.Manifold.weylTensor_eq_zero_of_forall_exists_eventually_hessian_eq`: solutions through
  every value of the gradient at a point force `C = 0` and `W = 0` there.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G (the Weyl–Schouten theorem).
-/

public section

open Bundle Filter LinearMap.BilinForm TauCeti.Manifold
open scoped ContDiff Manifold InnerProductSpace Topology

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

local notation "curvature" => cov.curvatureTensor (I := I) (M := M) (F := E)
  (V := TangentSpace I)

/-- The right side of the conformal flattening equation `Hess φ = Φ_(grad φ)`,
`Φ_ξ(u, v) = P(u, v) + ⟪ξ, u⟫ ⟪ξ, v⟫ - (‖ξ‖² / 2) ⟪u, v⟫`, where `P` is the Schouten tensor. -/
def conformalFlatteningForm (x : M) (ξ : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  cov.schoutenTensor x + (innerₗ _ ξ).smulRight (innerₗ _ ξ) - (‖ξ‖ ^ 2 / 2) • innerₗ _

/-- Evaluation of the right side of the conformal flattening equation. -/
@[simp]
theorem conformalFlatteningForm_apply (x : M) (ξ u v : TangentSpace I x) :
    cov.conformalFlatteningForm x ξ u v =
      cov.schoutenTensor x u v + ⟪ξ, u⟫_ℝ * ⟪ξ, v⟫_ℝ - ‖ξ‖ ^ 2 / 2 * ⟪u, v⟫_ℝ :=
  (rfl)

/-- The derivative of the right side `Φ_ξ` of the conformal flattening equation along a solution,
`D_ξ(u, v, w) = (∇_w P)(u, v) + Φ_ξ(w, u) ⟪ξ, v⟫ + ⟪ξ, u⟫ Φ_ξ(w, v) - Φ_ξ(w, ξ) ⟪u, v⟫`, with the
derivative direction `w` last as in `CovariantDerivative.derivSchoutenTensor`. -/
def conformalFlatteningDeriv (x : M) (ξ : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ (cov.derivSchoutenTensor x u v).toLinearMap +
      ⟪ξ, v⟫_ℝ • (cov.conformalFlatteningForm x ξ).flip u +
      ⟪ξ, u⟫_ℝ • (cov.conformalFlatteningForm x ξ).flip v -
      ⟪u, v⟫_ℝ • (cov.conformalFlatteningForm x ξ).flip ξ)
    (fun u u' v ↦ by
      ext w
      simp only [map_add, _root_.add_apply, ContinuousLinearMap.toLinearMap_add, inner_add_right,
        inner_add_left, LinearMap.sub_apply, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
        LinearMap.smul_apply, LinearMap.flip_apply, smul_eq_mul]
      ring)
    (fun c u v ↦ by
      ext w
      simp only [map_smul, _root_.smul_apply, ContinuousLinearMap.toLinearMap_smul,
        real_inner_smul_right, real_inner_smul_left, LinearMap.sub_apply, LinearMap.add_apply,
        LinearMap.smul_apply, ContinuousLinearMap.coe_coe, smul_eq_mul, LinearMap.flip_apply]
      ring)
    (fun u v v' ↦ by
      ext w
      simp only [map_add, ContinuousLinearMap.toLinearMap_add, inner_add_right,
        LinearMap.sub_apply, LinearMap.add_apply, ContinuousLinearMap.coe_coe, LinearMap.smul_apply,
        LinearMap.flip_apply, smul_eq_mul]
      ring)
    (fun c u v ↦ by
      ext w
      simp only [map_smul, ContinuousLinearMap.toLinearMap_smul, real_inner_smul_right,
        LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
        smul_eq_mul, LinearMap.flip_apply]
      ring)

/-- Evaluation of the derivative of the right side of the conformal flattening equation. -/
@[simp]
theorem conformalFlatteningDeriv_apply (x : M) (ξ u v w : TangentSpace I x) :
    cov.conformalFlatteningDeriv x ξ u v w =
      cov.derivSchoutenTensor x u v w + cov.conformalFlatteningForm x ξ w u * ⟪ξ, v⟫_ℝ +
        ⟪ξ, u⟫_ℝ * cov.conformalFlatteningForm x ξ w v -
        cov.conformalFlatteningForm x ξ w ξ * ⟪u, v⟫_ℝ := by
  simp only [conformalFlatteningDeriv, LinearMap.mk₂_apply, LinearMap.sub_apply,
    LinearMap.add_apply, LinearMap.smul_apply, LinearMap.flip_apply, ContinuousLinearMap.coe_coe,
    smul_eq_mul]
  ring

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] {cov}

/-- For a metric-compatible torsion-free connection, the right side of the conformal flattening
equation is symmetric. -/
theorem IsMetricCompatible.conformalFlatteningForm_isSymm
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (ξ : TangentSpace I x) :
    (cov.conformalFlatteningForm x ξ).IsSymm := by
  refine ⟨fun u v ↦ ?_⟩
  have hP := (IsMetricCompatible.schoutenTensor_isSymm (cov := cov) hcov ht x).eq u v
  simp only [RingHom.id_apply] at hP
  simp only [conformalFlatteningForm_apply, RingHom.id_apply, hP, real_inner_comm u v]
  ring

/-- **The integrability obstruction of the conformal flattening equation.** For a
metric-compatible torsion-free connection and every tangent vector `ξ`,
`D_ξ(u, v, w) - D_ξ(u, w, v) = ⟪R(w, v) ξ, u⟫ + (C(u, v, w) + W(w, v, u, ξ))`, where `D_ξ` is
`CovariantDerivative.conformalFlatteningDeriv`, `C` the Cotton tensor and `W` the Weyl tensor.

Along a solution of the equation the Ricci identity gives
`D_ξ(u, v, w) - D_ξ(u, w, v) = ⟪R(w, v) ξ, u⟫`, so `C(u, v, w) + W(w, v, u, ξ)` must vanish at `x`
for the equation to have a solution near `x` with gradient `ξ` at `x`. -/
theorem IsMetricCompatible.conformalFlatteningDeriv_sub_swap
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) (x : M) (ξ u v w : TangentSpace I x) :
    cov.conformalFlatteningDeriv x ξ u v w - cov.conformalFlatteningDeriv x ξ u w v =
      ⟪curvature x w v ξ, u⟫_ℝ + (cov.cottonTensor x u v w + cov.weylTensor x w v u ξ) := by
  have hP (a b : TangentSpace I x) : cov.schoutenTensor x a b = cov.schoutenTensor x b a := by
    simpa only [RingHom.id_apply] using
      (IsMetricCompatible.schoutenTensor_isSymm (cov := cov) hcov ht x).eq a b
  -- Move the curvature term into the Weyl tensor, `⟪R(w, v) ξ, u⟫ = -Rm(w, v, u, ξ)`.
  have hR := IsMetricCompatible.riemannCurvatureTensor_antisymm_last (cov := cov) hcov x w v ξ u
  simp only [riemannCurvatureTensor_apply] at hR
  rw [hR, weylTensor_apply, kulkarniNomizu_apply]
  simp only [conformalFlatteningDeriv_apply, conformalFlatteningForm_apply, cottonTensor_apply,
    innerₗ_apply_apply, riemannCurvatureTensor_apply, hP v w, real_inner_comm u ξ,
    real_inner_comm v ξ, real_inner_comm w ξ, real_inner_comm u v, real_inner_comm u w,
    real_inner_comm v w, real_inner_self_eq_norm_sq]
  ring

/-- At a point where the Weyl and Cotton tensors vanish, the integrability obstruction of the
conformal flattening equation vanishes for every value `ξ`:
`D_ξ(u, v, w) - D_ξ(u, w, v) = ⟪R(w, v) ξ, u⟫`. -/
theorem IsMetricCompatible.conformalFlatteningDeriv_sub_swap_eq_inner_curvatureTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := fun y : M ↦ TangentSpace I y) cov)
    (ht : cov.torsion = 0) {x : M} (hW : cov.weylTensor x = 0) (hC : cov.cottonTensor x = 0)
    (ξ u v w : TangentSpace I x) :
    cov.conformalFlatteningDeriv x ξ u v w - cov.conformalFlatteningDeriv x ξ u w v =
      ⟪curvature x w v ξ, u⟫_ℝ := by
  rw [IsMetricCompatible.conformalFlatteningDeriv_sub_swap hcov ht, hW, hC]
  simp

end CovariantDerivative

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **The conformal flattening equation.** In dimension at least `3`, the metric `f g` with
`f = e^(2φ)` has vanishing Schouten tensor at `x` exactly when
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` at `x`, where the Hessian, the gradient and the Schouten
tensor `P` are those of `g`. -/
theorem schoutenTensor_leviCivitaConnection_rescale_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (hn : 3 ≤ Module.finrank ℝ E) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).schoutenTensor x = 0) ↔
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∀ u v : TangentSpace I x, hessian I φ x u v =
      (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm x
        (mgradient I φ x) u v := by
  simp only [LinearMap.ext_iff₂, LinearMap.zero_apply,
    schoutenTensor_leviCivitaConnection_rescale g hf hf_pos hfφ hn x]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  simp only [CovariantDerivative.conformalFlatteningForm_apply, inner_mgradient]
  refine forall₂_congr fun u v ↦ ?_
  constructor <;> intro h <;> linarith

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- Along a solution `φ` of the conformal flattening equation `Hess φ = Φ_(grad φ)` near `x`, the
covariant derivative of the Hessian is `D_(grad φ)`:
`(∇_w Hess φ)(X, Y) = D_(grad φ)(X, Y, w)`, where
`(∇_w Hess φ)(X, Y) = w (Hess φ(X, Y)) - Hess φ(∇_w X, Y) - Hess φ(X, ∇_w Y)` and `D` is
`CovariantDerivative.conformalFlatteningDeriv` for the Levi-Civita connection. -/
theorem mvfderiv_hessian_sub_eq_conformalFlatteningDeriv {φ : M → ℝ} {x : M}
    (hφ : ContMDiffAt I 𝓘(ℝ) 2 φ x)
    (hsol : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y, hessian I φ y u v =
      (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
        (mgradient I φ y) u v)
    {X Y : Π x : M, TangentSpace I x} (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (w : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    mvfderiv I (fun y ↦ hessian I φ y (X y) (Y y)) x w -
        hessian I φ x (cov X x w) (Y x) - hessian I φ x (X x) (cov Y x w) =
      cov.conformalFlatteningDeriv x (mgradient I φ x) (X x) (Y x) w := by
  let _ : IsManifold I (1 + 1) M := by
    simpa only [one_add_one_eq_two] using (inferInstance : IsManifold I 2 M)
  have hcov := CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M)
  have hG : MDiffAt (T% (mgradient I φ)) x :=
    (contMDiffAt_mgradient (n := 1) (by simpa only [one_add_one_eq_two] using hφ)).mdifferentiableAt
      one_ne_zero
  have hGX := mdifferentiableAt_inner hG hX
  have hGY := mdifferentiableAt_inner hG hY
  have hGG := mdifferentiableAt_inner hG hG
  have hXY := mdifferentiableAt_inner hX hY
  have hPXY := (CovariantDerivative.leviCivitaConnection I M).mdifferentiableAt_schoutenTensor_apply
    hX hY
  -- Near `x`, replace the Hessian by the right side of the equation, written as a sum of products.
  have hfun : (fun y ↦ hessian I φ y (X y) (Y y)) =ᶠ[𝓝 x]
      (fun y ↦ (CovariantDerivative.leviCivitaConnection I M).schoutenTensor y (X y) (Y y)) +
        (fun y ↦ ⟪mgradient I φ y, X y⟫_ℝ) * (fun y ↦ ⟪mgradient I φ y, Y y⟫_ℝ) -
        ((fun y ↦ ⟪mgradient I φ y, mgradient I φ y⟫_ℝ) * fun _ ↦ (2 : ℝ)⁻¹) *
          fun y ↦ ⟪X y, Y y⟫_ℝ :=
    hsol.mono fun y hy ↦ by
      simp only [hy, CovariantDerivative.conformalFlatteningForm_apply, Pi.add_apply,
        Pi.sub_apply, Pi.mul_apply, real_inner_self_eq_norm_sq]
      ring
  -- At `x`, the Hessian, also in the form `⟪∇_a grad φ, b⟫`, is the right side of the equation.
  have hHx := hsol.self_of_nhds
  have hH (a b : TangentSpace I x) :
      ⟪CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x a, b⟫_ℝ =
        hessian I φ x a b :=
    (hessian_def I φ x a b).symm
  rw [hfun.mvfderiv_eq, mvfderiv_sub (hPXY.add (hGX.mul hGY))
      ((hGG.mul mdifferentiableAt_const).mul hXY), mvfderiv_add hPXY (hGX.mul hGY),
    mvfderiv_mul hGX hGY, mvfderiv_mul (hGG.mul mdifferentiableAt_const) hXY,
    mvfderiv_mul hGG mdifferentiableAt_const]
  simp only [mvfderiv_const, _root_.add_apply, _root_.sub_apply, _root_.smul_apply, smul_eq_mul,
    _root_.zero_apply, Pi.mul_apply]
  rw [hcov.mvfderiv_inner_eq (fun _ ↦ w) hG hX, hcov.mvfderiv_inner_eq (fun _ ↦ w) hG hY,
    hcov.mvfderiv_inner_eq (fun _ ↦ w) hG hG, hcov.mvfderiv_inner_eq (fun _ ↦ w) hX hY,
    CovariantDerivative.conformalFlatteningDeriv_apply,
    (CovariantDerivative.leviCivitaConnection I M).derivSchoutenTensor_apply hX hY w]
  simp only [real_inner_comm (CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x w),
    real_inner_comm (mgradient I φ x) w, hH, hHx,
    CovariantDerivative.conformalFlatteningForm_apply, real_inner_self_eq_norm_sq]
  ring

/-- **The integrability condition of the conformal flattening equation.** If a smooth `φ` solves
`Hess φ = P + dφ ⊗ dφ - (|dφ|² / 2) g` near `x`, then the Cotton and Weyl tensors of the
Levi-Civita connection satisfy `C(u, v, w) + W(w, v, u, grad φ) = 0` at `x`. -/
theorem cottonTensor_add_weylTensor_eq_zero_of_eventually_hessian_eq {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {x : M}
    (hsol : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y, hessian I φ y u v =
      (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
        (mgradient I φ y) u v)
    (u v w : TangentSpace I x) :
    letI cov := CovariantDerivative.leviCivitaConnection I M
    cov.cottonTensor x u v w + cov.weylTensor x w v u (mgradient I φ x) = 0 := by
  set cov := CovariantDerivative.leviCivitaConnection I M
  obtain ⟨X, hX, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  obtain ⟨Z, hZ, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  have hXx : MDiffAt (T% X) x := hX.mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := hY.mdifferentiableAt (by simp)
  have hZx : MDiffAt (T% Z) x := hZ.mdifferentiableAt (by simp)
  -- The Ricci identity for `Hess φ`, with both covariant derivatives computed from the equation.
  have hRicci := mvfderiv_hessian_sub_swap hφ hX hY hZ x
  have hφx : ContMDiffAt I 𝓘(ℝ) 2 φ x := hφ.contMDiffAt.of_le (by simp)
  have hYZ := mvfderiv_hessian_sub_eq_conformalFlatteningDeriv hφx hsol hXx hYx (Z x)
  have hZY := mvfderiv_hessian_sub_eq_conformalFlatteningDeriv hφx hsol hXx hZx (Y x)
  have hobs := CovariantDerivative.IsMetricCompatible.conformalFlatteningDeriv_sub_swap
    (CovariantDerivative.isMetricCompatible_leviCivitaConnection (I := I) (M := M))
    (CovariantDerivative.torsion_leviCivitaConnection_eq_zero I) x (mgradient I φ x)
    (X x) (Y x) (Z x)
  linarith

/-- If the conformal flattening equation has a smooth solution near `x` whose gradient vanishes at
`x`, then the Cotton tensor of the Levi-Civita connection vanishes at `x`. -/
theorem cottonTensor_eq_zero_of_eventually_hessian_eq {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {x : M} (hx : mgradient I φ x = 0)
    (hsol : ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y, hessian I φ y u v =
      (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
        (mgradient I φ y) u v) :
    (CovariantDerivative.leviCivitaConnection I M).cottonTensor x = 0 := by
  ext u v w
  simpa [hx] using cottonTensor_add_weylTensor_eq_zero_of_eventually_hessian_eq hφ hsol u v w

/-- If the conformal flattening equation has a smooth solution near `x` through every value
`grad φ x = ξ` of the gradient at `x`, then the Weyl tensor of the Levi-Civita connection vanishes
at `x`. -/
theorem weylTensor_eq_zero_of_forall_exists_eventually_hessian_eq {x : M}
    (hsol : ∀ ξ : TangentSpace I x, ∃ φ : M → ℝ, ContMDiff I 𝓘(ℝ) ∞ φ ∧ mgradient I φ x = ξ ∧
      ∀ᶠ y in 𝓝 x, ∀ u v : TangentSpace I y, hessian I φ y u v =
        (CovariantDerivative.leviCivitaConnection I M).conformalFlatteningForm y
          (mgradient I φ y) u v) :
    (CovariantDerivative.leviCivitaConnection I M).weylTensor x = 0 := by
  obtain ⟨φ₀, hφ₀, hx₀, hsol₀⟩ := hsol 0
  have hC := cottonTensor_eq_zero_of_eventually_hessian_eq hφ₀ hx₀ hsol₀
  ext w v u ξ
  obtain ⟨φ, hφ, rfl, hsolφ⟩ := hsol ξ
  simpa [hC] using cottonTensor_add_weylTensor_eq_zero_of_eventually_hessian_eq hφ hsolφ u v w

end TauCeti.Manifold
