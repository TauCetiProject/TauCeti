/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AddOneForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Conformal
import TauCeti.Analysis.InnerProductSpace.KulkarniNomizu
import TauCeti.Geometry.Manifold.Riemannian.Scaling
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# Curvature under a conformal change of metric

Let `g` be a Riemannian metric on `M` and `f` a positive function, and let `ĝ = f g` be the
conformally rescaled metric `Bundle.ContMDiffRiemannianMetric.rescale`. The Levi-Civita
connections of the two metrics differ by the conformal connection tensor
`A(Y, X) = (2 f)⁻¹ (df(X) Y + df(Y) X - g(X, Y) grad_g f)`
(`TauCeti.Manifold.conformalConnectionTensor`), and this file computes the curvature of `ĝ`
from that of `g`:

`R^ĝ(X, Y) Z = R^g(X, Y) Z + (∇_X A)(Z, Y) - (∇_Y A)(Z, X) + A(A(Z, Y), X) - A(A(Z, X), Y)`,

where `∇` is the Levi-Civita connection of `g` and
`(∇_X A)(Z, Y) = ∇_X (A(Z, Y)) - A(∇_X Z, Y) - A(Z, ∇_X Y)`. Writing `f = e^(2φ)`, the tensor
is `A(Y, X) = dφ(X) Y + dφ(Y) X - g(X, Y) grad_g φ`, and this is the classical transformation law
of the Riemann curvature under the conformal change `e^(2φ) g`. It is the input from which the
Ricci and scalar curvatures of `ĝ`, and hence the conformal Laplacian of the Yamabe problem, are
computed.

The identity holds at a point `x` for a `Cⁿ` metric with `1 ≤ n`, and with the Levi-Civita
connection of `g` replaced by any connection that is Levi-Civita for `g`. The conformal factor `f`
is assumed `Cⁿ` on all of `M` and the vector field `Z` differentiable on all of `M`; the remaining
hypotheses are differentiability at `x` of `X`, `Y`, `∇_X Z`, `∇_Y Z`, `A(Z, X)` and `A(Z, Y)`.
For a smooth metric, a smooth conformal factor and smooth vector fields all the hypotheses hold.

For the conformal factor `f = e^(2u)` of a smooth function `u`, the derivative of `A` is computed
from the Hessian of `u`, `(∇_X A)(Z, Y) = Hess u(X, Y) Z + Hess u(X, Z) Y - g(Y, Z) ∇_X grad u`
(`TauCeti.Manifold.leviCivitaConnection_conformalConnectionTensor_exp_two_mul`).
This turns the identity above into an algebraic expression in the curvature of `g` and the first
two derivatives of `u` at the point. With `T = Hess u - du ⊗ du` and `T♯(X) = ∇_X grad u -
du(X) grad u`,

`R^ĝ(X, Y) Z = R^g(X, Y) Z + T(X, Z) Y - T(Y, Z) X - g(Y, Z) T♯(X) + g(X, Z) T♯(Y)
  + |du|² (g(X, Z) Y - g(Y, Z) X)`.

Taking traces in a `g`-orthonormal basis gives, in dimension `n`, with `Δ = div grad` the
Laplace–Beltrami operator of `g` (so that `Δ⁺ = -Δ` is the nonnegative Laplacian),

`Ric^ĝ = Ric^g - (n - 2) (Hess u - du ⊗ du) - (Δu + (n - 2) |du|²) g`,
`Scal^ĝ = e^(-2u) (Scal^g - 2 (n - 1) Δu - (n - 1) (n - 2) |du|²)`.

These are the transformation laws of Ricci and scalar curvature under a conformal change of metric
from which the conformal Laplacian of the Yamabe problem arises.

As for the conformal change of the Levi-Civita connection
(`Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_apply`), connections do not depend
on a metric, so each metric is installed in turn as the `RiemannianBundle` instance of the tangent
bundle of `M` and the connections are compared directly on `M`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale`: the curvature
  of `f g` in terms of a Levi-Civita connection of `g` and the conformal connection tensor of `f`.
* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale_of_contMDiff`:
  the same identity for a smooth metric, a smooth conformal factor and smooth vector fields.
* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale_exp` and
  `Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale_exp`: the curvature
  of `e^(2u) g` in terms of the curvature of `g` and the derivatives of `u`.
* `Bundle.ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_rescale_exp`: the Ricci tensor
  of `e^(2u) g`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_exp`: the scalar curvature of
  `e^(2u) g`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.J.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (curvature of conformally related metrics, Theorem 7.30).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Curvature under conformal change.** Let `∇` be a Levi-Civita connection of a `C¹` metric `g`
and `A` the conformal connection tensor of a positive function `f`. Then the curvature of the
Levi-Civita connection of `f g` is

`R^(f g)(X, Y) Z = R^∇(X, Y) Z + (∇_X A)(Z, Y) - (∇_Y A)(Z, X) + A(A(Z, Y), X) - A(A(Z, X), Y)`,

with `(∇_X A)(Z, Y) = ∇_X (A(Z, Y)) - A(∇_X Z, Y) - A(Z, ∇_X Y)`. The metric `g` and the
function `f` are assumed `Cⁿ` on all of `M` for some `1 ≤ n`, and `Z` differentiable on all of `M`;
the remaining hypotheses are differentiability at `x` of `X`, `Y`, `∇_X Z`, `∇_Y Z`, `A(Z, X)` and
`A(Z, Y)`. -/
theorem curvatureOperator_leviCivitaConnection_rescale [IsManifold I 2 M] {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hcov : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      cov.IsLeviCivitaConnection)
    {X Y Z : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) (hZ : MDiff (T% Z))
    (hXZ : MDiffAt (T% (fun y ↦ cov Z y (X y))) x)
    (hYZ : MDiffAt (T% (fun y ↦ cov Z y (Y y))) x)
    (hAX : MDiffAt (T% (fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalConnectionTensor I f y (Z y) (X y)))) x)
    (hAY : MDiffAt (T% (fun y ↦
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        conformalConnectionTensor I f y (Z y) (Y y)))) x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      (CovariantDerivative.leviCivitaConnection I M).curvatureOperator X Y Z x) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    cov.curvatureOperator X Y Z x +
      (cov (fun y ↦ conformalConnectionTensor I f y (Z y) (Y y)) x (X x) -
          conformalConnectionTensor I f x (cov Z x (X x)) (Y x) -
          conformalConnectionTensor I f x (Z x) (cov Y x (X x))) -
      (cov (fun y ↦ conformalConnectionTensor I f y (Z y) (X y)) x (Y x) -
          conformalConnectionTensor I f x (cov Z x (Y x)) (X x) -
          conformalConnectionTensor I f x (Z x) (cov X x (Y x))) +
      (conformalConnectionTensor I f x (conformalConnectionTensor I f x (Z x) (Y x)) (X x) -
        conformalConnectionTensor I f x (conformalConnectionTensor I f x (Z x) (X x)) (Y x)) := by
  have ht : cov.torsion = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact hcov.torsion
  have hA := isLeviCivitaConnection_rescale_addOneForm g hn hf hf_pos hcov
  set A := (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
    conformalConnectionTensor I f)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  -- The Levi-Civita connection of `f g` agrees with `∇ + A` on differentiable vector fields.
  have hcongr : ∀ ⦃σ : Π x : M, TangentSpace I x⦄ ⦃y : M⦄, MDiffAt (T% σ) y →
      CovariantDerivative.leviCivitaConnection I M σ y = cov.addOneForm A σ y :=
    fun σ y hσ ↦ ContinuousLinearMap.ext fun v ↦
      (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).uniqueness I hA hσ v
  rw [CovariantDerivative.curvatureOperator_congr_covariantDerivative _ hcongr hZ
      (mdifferentiableAt_add_section hXZ hAX) (mdifferentiableAt_add_section hYZ hAY),
    CovariantDerivative.curvatureOperator_addOneForm_of_torsion_eq_zero cov ht A hX hY hXZ hYZ
      hAX hAY]

/-- **Curvature under conformal change**, for a smooth metric `g`, a smooth positive function `f`
and smooth vector fields. With `∇` the Levi-Civita connection of `g` and `A` the conformal
connection tensor of `f`, the curvature of the Levi-Civita connection of `f g` is

`R^(f g)(X, Y) Z = R^g(X, Y) Z + (∇_X A)(Z, Y) - (∇_Y A)(Z, X) + A(A(Z, Y), X) - A(A(Z, X), Y)`,

with `(∇_X A)(Z, Y) = ∇_X (A(Z, Y)) - A(∇_X Z, Y) - A(Z, ∇_X Y)`. -/
theorem curvatureOperator_leviCivitaConnection_rescale_of_contMDiff [IsManifold I ∞ M]
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
    {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureOperator X Y Z x) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI cov := CovariantDerivative.leviCivitaConnection I M
    cov.curvatureOperator X Y Z x +
      (cov (fun y ↦ conformalConnectionTensor I f y (Z y) (Y y)) x (X x) -
          conformalConnectionTensor I f x (cov Z x (X x)) (Y x) -
          conformalConnectionTensor I f x (Z x) (cov Y x (X x))) -
      (cov (fun y ↦ conformalConnectionTensor I f y (Z y) (X y)) x (Y x) -
          conformalConnectionTensor I f x (cov Z x (Y x)) (X x) -
          conformalConnectionTensor I f x (Z x) (cov X x (Y x))) +
      (conformalConnectionTensor I f x (conformalConnectionTensor I f x (Z x) (Y x)) (X x) -
        conformalConnectionTensor I f x (conformalConnectionTensor I f x (Z x) (X x)) (Y x)) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsManifold I ((∞ : ℕ∞ω) + 1) M :=
    IsManifold.of_le (m := (∞ : ℕ∞ω) + 1) (n := ∞) (by simp)
  have hA {V W : Π x : M, TangentSpace I x} (hV : CMDiff ∞ (T% V)) (hW : CMDiff ∞ (T% W)) :
      MDiffAt (T% (fun y ↦ conformalConnectionTensor I f y (V y) (W y))) x :=
    (contMDiff_conformalConnectionTensor_apply (n := ∞) hf (fun y ↦ (hf_pos y).ne') hV
      hW).mdifferentiableAt (by simp)
  have hcov {V : Π x : M, TangentSpace I x} (hV : CMDiff ∞ (T% V)) :
      MDiffAt (T% (fun y ↦ CovariantDerivative.leviCivitaConnection I M Z y (V y))) x :=
    ((CovariantDerivative.leviCivitaConnection I M).contMDiff_apply hV hZ).mdifferentiableAt
      (by simp)
  exact curvatureOperator_leviCivitaConnection_rescale g (by simp) hf hf_pos
    (CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
    (hX.mdifferentiableAt (by simp)) (hY.mdifferentiableAt (by simp))
    (hZ.mdifferentiable (by simp)) (hcov hX) (hcov hY) (hA hZ hX) (hA hZ hY)

section Exp

open TauCeti.Manifold

variable [IsManifold I ∞ M]

/-- **Curvature under the conformal change `e^(2u) g`.** For a smooth metric `g`, a smooth function
`u` and smooth vector fields, with `∇` the Levi-Civita connection of `g`,
`T(X, Z) = Hess u(X, Z) - du(X) du(Z)` and `T♯(X) = ∇_X grad u - du(X) grad u`,

`R^(e^(2u) g)(X, Y) Z = R^g(X, Y) Z + T(X, Z) Y - T(Y, Z) X - g(Y, Z) T♯(X) + g(X, Z) T♯(Y)
  + |du|² (g(X, Z) Y - g(Y, Z) X)`. -/
theorem curvatureOperator_leviCivitaConnection_rescale_exp
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) {X Y Z : Π x : M, TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun y ↦ Real.exp (2 * u y))
          (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hu))
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureOperator X Y Z x) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI cov := CovariantDerivative.leviCivitaConnection I M
    cov.curvatureOperator X Y Z x +
      (hessian I u x (X x) (Z x) - mvfderiv I u x (X x) * mvfderiv I u x (Z x)) • Y x -
      (hessian I u x (Y x) (Z x) - mvfderiv I u x (Y x) * mvfderiv I u x (Z x)) • X x -
      ⟪Y x, Z x⟫ • (cov (mgradient I u) x (X x) - mvfderiv I u x (X x) • mgradient I u x) +
      ⟪X x, Z x⟫ • (cov (mgradient I u) x (Y x) - mvfderiv I u x (Y x) • mgradient I u x) +
      ⟪mgradient I u x, mgradient I u x⟫ • (⟪X x, Z x⟫ • Y x - ⟪Y x, Z x⟫ • X x) := by
  rw [curvatureOperator_leviCivitaConnection_rescale_of_contMDiff g _ _ hX hY hZ x]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hu' : MDiffAt u x := hu.mdifferentiableAt (by simp)
  rw [leviCivitaConnection_conformalConnectionTensor_exp_two_mul hu X
      (hY.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp)),
    leviCivitaConnection_conformalConnectionTensor_exp_two_mul hu Y
      (hX.mdifferentiableAt (by simp)) (hZ.mdifferentiableAt (by simp))]
  simp only [conformalConnectionTensor_exp_two_mul hu']
  rw [hessian_symm hu x (Y x) (X x)]
  simp only [inner_add_left, inner_sub_left, inner_smul_left, inner_mgradient_right,
    real_inner_comm, map_add, map_sub, map_smul, smul_eq_mul, RCLike.conj_to_real]
  module

/-- In an orthonormal basis, `∑ du(bᵢ)² = |grad u|²`. -/
private theorem sum_mvfderiv_mul_mvfderiv [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (u : M → ℝ) (x : M) {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    ∑ i, mvfderiv I u x (b i) * mvfderiv I u x (b i) = ⟪mgradient I u x, mgradient I u x⟫ := by
  rw [← b.sum_inner_mul_inner]
  simp only [inner_mgradient, inner_mgradient_right]

variable [T2Space M]

/-- **Curvature tensor under the conformal change `e^(2u) g`.** For a smooth metric `g` and a
smooth function `u`, the `(1,3)` curvature tensor of `e^(2u) g` at `x` is

`R(v, w) z + T(v, z) w - T(w, z) v - g(w, z) T♯(v) + g(v, z) T♯(w) + |du|² (g(v, z) w - g(w, z) v)`,

where `R` is the curvature tensor of `g`, `T(v, z) = Hess u(v, z) - du(v) du(z)` and
`T♯(v) = ∇_v grad u - du(v) grad u`. -/
theorem curvatureTensor_leviCivitaConnection_rescale_exp
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (x : M) (v w z : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun y ↦ Real.exp (2 * u y))
          (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hu))
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x v w z) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI cov := CovariantDerivative.leviCivitaConnection I M
    cov.curvatureTensor x v w z +
      (hessian I u x v z - mvfderiv I u x v * mvfderiv I u x z) • w -
      (hessian I u x w z - mvfderiv I u x w * mvfderiv I u x z) • v -
      ⟪w, z⟫ • (cov (mgradient I u) x v - mvfderiv I u x v • mgradient I u x) +
      ⟪v, z⟫ • (cov (mgradient I u) x w - mvfderiv I u x w • mgradient I u x) +
      ⟪mgradient I u x, mgradient I u x⟫ • (⟪v, z⟫ • w - ⟪w, z⟫ • v) := by
  obtain ⟨X, hX, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  obtain ⟨Z, hZ, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E z
  rw [CovariantDerivative.curvatureTensor_apply _ x hX hY hZ,
    curvatureOperator_leviCivitaConnection_rescale_exp g hu hX hY hZ x]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  rw [CovariantDerivative.curvatureTensor_apply _ x hX hY hZ]

/-- **Ricci curvature under the conformal change `e^(2u) g`.** For a smooth metric `g` on a
manifold of dimension `n` and a smooth function `u`,

`Ric^(e^(2u) g) = Ric^g - (n - 2) (Hess u - du ⊗ du) - (Δu + (n - 2) |du|²) g`,

where `Δ = div grad` is the Laplace–Beltrami operator of `g`. -/
theorem ricciTensor_leviCivitaConnection_rescale_exp
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (x : M) (v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale (fun y ↦ Real.exp (2 * u y))
          (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hu))
          fun _ ↦ Real.exp_pos _).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).ricciTensor x v w -
      ((Module.finrank ℝ E : ℝ) - 2) * (hessian I u x v w - mvfderiv I u x v * mvfderiv I u x w) -
      (laplaceBeltrami I u x + ((Module.finrank ℝ E : ℝ) - 2) *
        ⟪mgradient I u x, mgradient I u x⟫) * ⟪v, w⟫ := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- Trace the curvature formula against a `g`-orthonormal basis.
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  set cov := CovariantDerivative.leviCivitaConnection I M
  set G := mgradient I u x
  set du : TangentSpace I x →ₗ[ℝ] ℝ := (mvfderiv I u x).toLinearMap
  -- The correction to the curvature is `-(T + ½ |du|² g) ⊙ g`, with `T = Hess u - du ⊗ du`.
  let K : LinearMap.BilinForm ℝ (TangentSpace I x) :=
    (innerₗ _).comp (cov (mgradient I u) x).toLinearMap -
      (LinearMap.mul ℝ ℝ).compl₁₂ du du + ((1 / 2 : ℝ) * ⟪G, G⟫) • innerₗ _
  have hK (v w : TangentSpace I x) :
      K v w =
        hessian I u x v w - mvfderiv I u x v * mvfderiv I u x w + 1 / 2 * ⟪G, G⟫ * ⟪v, w⟫ := by
    simp [K, du, cov, hessian_def]
    -- `mvfderiv` takes values in the tangent space of `ℝ`, which is `ℝ` only by definition.
    rfl
  rw [CovariantDerivative.ricciTensor_eq_sum_inner _ x b]
  simp only [curvatureTensor_leviCivitaConnection_rescale_exp g hu x]
  have key (i) : ⟪b i, cov.curvatureTensor x (b i) v w +
      (hessian I u x (b i) w - mvfderiv I u x (b i) * mvfderiv I u x w) • v -
      (hessian I u x v w - mvfderiv I u x v * mvfderiv I u x w) • b i -
      ⟪v, w⟫ • (cov (mgradient I u) x (b i) - mvfderiv I u x (b i) • G) +
      ⟪b i, w⟫ • (cov (mgradient I u) x v - mvfderiv I u x v • G) +
      ⟪G, G⟫ • (⟪b i, w⟫ • v - ⟪v, w⟫ • b i)⟫ =
      ⟪b i, cov.curvatureTensor x (b i) v w⟫ -
        LinearMap.BilinForm.kulkarniNomizu K (innerₗ _) (b i) v w (b i) := by
    have h₁ (y z : TangentSpace I x) : ⟪z, cov (mgradient I u) x y⟫ = hessian I u x y z := by
      rw [hessian_def, real_inner_comm]
    simp only [LinearMap.BilinForm.kulkarniNomizu_apply, hK, innerₗ_apply_apply,
      inner_add_right, inner_sub_right, inner_smul_right, inner_mgradient_right, G, h₁,
      hessian_symm hu x v (b i), real_inner_comm (b i)]
    ring
  rw [Finset.sum_congr rfl fun i _ ↦ key i, Finset.sum_sub_distrib,
    ← CovariantDerivative.ricciTensor_eq_sum_inner cov x b,
    LinearMap.BilinForm.sum_kulkarniNomizu_innerₗ, TauCeti.bilinFormTrace_eq_sum K b,
    laplaceBeltrami_eq_sum_hessian I u x b]
  -- The tangent space `TangentSpace I x` is the model space `E`.
  have hn : Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E := rfl
  have s₀ : ∑ i, ⟪b i, b i⟫ = Module.finrank ℝ E :=
    (TauCeti.bilinFormTrace_eq_sum (innerₗ _) b).symm.trans TauCeti.bilinFormTrace_inner
  simp only [hK, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_mvfderiv_mul_mvfderiv u x b, s₀, hn]
  ring

/-- **Scalar curvature under the conformal change `e^(2u) g`.** For a smooth metric `g` on a
manifold of dimension `n` and a smooth function `u`,

`Scal(e^(2u) g) = e^(-2u) (Scal(g) - 2 (n - 1) Δu - (n - 1) (n - 2) |du|²)`,

where `Δ = div grad` is the Laplace–Beltrami operator of `g`. -/
theorem scalarCurvature_rescale_exp
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {u : M → ℝ} (hu : ContMDiff I 𝓘(ℝ) ∞ u) (x : M) :
    (g.rescale (fun y ↦ Real.exp (2 * u y))
      (Real.contDiff_exp.comp_contMDiff (contMDiff_const.mul hu))
      fun _ ↦ Real.exp_pos _).scalarCurvature x =
    Real.exp (-2 * u x) * (g.scalarCurvature x -
      2 * ((Module.finrank ℝ E : ℝ) - 1) *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          laplaceBeltrami I u x) -
      ((Module.finrank ℝ E : ℝ) - 1) * ((Module.finrank ℝ E : ℝ) - 2) *
        (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
          ⟪mgradient I u x, mgradient I u x⟫)) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  -- A `g`-orthonormal basis, recorded as a plain basis through the inner products of `g`.
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hb : ∀ i j, g.inner x (b.toBasis i) (b.toBasis j) = if i = j then 1 else 0 :=
    fun i j ↦ by
      rw [b.coe_toBasis, ← inner_riemannianBundle]
      exact orthonormal_iff_ite.1 b.orthonormal i j
  rw [scalarCurvature_rescale_eq_sum g _ _ x b.toBasis hb, b.coe_toBasis, ← Real.exp_neg,
    neg_mul_eq_neg_mul, scalarCurvature_def]
  simp only [ricciTensor_leviCivitaConnection_rescale_exp g hu x]
  -- Sum the Ricci formula over the `g`-orthonormal basis.
  have s₀ : ∑ i, ⟪b i, b i⟫ = Module.finrank ℝ E :=
    (TauCeti.bilinFormTrace_eq_sum (innerₗ _) b).symm.trans TauCeti.bilinFormTrace_inner
  have s₁ : ∑ i, hessian I u x (b i) (b i) = laplaceBeltrami I u x :=
    (laplaceBeltrami_eq_sum_hessian I u x b).symm
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_sub_distrib, s₁, sum_mvfderiv_mul_mvfderiv u x b, s₀,
    ← CovariantDerivative.scalarCurvature_eq_sum _ x b]
  ring

end Exp

end Bundle.ContMDiffRiemannianMetric
