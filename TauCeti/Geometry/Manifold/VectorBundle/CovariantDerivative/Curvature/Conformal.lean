/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AddOneForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Conformal
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Geometry.Manifold.ContMDiff.Log
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Basic
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
of the Riemann curvature under the conformal change `e^(2φ) g`.

The identity holds at a point `x` for a `Cⁿ` metric with `1 ≤ n`, and with the Levi-Civita
connection of `g` replaced by any connection that is Levi-Civita for `g`. The conformal factor `f`
is assumed `Cⁿ` on all of `M` and the vector field `Z` differentiable on all of `M`; the remaining
hypotheses are differentiability at `x` of `X`, `Y`, `∇_X Z`, `∇_Y Z`, `A(Z, X)` and `A(Z, Y)`.
For a smooth metric, a smooth conformal factor and smooth vector fields all the hypotheses hold.
As for the conformal change of the Levi-Civita connection
(`Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_apply`), connections do not depend
on a metric, so each metric is installed in turn as the `RiemannianBundle` instance of the tangent
bundle of `M` and the connections are compared directly on `M`.

For a smooth metric and a smooth conformal factor `f = e^(2φ)`, the difference of the two
curvatures is a tensor built from the Hessian `Hess φ`, the differential `dφ` and the gradient
`grad φ`, so it can be evaluated pointwise and contracted. The factor is given as a smooth
positive function `f` together with a function `φ` satisfying `f = e^(2φ)`; such a `φ` is
automatically smooth. With `n` the dimension, `Δ = div grad`
the Laplace–Beltrami operator of `g` and `R(u, v) w = ∇_u ∇_v w - ∇_v ∇_u w - ∇_[u,v] w`, the
contractions are the classical formulas

`Ric^ĝ = Ric^g - (n - 2) (Hess φ - dφ ⊗ dφ) + (-Δφ - (n - 2) |dφ|²) g`,

`Scal^ĝ = e^(-2φ) (Scal^g - 2 (n - 1) Δφ - (n - 1) (n - 2) |dφ|²)`.

The scalar formula is the input from which the conformal Laplacian of the Yamabe problem arises.
In dimension two it becomes `Scal^ĝ = e^(-2φ) (Scal^g - 2 Δφ)`, the curvature equation of
conformal metrics on surfaces.

In dimension `n ≥ 3` the Ricci and scalar formulas combine into the transformation law of the
Schouten tensor `P = (Ric - Scal g / (2 (n - 1))) / (n - 2)`,

`P^ĝ = P^g - Hess φ + dφ ⊗ dφ - (|dφ|² / 2) g`,

Since the fully covariant curvature tensor of `ĝ` is `e^(2φ) (Rm^g - T ⊙ g)`, with ⊙ the
Kulkarni–Nomizu product and `T = Hess φ - dφ ⊗ dφ + (|dφ|² / 2) g` the same correction, the Weyl
tensor `W = Rm - P ⊙ g` satisfies `W^ĝ = f W^g` for `ĝ = f g`, away from dimension `2`.
Equivalently, the Weyl tensor of type `(1, 3)` is a conformal invariant; in particular its
vanishing depends only on the conformal class. This is the conformal invariance used in the
characterization of local conformal flatness by the Weyl tensor.

## Main results

* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale`: the curvature
  of `f g` in terms of a Levi-Civita connection of `g` and the conformal connection tensor of `f`.
* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale_of_contMDiff`:
  the same identity for a smooth metric, a smooth conformal factor and smooth vector fields.
* `Bundle.ContMDiffRiemannianMetric.curvatureTensor_leviCivitaConnection_rescale`: the pointwise
  curvature tensor of `e^(2φ) g` in terms of that of `g`, `Hess φ`, `dφ` and `grad φ`.
* `Bundle.ContMDiffRiemannianMetric.ricciTensor_leviCivitaConnection_rescale`: the Ricci tensor of
  `e^(2φ) g`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale`: the scalar curvature of `e^(2φ) g`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_of_finrank_eq_two`: on a surface,
  `Scal^(e^(2φ) g) = e^(-2φ) (Scal^g - 2 Δφ)`.
* `Bundle.ContMDiffRiemannianMetric.scalarCurvature_rescale_eq_iff_of_finrank_eq_two`: on a surface,
  `e^(2φ) g` has scalar curvature `c` exactly when `-Δφ + Scal^g / 2 = (c / 2) e^(2φ)`.
* `Bundle.ContMDiffRiemannianMetric.schoutenTensor_leviCivitaConnection_rescale`: the Schouten
  tensor of `e^(2φ) g`.
* `Bundle.ContMDiffRiemannianMetric.weylTensor_leviCivitaConnection_rescale`: the Weyl tensor of
  `f g` is `f` times that of `g`.
* `Bundle.ContMDiffRiemannianMetric.weylTensor_leviCivitaConnection_rescale_eq_zero_iff`: the Weyl
  tensor of `f g` vanishes at a point exactly when that of `g` does.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Sections 1.G and 1.J.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 7 (curvature of conformally related metrics).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle
open scoped ContDiff Manifold

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

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The covariant derivative of the conformal connection tensor `A` of `e^(2φ)`:
`(∇_X A)(Z, Y) = Hess φ(X, Y) Z + Hess φ(X, Z) Y - g(Z, Y) ∇_X grad φ`. -/
private theorem leviCivitaConnection_conformalConnectionTensor_exp {φ : M → ℝ}
    (hφ : ContMDiff I 𝓘(ℝ) ∞ φ) {X Y Z : Π x : M, TangentSpace I x}
    (hY : CMDiff ∞ (T% Y)) (hZ : CMDiff ∞ (T% Z)) (x : M) :
    CovariantDerivative.leviCivitaConnection I M
        (fun y ↦ conformalConnectionTensor I (fun y ↦ Real.exp (2 * φ y)) y (Z y) (Y y)) x
        (X x) -
      conformalConnectionTensor I (fun y ↦ Real.exp (2 * φ y)) x
        (CovariantDerivative.leviCivitaConnection I M Z x (X x)) (Y x) -
      conformalConnectionTensor I (fun y ↦ Real.exp (2 * φ y)) x (Z x)
        (CovariantDerivative.leviCivitaConnection I M Y x (X x)) =
    hessian I φ x (X x) (Y x) • Z x + hessian I φ x (X x) (Z x) • Y x -
      inner ℝ (Z x) (Y x) •
        CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x (X x) := by
  let _ : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have hφ' : MDiff φ := hφ.mdifferentiable (by simp)
  have hG : CMDiff ∞ (T% (mgradient I φ)) := contMDiff_mgradient hφ
  have hinner {U W : Π x : M, TangentSpace I x} (hU : CMDiff ∞ (T% U)) (hW : CMDiff ∞ (T% W)) :
      MDiffAt (fun y ↦ inner ℝ (U y) (W y)) x :=
    mdifferentiableAt_inner (hU.mdifferentiableAt (by simp)) (hW.mdifferentiableAt (by simp))
  have hd {W : Π x : M, TangentSpace I x} (hW : CMDiff ∞ (T% W)) :
      MDiffAt (fun y ↦ mvfderiv I φ y (W y)) x := by
    simpa only [inner_mgradient] using hinner hG hW
  -- Write `A(Z, Y) = dφ(Y) Z + dφ(Z) Y - g(Z, Y) grad φ` and apply the Leibniz rule.
  have hfield :
      (fun y ↦ conformalConnectionTensor I (fun y ↦ Real.exp (2 * φ y)) y (Z y) (Y y)) =
      (fun y ↦ mvfderiv I φ y (Y y)) • Z + (fun y ↦ mvfderiv I φ y (Z y)) • Y +
        (fun y ↦ -inner ℝ (Z y) (Y y)) • mgradient I φ := by
    funext y
    simp only [conformalConnectionTensor_exp_two_mul_apply (hφ' y), Pi.add_apply,
      Pi.smul_apply', neg_smul, sub_eq_add_neg]
  have hYx := hY.mdifferentiableAt (x := x) (by simp)
  have hZx := hZ.mdifferentiableAt (x := x) (by simp)
  have hGx := hG.mdifferentiableAt (x := x) (by simp)
  have hn : MDiffAt (fun y ↦ -inner ℝ (Z y) (Y y)) x := (hinner hZ hY).neg
  rw [hfield, (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      (mdifferentiableAt_add_section ((hd hY).smul_section hZx) ((hd hZ).smul_section hYx))
      (hn.smul_section hGx),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.add
      ((hd hY).smul_section hZx) ((hd hZ).smul_section hYx),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.leibniz hZx (hd hY),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.leibniz hYx (hd hZ),
    (CovariantDerivative.leviCivitaConnection I M).isCovariantDerivativeOnUniv.leibniz hGx hn]
  -- The derivatives of `dφ(Y)` and `dφ(Z)` give the Hessian, and that of `g(Z, Y)` cancels by
  -- metric compatibility.
  have hφ2 : ContMDiff I 𝓘(ℝ) 2 φ := hφ.of_le (by simp)
  have hHY := hessian_apply_eq_mvfderiv_sub x hφ2.contMDiffAt X Y hYx
  have hHZ := hessian_apply_eq_mvfderiv_sub x hφ2.contMDiffAt X Z hZx
  have hm := (CovariantDerivative.isMetricCompatible_leviCivitaConnection I).mvfderiv_inner_eq
      X hZx hYx
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, mvfderiv_fun_neg,
    neg_apply, conformalConnectionTensor_exp_two_mul_apply (hφ' x), hHY, hHZ, hm]
  module

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

/-- **Curvature tensor under conformal change.** Let `g` be a smooth metric and `f = e^(2φ)` a
smooth positive function. With `Hess φ`, `∇` and `grad φ` taken for `g`, the curvature tensor of
`f g` at `x` is

`R^(f g)(u, v) w = R^g(u, v) w + Hess φ(u, w) v - Hess φ(v, w) u + g(u, w) ∇_v grad φ`
`- g(v, w) ∇_u grad φ + dφ(v) dφ(w) u - dφ(u) dφ(w) v + (dφ(u) g(v, w) - dφ(v) g(u, w)) grad φ`
`- |dφ|² (g(v, w) u - g(u, w) v)`. -/
theorem curvatureTensor_leviCivitaConnection_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) (u v w : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x u v w) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI cov := CovariantDerivative.leviCivitaConnection I M
    cov.curvatureTensor x u v w + hessian I φ x u w • v - hessian I φ x v w • u +
      ⟪u, w⟫ • cov (mgradient I φ) x v - ⟪v, w⟫ • cov (mgradient I φ) x u +
      (mvfderiv I φ x v * mvfderiv I φ x w) • u - (mvfderiv I φ x u * mvfderiv I φ x w) • v +
      (mvfderiv I φ x u * ⟪v, w⟫ - mvfderiv I φ x v * ⟪u, w⟫) • mgradient I φ x -
      ‖mgradient I φ x‖ ^ 2 • (⟪v, w⟫ • u - ⟪u, w⟫ • v) := by
  have hφ : ContMDiff I 𝓘(ℝ) ∞ φ := by
    simpa only [hfφ, Real.log_exp, mul_div_cancel_left₀ _ (two_ne_zero' ℝ)] using
      (hf.log fun y ↦ (hf_pos y).ne').div_const 2
  obtain rfl : f = fun y ↦ Real.exp (2 * φ y) := funext hfφ
  obtain ⟨X, hX, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E u
  obtain ⟨Y, hY, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E v
  obtain ⟨Z, hZ, rfl⟩ := FiberBundle.exists_contMDiff_section_eq I E w
  have h₁ : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x (X x) (Y x) (Z x)) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).curvatureOperator X Y Z x) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale _ hf hf_pos).toRiemannianMetric⟩
    exact CovariantDerivative.curvatureTensor_apply _ x hX hY hZ
  rw [h₁, curvatureOperator_leviCivitaConnection_rescale_of_contMDiff g hf hf_pos hX hY hZ x]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hφx : MDiffAt φ x := hφ.mdifferentiableAt (by simp)
  rw [CovariantDerivative.curvatureTensor_apply _ x hX hY hZ]
  have hXYZ := leviCivitaConnection_conformalConnectionTensor_exp hφ (X := X) hY hZ x
  have hYXZ := leviCivitaConnection_conformalConnectionTensor_exp hφ (X := Y) hX hZ x
  have hφ2 : ContMDiff I 𝓘(ℝ) 2 φ := hφ.of_le (by simp)
  rw [hXYZ, hYXZ, hessian_symm x hφ2.contMDiffAt (Y x) (X x)]
  simp only [conformalConnectionTensor_exp_two_mul_apply hφx, map_add, map_sub, map_smul,
    add_apply, sub_apply, smul_apply, inner_mgradient, mvfderiv_apply_mgradient,
    real_inner_self_eq_norm_sq]
  simp only [real_inner_comm (X x) (Z x), real_inner_comm (Y x) (Z x),
    real_inner_comm (X x) (Y x)]
  module

/-- **Ricci tensor under conformal change.** Let `g` be a smooth metric on a manifold of
dimension `n` and `f = e^(2φ)` a smooth positive function. Then
`Ric^(f g) = Ric^g - (n - 2) (Hess φ - dφ ⊗ dφ) + (-Δφ - (n - 2) |dφ|²) g`, where `Hess φ`,
`Δφ = div grad φ` and `|dφ|` are taken for `g`. -/
theorem ricciTensor_leviCivitaConnection_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) (u v : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x u v) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).ricciTensor x u v -
      (Module.finrank ℝ E - 2) * (hessian I φ x u v - mvfderiv I φ x u * mvfderiv I φ x v) +
      (-laplaceBeltrami I φ x - (Module.finrank ℝ E - 2) * ‖mgradient I φ x‖ ^ 2) * ⟪u, v⟫ := by
  -- The Ricci tensor is a trace, which does not involve the metric.
  have hRic : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).ricciTensor x u v) =
      LinearMap.trace ℝ (TangentSpace I x)
        (((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
        (CovariantDerivative.leviCivitaConnection I M).curvatureTensor x).flip u).flip v) := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
    exact CovariantDerivative.ricciTensor_apply _ x u v
  rw [hRic]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  rw [LinearMap.trace_eq_sum_inner _ b,
    CovariantDerivative.ricciTensor_eq_sum_inner _ x b u v]
  simp only [LinearMap.flip_apply, curvatureTensor_leviCivitaConnection_rescale g hf hf_pos hfφ]
  simp only [inner_add_right, inner_sub_right, inner_smul_right, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- The contractions against the orthonormal basis `b`.
  have hsum (a c : TangentSpace I x) : ∑ i, ⟪b i, a⟫ * ⟪b i, c⟫ = ⟪a, c⟫ := by
    rw [← b.sum_inner_mul_inner a c]
    simp only [real_inner_comm a]
  have hdim : ∑ i, ⟪b i, b i⟫ = Module.finrank ℝ E := by
    rw [b.sum_inner_self, Fintype.card_fin, TauCeti.finrank_tangentSpace]
  have hΔ : ∑ i, ⟪b i, CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x (b i)⟫ =
      laplaceBeltrami I φ x := by
    simp only [laplaceBeltrami_eq_sum_hessian I φ x b, hessian_def, real_inner_comm]
  have hH₁ : ∑ i, hessian I φ x (b i) v * ⟪b i, u⟫ = hessian I φ x u v := by
    simpa only [hessian_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      innerSL_apply_apply] using
      b.sum_apply_mul_inner (((innerSL ℝ).flip v).comp
        (CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x)) u
  have hH₂ : ∑ i, ⟪b i, v⟫ *
      ⟪b i, CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x u⟫ =
      hessian I φ x u v := by
    rw [hsum, real_inner_comm, hessian_def]
  have hP₁ : ∑ i, mvfderiv I φ x (b i) * mvfderiv I φ x v * ⟪b i, u⟫ =
      mvfderiv I φ x u * mvfderiv I φ x v := by
    simp only [mul_right_comm _ (mvfderiv I φ x v), ← Finset.sum_mul, b.sum_apply_mul_inner]
  have hP₂ : ∑ i, (mvfderiv I φ x (b i) * ⟪u, v⟫ - mvfderiv I φ x u * ⟪b i, v⟫) *
      ⟪b i, mgradient I φ x⟫ =
      ⟪u, v⟫ * ‖mgradient I φ x‖ ^ 2 - mvfderiv I φ x u * mvfderiv I φ x v := by
    simp only [sub_mul, Finset.sum_sub_distrib, mul_right_comm _ ⟪u, v⟫,
      mul_assoc (mvfderiv I φ x u), ← Finset.mul_sum, ← Finset.sum_mul, b.sum_apply_mul_inner,
      hsum]
    rw [mvfderiv_apply_mgradient, real_inner_self_eq_norm_sq, inner_mgradient_right]
    ring
  rw [hH₁, hdim, hH₂, hΔ, hP₁, hP₂, hsum v u, real_inner_comm v u]
  ring

/-- **Scalar curvature under conformal change.** Let `g` be a smooth metric on a manifold of
dimension `n` and `f = e^(2φ)` a smooth positive function. Then
`Scal^(f g) = f⁻¹ (Scal^g - 2 (n - 1) Δφ - (n - 1) (n - 2) |dφ|²)`, where `Δφ = div grad φ` and
`|dφ|` are taken for `g`. -/
theorem scalarCurvature_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) :
    (g.rescale f hf hf_pos).scalarCurvature x =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (f x)⁻¹ * (g.scalarCurvature x - 2 * (Module.finrank ℝ E - 1) * laplaceBeltrami I φ x -
        (Module.finrank ℝ E - 1) * (Module.finrank ℝ E - 2) * ‖mgradient I φ x‖ ^ 2) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  -- Contract the conformal change of the Ricci tensor against the `g`-orthonormal basis `b`.
  have hG : ‖mgradient I φ x‖ ^ 2 = ∑ j, mvfderiv I φ x (b j) * mvfderiv I φ x (b j) := by
    rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner]
    simp only [inner_mgradient, inner_mgradient_right]
  rw [scalarCurvature_rescale_eq_sum g hf hf_pos b, scalarCurvature_def,
    CovariantDerivative.scalarCurvature_eq_sum _ x b]
  simp only [ricciTensor_leviCivitaConnection_rescale g hf hf_pos hfφ, real_inner_self_eq_norm_sq,
    b.orthonormal.1, one_pow, mul_one, laplaceBeltrami_eq_sum_hessian I φ x b, hG]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, TauCeti.finrank_tangentSpace]
  ring

/-- **Scalar curvature under conformal change on a surface.** Let `g` be a smooth metric on a
surface and `f = e^(2φ)` a smooth positive function. Then
`Scal^(f g) = f⁻¹ (Scal^g - 2 Δφ)`, where `Δφ = div grad φ` is taken for `g`. -/
theorem scalarCurvature_rescale_of_finrank_eq_two
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ} (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (x : M) :
    (g.rescale f hf hf_pos).scalarCurvature x =
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      (f x)⁻¹ * (g.scalarCurvature x - 2 * laplaceBeltrami I φ x) := by
  rw [g.scalarCurvature_rescale hf hf_pos hfφ x, hE]
  norm_num

/-- **The prescribed curvature equation on a surface.** Let `g` be a smooth metric on a surface
and `f = e^(2φ)` a smooth positive function. Then `e^(2φ) g` has scalar curvature `c` at `x`
exactly when `-Δφ + Scal^g / 2 = (c / 2) e^(2φ)` there, where `Δφ = div grad φ` is taken for
`g`. Since the scalar curvature of a surface is twice its Gaussian curvature, for `c = -2` this is
the equation `Δ⁺φ + K + e^(2φ) = 0` for a metric of Gaussian curvature `-1`, where
`Δ⁺ = -div grad` and `K = Scal^g / 2`. -/
theorem scalarCurvature_rescale_eq_iff_of_finrank_eq_two
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hE : Module.finrank ℝ E = 2) {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ} (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (c : ℝ) (x : M) :
    (g.rescale f hf hf_pos).scalarCurvature x = c ↔
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      -laplaceBeltrami I φ x + g.scalarCurvature x / 2 = c / 2 * Real.exp (2 * φ x) := by
  rw [scalarCurvature_rescale_of_finrank_eq_two g hE hf hf_pos hfφ x, ← hfφ x,
    inv_mul_eq_iff_eq_mul₀ (hf_pos x).ne']
  constructor <;> intro h <;> linarith

/-- **Schouten tensor under conformal change.** Let `g` be a smooth metric on a manifold of
dimension `n ≥ 3` and `f = e^(2φ)` a smooth positive function. Then the Schouten tensor of `f g` is
`P^(f g) = P^g - Hess φ + dφ ⊗ dφ - (|dφ|² / 2) g`, where `Hess φ` and `|dφ|` are taken for `g`. -/
theorem schoutenTensor_leviCivitaConnection_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x) {φ : M → ℝ}
    (hfφ : ∀ x, f x = Real.exp (2 * φ x)) (hn : 3 ≤ Module.finrank ℝ E) (x : M)
    (u v : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).schoutenTensor x u v) =
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    (CovariantDerivative.leviCivitaConnection I M).schoutenTensor x u v - hessian I φ x u v +
      mvfderiv I φ x u * mvfderiv I φ x v - ‖mgradient I φ x‖ ^ 2 / 2 * ⟪u, v⟫ := by
  have hR := ricciTensor_leviCivitaConnection_rescale g hf hf_pos hfφ x u v
  have hS := scalarCurvature_rescale g hf hf_pos hfφ x
  -- Unfold the Schouten tensor of `f g`, whose metric term is `f x` times that of `g`.
  have hL : (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).schoutenTensor x u v) =
      ((Module.finrank ℝ E : ℝ) - 2)⁻¹ *
        ((letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
          ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
          (CovariantDerivative.leviCivitaConnection I M).ricciTensor x u v) -
        (g.rescale f hf hf_pos).scalarCurvature x / (2 * ((Module.finrank ℝ E : ℝ) - 1)) *
          (f x * g.inner x u v)) := by
    simp only [CovariantDerivative.schoutenTensor_apply, TauCeti.finrank_tangentSpace,
      scalarCurvature_def, inner_riemannianBundle (g.rescale f hf hf_pos), rescale_inner]
  rw [hL, hR, hS]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hSg : g.scalarCurvature x =
      (CovariantDerivative.leviCivitaConnection I M).scalarCurvature x :=
    scalarCurvature_def g x
  rw [CovariantDerivative.schoutenTensor_apply, TauCeti.finrank_tangentSpace,
    ← inner_riemannianBundle, hSg]
  have hn' : (3 : ℝ) ≤ Module.finrank ℝ E := by exact_mod_cast hn
  have hn2 : (Module.finrank ℝ E : ℝ) - 2 ≠ 0 := by linarith
  have hn1 : (Module.finrank ℝ E : ℝ) - 1 ≠ 0 := by linarith
  have hf0 : f x ≠ 0 := (hf_pos x).ne'
  field_simp
  ring

/-- **Weyl tensor under conformal change.** Away from dimension `2`, the fully covariant Weyl
tensor of a conformally rescaled smooth metric `f g` is `f` times that of `g`:
`W^(f g)(u, v, w, z) = f W^g(u, v, w, z)`. Equivalently, the Weyl tensor of type `(1, 3)` is
conformally invariant. -/
theorem weylTensor_leviCivitaConnection_rescale
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
    (hn : Module.finrank ℝ E ≠ 2) (x : M) (u v w z : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x u v w z) =
    f x * (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x u v w z) := by
  rcases le_or_gt (Module.finrank ℝ E) 1 with h1 | h3
  · -- In dimension at most one both Weyl tensors vanish.
    rw [← TauCeti.finrank_tangentSpace (I := I) x] at h1
    have h0 (g' : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)) :=
      letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g'.toRiemannianMetric⟩
      (CovariantDerivative.leviCivitaConnection I M).weylTensor_eq_zero_of_finrank_le_one x h1
    rw [h0 (g.rescale f hf hf_pos), h0 g]
    simp
  set φ : M → ℝ := fun y ↦ Real.log (f y) / 2
  have hfφ (y : M) : f y = Real.exp (2 * φ y) := by
    simp only [φ, mul_div_cancel₀ _ (two_ne_zero' ℝ), Real.exp_log (hf_pos y)]
  -- Expand both Weyl tensors and insert the conformal laws for the curvature and Schouten
  -- tensors of `f g`; the correction terms then cancel.
  simp only [CovariantDerivative.weylTensor_apply,
    CovariantDerivative.riemannCurvatureTensor_apply, LinearMap.BilinForm.kulkarniNomizu_apply,
    innerₗ_apply_apply, schoutenTensor_leviCivitaConnection_rescale g hf hf_pos hfφ (by omega),
    curvatureTensor_leviCivitaConnection_rescale g hf hf_pos hfφ]
  -- Express every inner product, of `f g` or of `g`, through `g.inner`.
  simp only [inner_riemannianBundle (g.rescale f hf hf_pos), rescale_inner,
    inner_riemannianBundle g]
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have hH (a b : TangentSpace I x) : g.inner x
      (CovariantDerivative.leviCivitaConnection I M (mgradient I φ) x a) b = hessian I φ x a b :=
    (hessian_def I φ x a b).symm
  have hd (b : TangentSpace I x) : g.inner x (mgradient I φ x) b = mvfderiv I φ x b :=
    inner_mgradient b
  simp only [map_add, map_sub, map_smul, add_apply, sub_apply, smul_apply, smul_eq_mul, hH, hd]
  ring

/-- Away from dimension `2`, the Weyl tensor of a conformally rescaled smooth metric `f g` vanishes
at a point exactly when that of `g` does. -/
theorem weylTensor_leviCivitaConnection_rescale_eq_zero_iff
    (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hf_pos : ∀ x, 0 < f x)
    (hn : Module.finrank ℝ E ≠ 2) (x : M) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0 ↔
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      (CovariantDerivative.leviCivitaConnection I M).weylTensor x) = 0 := by
  have h := weylTensor_leviCivitaConnection_rescale g hf hf_pos hn x
  have hf0 : f x ≠ 0 := (hf_pos x).ne'
  constructor <;> intro h0 <;> ext u v w z
  · simpa [h0, hf0] using (h u v w z).symm
  · simpa [h0] using h u v w z

end Bundle.ContMDiffRiemannianMetric
