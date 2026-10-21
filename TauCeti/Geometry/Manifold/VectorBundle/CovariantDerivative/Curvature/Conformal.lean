/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AddOneForm
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Conformal
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Regularity
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Regularity

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
As for the conformal change of the Levi-Civita connection
(`Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_apply`), connections do not depend
on a metric, so each metric is installed in turn as the `RiemannianBundle` instance of the tangent
bundle of `M` and the connections are compared directly on `M`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale`: the curvature
  of `f g` in terms of a Levi-Civita connection of `g` and the conformal connection tensor of `f`.
* `Bundle.ContMDiffRiemannianMetric.curvatureOperator_leviCivitaConnection_rescale_of_contMDiff`:
  the same identity for a smooth metric, a smooth conformal factor and smooth vector fields.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.J.
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
