/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.ContractedBianchi
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Cotton
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Weyl.Basic
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Sum
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The divergence of the Weyl tensor

For a metric-compatible torsion-free connection on the tangent bundle of a Riemannian manifold of
dimension `n ≠ 2`, the divergence of the Weyl tensor is a multiple of the Cotton tensor:

`∑ᵢ (∇_{eᵢ} W)(eᵢ, u, v, w) = (n - 3) C(u, v, w)`

in any orthonormal basis `eᵢ`, where `C(u, v, w) = (∇_w P)(u, v) - (∇_v P)(u, w)` and `P` is the
Schouten tensor. In dimension `3` the left side vanishes because `W` does, while `C` is the
obstruction to local conformal flatness; in dimension at least `4` a metric with vanishing Weyl
tensor therefore has vanishing Cotton tensor, which is the integrability condition behind the
Weyl–Schouten theorem.

The covariant derivative of `W = Rm - P ⊙ g` is `∇_d W = ∇_d Rm - (∇_d P) ⊙ g`, because the metric
is parallel. We define it by this formula (`CovariantDerivative.derivWeylTensor`) and show that it
satisfies the Leibniz rule characterizing the covariant derivative of a tensor
(`CovariantDerivative.IsMetricCompatible.derivWeylTensor_eq_mvfderiv_sub`). The divergence of `Rm`
is the antisymmetrized derivative of Ricci curvature by the contracted second Bianchi identity, and
the divergence of `(∇P) ⊙ g` involves the divergence of `P`, which the twice contracted Bianchi
identity `2 div Ric = d Scal` identifies with `d (tr_g P)`. The difference is `(n - 3) C`.

## Main declarations

* `CovariantDerivative.derivWeylTensor`: the covariant derivative of the Weyl tensor, with
  `CovariantDerivative.IsMetricCompatible.derivWeylTensor_eq_mvfderiv_sub` its Leibniz rule on
  smooth vector fields.
* `CovariantDerivative.IsMetricCompatible.sum_derivWeylTensor_self_eq_mul_cottonTensor`:
  `div W = (n - 3) C`.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G (the Cotton tensor and the
  divergence of the Weyl tensor).
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle FiberBundle LinearMap.BilinForm
open scoped ContDiff Manifold

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

/-- The covariant derivative of the Weyl tensor along `d`,
`cov.derivWeylTensor x d u v w z = (∇_d W)(u, v, w, z)`, defined as
`⟨(∇_d R)(u, v)w, z⟩ - ((∇_d P) ⊙ g)(u, v, w, z)` with `P` the Schouten tensor. For a
metric-compatible connection the metric is parallel, so this is the covariant derivative of
`W = Rm - P ⊙ g`; on smooth vector fields it is given by the Leibniz rule
`CovariantDerivative.IsMetricCompatible.derivWeylTensor_eq_mvfderiv_sub`. -/
def derivWeylTensor (x : M) (d : TangentSpace I x) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ]
      TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ
    (fun u v ↦ compLeft (innerₗ (TangentSpace I x)) (cov.derivCurvatureTensor cov x d u v) -
      kulkarniNomizu
        (LinearMap.mk₂ ℝ (fun a c ↦ cov.derivSchoutenTensor x a c d)
          (by simp) (by simp) (by simp) (by simp))
        (innerₗ (TangentSpace I x)) u v)
    (fun u u' v ↦ by ext w z; simp; ring)
    (fun c u v ↦ by ext w z; simp; ring)
    (fun u v v' ↦ by ext w z; simp; ring)
    (fun c u v ↦ by ext w z; simp; ring)

/-- Evaluation of the covariant derivative of the Weyl tensor:
`(∇_d W)(u, v, w, z) = ⟨(∇_d R)(u, v)w, z⟩ - ((∇_d P) ⊙ g)(u, v, w, z)`. -/
@[simp]
theorem derivWeylTensor_apply (x : M) (d u v w z : TangentSpace I x) :
    cov.derivWeylTensor x d u v w z =
      inner ℝ (cov.derivCurvatureTensor cov x d u v w) z -
        (cov.derivSchoutenTensor x u z d * inner ℝ v w +
          cov.derivSchoutenTensor x v w d * inner ℝ u z -
          cov.derivSchoutenTensor x u w d * inner ℝ v z -
          cov.derivSchoutenTensor x v z d * inner ℝ u w) := by
  simp [derivWeylTensor, kulkarniNomizu_apply]

variable [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] {cov}

/-- The product rule for `P(A, B) ⟨C, D⟩` with a metric-compatible connection. -/
private theorem IsMetricCompatible.mvfderiv_schoutenTensor_mul_inner
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    {A B C D : Π y : M, TangentSpace I y} {x : M} (hA : MDiffAt (T% A) x)
    (hB : MDiffAt (T% B) x) (hC : MDiffAt (T% C) x) (hD : MDiffAt (T% D) x)
    (d : TangentSpace I x) :
    mvfderiv I (fun y ↦ cov.schoutenTensor y (A y) (B y) * inner ℝ (C y) (D y)) x d =
      (cov.derivSchoutenTensor x (A x) (B x) d + cov.schoutenTensor x (cov A x d) (B x) +
          cov.schoutenTensor x (A x) (cov B x d)) * inner ℝ (C x) (D x) +
        cov.schoutenTensor x (A x) (B x) *
          (inner ℝ (cov C x d) (D x) + inner ℝ (C x) (cov D x d)) := by
  have hg := hcov.mvfderiv_inner_eq (extend E d) hC hD
  simp only [extend_apply_self] at hg
  rw [mvfderiv_fun_mul (cov.mdifferentiableAt_schoutenTensor_apply hA hB)
    (TauCeti.Manifold.mdifferentiableAt_inner hC hD)]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hg,
    cov.derivSchoutenTensor_apply hA hB]
  ring

/-- **The Leibniz rule for `∇W`.** For a metric-compatible connection and smooth vector fields,
`(∇_d W)(U, V, W, Z) = d (W(U, V, W, Z)) - W(∇_d U, V, W, Z) - W(U, ∇_d V, W, Z) -
W(U, V, ∇_d W, Z) - W(U, V, W, ∇_d Z)`. This characterizes `derivWeylTensor` as the covariant
derivative of the Weyl tensor. -/
theorem IsMetricCompatible.derivWeylTensor_eq_mvfderiv_sub
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov)
    {U V W Z : Π y : M, TangentSpace I y} (hU : CMDiff ∞ (T% U)) (hV : CMDiff ∞ (T% V))
    (hW : CMDiff ∞ (T% W)) (hZ : CMDiff ∞ (T% Z)) (x : M) (d : TangentSpace I x) :
    cov.derivWeylTensor x d (U x) (V x) (W x) (Z x) =
      mvfderiv I (fun y ↦ cov.weylTensor y (U y) (V y) (W y) (Z y)) x d -
        cov.weylTensor x (cov U x d) (V x) (W x) (Z x) -
        cov.weylTensor x (U x) (cov V x d) (W x) (Z x) -
        cov.weylTensor x (U x) (V x) (cov W x d) (Z x) -
        cov.weylTensor x (U x) (V x) (W x) (cov Z x d) := by
  have hd (S : Π y : M, TangentSpace I y) (hS : CMDiff ∞ (T% S)) : MDiffAt (T% S) x :=
    hS.mdifferentiableAt (by simp)
  -- The Riemann part is the covariant derivative of `⟨R(U, V)W, Z⟩`.
  have hR := hcov.inner_derivCurvature (extend E d) hU hV hW hZ x
  simp only [extend_apply_self] at hR
  rw [derivCurvature_apply, ← derivCurvatureTensor_apply cov cov x d hU hV hW] at hR
  have hRd : MDiffAt (fun y ↦ inner ℝ (curvature y (U y) (V y) (W y)) (Z y)) x := by
    have h := TauCeti.Manifold.mdifferentiableAt_inner
      (hd _ (cov.contMDiff_curvatureOperator hU hV hW)) (hd Z hZ)
    simpa only [curvatureTensor_apply cov _ hU hV hW] using h
  have hPd (A B C D : Π y : M, TangentSpace I y) (hA : CMDiff ∞ (T% A))
      (hB : CMDiff ∞ (T% B)) (hC : CMDiff ∞ (T% C)) (hD : CMDiff ∞ (T% D)) :
      MDiffAt (fun y ↦ cov.schoutenTensor y (A y) (B y) * inner ℝ (C y) (D y)) x :=
    (cov.mdifferentiableAt_schoutenTensor_apply (hd A hA) (hd B hB)).mul
      (TauCeti.Manifold.mdifferentiableAt_inner (hd C hC) (hd D hD))
  have h₁ := hPd U Z V W hU hZ hV hW
  have h₂ := hPd V W U Z hV hW hU hZ
  have h₃ := hPd U W V Z hU hW hV hZ
  have h₄ := hPd V Z U W hV hZ hU hW
  have hfun : (fun y ↦ cov.weylTensor y (U y) (V y) (W y) (Z y)) =
      (fun y ↦ inner ℝ (curvature y (U y) (V y) (W y)) (Z y)) -
        ((((fun y ↦ cov.schoutenTensor y (U y) (Z y) * inner ℝ (V y) (W y)) +
          fun y ↦ cov.schoutenTensor y (V y) (W y) * inner ℝ (U y) (Z y)) -
          fun y ↦ cov.schoutenTensor y (U y) (W y) * inner ℝ (V y) (Z y)) -
          fun y ↦ cov.schoutenTensor y (V y) (Z y) * inner ℝ (U y) (W y)) := by
    funext y
    simp only [weylTensor_apply, riemannCurvatureTensor_apply, kulkarniNomizu_apply,
      innerₗ_apply_apply, Pi.sub_apply, Pi.add_apply]
  rw [hfun, mvfderiv_sub hRd (((h₁.add h₂).sub h₃).sub h₄), mvfderiv_sub ((h₁.add h₂).sub h₃) h₄,
    mvfderiv_sub (h₁.add h₂) h₃, mvfderiv_add h₁ h₂]
  simp only [_root_.sub_apply, _root_.add_apply,
    hcov.mvfderiv_schoutenTensor_mul_inner (hd U hU) (hd Z hZ) (hd V hV) (hd W hW),
    hcov.mvfderiv_schoutenTensor_mul_inner (hd V hV) (hd W hW) (hd U hU) (hd Z hZ),
    hcov.mvfderiv_schoutenTensor_mul_inner (hd U hU) (hd W hW) (hd V hV) (hd Z hZ),
    hcov.mvfderiv_schoutenTensor_mul_inner (hd V hV) (hd Z hZ) (hd U hU) (hd W hW),
    derivWeylTensor_apply, weylTensor_apply, riemannCurvatureTensor_apply, kulkarniNomizu_apply,
    innerₗ_apply_apply, hR]
  ring

/-- **The divergence of the Weyl tensor.** For a metric-compatible torsion-free connection in
dimension `n ≠ 2`, `∑ᵢ (∇_{eᵢ} W)(eᵢ, u, v, w) = (n - 3) C(u, v, w)` in any orthonormal basis,
where `C` is the Cotton tensor. -/
theorem IsMetricCompatible.sum_derivWeylTensor_self_eq_mul_cottonTensor {ι : Type*} [Fintype ι]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0)
    (hn : Module.finrank ℝ E ≠ 2) (x : M) (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (u v w : TangentSpace I x) :
    ∑ i, cov.derivWeylTensor x (b i) (b i) u v w =
      ((Module.finrank ℝ E : ℝ) - 3) * cov.cottonTensor x u v w := by
  have hn2 : (Module.finrank ℝ E : ℝ) - 2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hn)
  -- The divergence of `Rm`, by the contracted second Bianchi identity.
  have hR := hcov.sum_inner_derivCurvatureTensor_self_eq_sub ht x b u v w
  -- The divergence of `P`.
  have hdivP (z : TangentSpace I x) : ∑ i, cov.derivSchoutenTensor x (b i) z (b i) =
      ((Module.finrank ℝ E : ℝ) - 2)⁻¹ * (∑ i, cov.derivRicciTensor x (b i) z (b i) -
        mvfderiv I cov.scalarCurvature x z / (2 * ((Module.finrank ℝ E : ℝ) - 1))) := by
    simp only [hcov.derivSchoutenTensor_eq, ← Finset.mul_sum, Finset.sum_sub_distrib,
      div_mul_eq_mul_div, ← Finset.sum_div, b.sum_apply_mul_inner]
  -- The twice contracted second Bianchi identity, for the divergence of `Ric`.
  have h₁ := hcov.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature ht x b v
  have h₂ := hcov.two_mul_sum_derivRicciTensor_eq_mvfderiv_scalarCurvature ht x b w
  simp only [derivWeylTensor_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.sum_mul, hR, hdivP, b.sum_apply_mul_inner, cottonTensor_apply]
  simp only [hcov.derivSchoutenTensor_eq]
  by_cases hn1 : (Module.finrank ℝ E : ℝ) - 1 = 0
  · -- In dimension one the scalar curvature vanishes identically.
    have hzero : cov.scalarCurvature = 0 := funext fun y ↦
      cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero y
        (cov.curvatureTensor_eq_zero_of_finrank_le_one y (by
          rw [TauCeti.finrank_tangentSpace]
          exact_mod_cast (sub_eq_zero.mp hn1).le))
    simp only [hzero, mvfderiv_zero, _root_.zero_apply, zero_div, zero_mul, sub_zero] at h₁ h₂ ⊢
    field_simp
    linear_combination (inner ℝ u w * h₁ - inner ℝ u v * h₂) / 2
  · field_simp
    linear_combination ((Module.finrank ℝ E : ℝ) - 1) * (inner ℝ u w * h₁ - inner ℝ u v * h₂)

end CovariantDerivative
