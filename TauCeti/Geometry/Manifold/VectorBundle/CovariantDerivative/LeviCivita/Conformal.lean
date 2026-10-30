/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.ChainRule
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# The Levi-Civita connection under a conformal change of metric

Let `g` be a Riemannian metric on `M` and `f` a positive function, and let `ĝ = f g` be the
conformally rescaled metric `Bundle.ContMDiffRiemannianMetric.rescale`. The Levi-Civita
connections of `g` and `ĝ` differ by the tensor

`A(Y, X) = (2 f)⁻¹ (df(X) Y + df(Y) X - g(X, Y) grad_g f)`,

that is, `∇^ĝ_X Y = ∇^g_X Y + A(Y, X)` for every vector field `Y` differentiable at the point.
Writing `f = e^(2φ)`, this is the classical formula
`∇^ĝ_X Y = ∇^g_X Y + dφ(X) Y + dφ(Y) X - g(X, Y) grad_g φ`. It is the first-order input for the
transformation laws of curvature under conformal change, and hence for the conformal Laplacian.
For the metrics `u ^ p g` of the Yamabe problem, with `p = 4 / (n - 2)`, the tensor is `p` times
the tensor of `u` (`TauCeti.Manifold.conformalConnectionTensor_rpow`).

The tensor `A` is built from `g` alone and the difference is added to a connection with Mathlib's
`CovariantDerivative.addOneForm`. Adding `A` to a Levi-Civita connection of `g` gives a
torsion-free connection, since `A` is symmetric, compatible with `f g`, by a direct computation
with the product rule. Uniqueness of the Levi-Civita connection on differentiable vector fields,
`CovariantDerivative.IsLeviCivitaConnection.uniqueness`, then identifies it with Mathlib's
Levi-Civita connection of `f g`. As in
`TauCeti.Geometry.Manifold.Riemannian.Scaling`, connections do not depend on a metric, so each
metric is installed in turn as the `RiemannianBundle` instance of the tangent bundle of `M` and
the connections are compared directly on `M`.

## Main definitions and results

* `TauCeti.Manifold.conformalConnectionTensor`: the tensor `A` above, for the metric of the
  `RiemannianBundle` instance; `TauCeti.Manifold.conformalConnectionTensor_apply` evaluates it,
  and `TauCeti.Manifold.inner_conformalConnectionTensor` pairs it with a third vector.
* `TauCeti.Manifold.trace_conformalConnectionTensor`: its trace in the direction of
  differentiation is `(N / 2) f⁻¹ df` in real dimension `N`.
* `TauCeti.Manifold.contMDiff_conformalConnectionTensor_apply`: evaluated on `C^n` vector fields,
  the tensor of a nowhere vanishing `C^(n + 1)` function is a `C^n` vector field.
* `TauCeti.Manifold.conformalConnectionTensor_rpow`: the tensor of `u ^ p` is `p` times the
  tensor of `u`.
* `Bundle.ContMDiffRiemannianMetric.isLeviCivitaConnection_rescale_addOneForm`: adding the tensor
  of `f` to a Levi-Civita connection of `g` gives a Levi-Civita connection of `f g`.
* `Bundle.ContMDiffRiemannianMetric.leviCivitaConnection_rescale_apply`: the Levi-Civita
  connection of `f g` is that of `g` plus the tensor of `f`, on differentiable vector fields.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.J.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), 37–91,
  Section 2.
-/

public section

open Bundle
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I) in
/-- The difference between the Levi-Civita connections of the metric `g` of the
`RiemannianBundle` instance and of its conformal rescaling `f g`:
`A(v, w) = (2 f)⁻¹ (df(w) v + df(v) w - ⟪v, w⟫ grad f)`. As for
`CovariantDerivative.addOneForm`, the first argument `v` is the value of the vector field being
differentiated and the second argument `w` is the direction of differentiation. -/
def conformalConnectionTensor (f : M → ℝ) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x :=
  (2 * f x)⁻¹ • (ContinuousLinearMap.smulRightL ℝ _ _ (mvfderiv I f x) +
    (mvfderiv I f x).smulRight (ContinuousLinearMap.id ℝ (TangentSpace I x)) -
    ContinuousLinearMap.compL ℝ _ ℝ _ (ContinuousLinearMap.toSpanSingleton ℝ (mgradient I f x)) ∘L
      innerSL ℝ (E := TangentSpace I x))

@[simp]
theorem conformalConnectionTensor_apply (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    conformalConnectionTensor I f x v w =
      (2 * f x)⁻¹ • (mvfderiv I f x w • v + mvfderiv I f x v • w -
        inner ℝ v w • mgradient I f x) := by
  simp only [conformalConnectionTensor, smul_apply, sub_apply, add_apply,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.toSpanSingleton_apply]
  -- `simp` does not match `innerSL_apply_apply` up to the instances of the Riemannian bundle.
  rw [innerSL_apply_apply]

/-- The conformal connection tensor is symmetric, which is why the conformally changed
connection stays torsion free. -/
theorem conformalConnectionTensor_comm (f : M → ℝ) (x : M) (v w : TangentSpace I x) :
    conformalConnectionTensor I f x v w = conformalConnectionTensor I f x w v := by
  rw [conformalConnectionTensor_apply, conformalConnectionTensor_apply, real_inner_comm,
    add_comm (mvfderiv I f x w • v)]

/-- The pairing of the conformal connection tensor with a third vector:
`⟪A(v, w), z⟫ = (2 f)⁻¹ (df(w) ⟪v, z⟫ + df(v) ⟪w, z⟫ - df(z) ⟪v, w⟫)`. -/
theorem inner_conformalConnectionTensor (f : M → ℝ) (x : M) (v w z : TangentSpace I x) :
    inner ℝ (conformalConnectionTensor I f x v w) z =
      (2 * f x)⁻¹ * (mvfderiv I f x w * inner ℝ v z + mvfderiv I f x v * inner ℝ w z -
        mvfderiv I f x z * inner ℝ v w) := by
  simp only [conformalConnectionTensor_apply, real_inner_smul_left, inner_sub_left,
    inner_add_left, inner_mgradient]
  ring

/-- The trace of the conformal connection tensor in the direction of differentiation:
`tr (w ↦ A(v, w)) = (N / 2) f⁻¹ df(v)` in real dimension `N`. This is the change of the divergence
under conformal change of the metric. -/
theorem trace_conformalConnectionTensor (f : M → ℝ) (x : M) (v : TangentSpace I x) :
    LinearMap.trace ℝ (TangentSpace I x) (conformalConnectionTensor I f x v).toLinearMap =
      (Module.finrank ℝ E / 2) * (f x)⁻¹ * mvfderiv I f x v := by
  have h : (conformalConnectionTensor I f x v).toLinearMap =
      (2 * f x)⁻¹ • ((mvfderiv I f x).toLinearMap.smulRight v +
        mvfderiv I f x v • LinearMap.id -
          (innerSL ℝ v).toLinearMap.smulRight (mgradient I f x)) := by
    ext w
    simp [conformalConnectionTensor_apply]
  rw [h]
  simp only [map_smul, map_add, map_sub, LinearMap.trace_smulRight, LinearMap.trace_id,
    ContinuousLinearMap.coe_coe, innerSL_apply_apply, smul_eq_mul]
  -- `TangentSpace I x` is the model space `E`, with the same real module structure.
  rw [real_inner_comm, inner_mgradient,
    show Module.finrank ℝ (TangentSpace I x) = Module.finrank ℝ E from rfl]
  field_simp
  ring

/-- The conformal connection tensor of a nowhere vanishing `C^(n + 1)` function, evaluated on two
`C^n` vector fields, is a `C^n` vector field for a `C^n` metric. -/
theorem contMDiff_conformalConnectionTensor_apply {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)] {f : M → ℝ}
    (hf : ContMDiff I 𝓘(ℝ) (n + 1) f) (hf₀ : ∀ x, f x ≠ 0)
    {Y Z : Π x : M, TangentSpace I x} (hY : CMDiff n (T% Y)) (hZ : CMDiff n (T% Z)) :
    CMDiff n (T% (fun y ↦ conformalConnectionTensor I f y (Y y) (Z y))) := by
  have hgrad := contMDiff_mgradient (I := I) hf
  -- The bundle argument of `ContMDiff.inner_bundle` is not inferred through `TangentSpace`.
  have hinner {U W : Π x : M, TangentSpace I x} (hU : CMDiff n (T% U)) (hW : CMDiff n (T% W)) :
      ContMDiff I 𝓘(ℝ) n (fun y ↦ inner ℝ (U y) (W y)) :=
    ContMDiff.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x) (b := id) hU hW
  -- Write the tensor through the gradient, `df(v) = ⟪grad f, v⟫`, and combine smooth sections.
  refine (((contMDiff_const.mul (hf.of_le le_self_add)).inv₀ fun y ↦
      mul_ne_zero two_ne_zero (hf₀ y)).smul_section
    ((((hinner hgrad hZ).smul_section hY).add_section
      ((hinner hgrad hY).smul_section hZ)).sub_section
        ((hinner hY hZ).smul_section hgrad))).congr fun y ↦ ?_
  simp [conformalConnectionTensor_apply, inner_mgradient]

/-- The conformal connection tensor of a real power `u ^ p` of a positive function is `p` times
that of `u`. For `p = 4 / (n - 2)` this is the conformal factor of the Yamabe problem. -/
theorem conformalConnectionTensor_rpow {u : M → ℝ} {x : M} (hu : MDiffAt u x) (hux : 0 < u x)
    (p : ℝ) :
    conformalConnectionTensor I (fun y ↦ u y ^ p) x = p • conformalConnectionTensor I u x := by
  have hgrad : mgradient I (fun y ↦ u y ^ p) x = (p * u x ^ (p - 1)) • mgradient I u x :=
    mgradient_comp_hasDerivAt (f := u) (Real.hasDerivAt_rpow_const (Or.inl hux.ne')) hu
  have hd : ∀ v, mvfderiv I (fun y ↦ u y ^ p) x v = p * u x ^ (p - 1) * mvfderiv I u x v := by
    intro v
    rw [← inner_mgradient, hgrad, real_inner_smul_left, inner_mgradient]
  ext v w
  simp only [conformalConnectionTensor_apply, smul_apply, hd, hgrad, Real.rpow_sub_one hux.ne']
  match_scalars <;> field_simp

/-- The conformal connection tensor of an exponential factor `e^(2φ)` is the classical tensor
`A(v, w) = dφ(w) v + dφ(v) w - ⟪v, w⟫ grad φ` of the conformal change `e^(2φ) g`. -/
theorem conformalConnectionTensor_exp_two_mul_apply {φ : M → ℝ} {x : M} (hφ : MDiffAt φ x)
    (v w : TangentSpace I x) :
    conformalConnectionTensor I (fun y ↦ Real.exp (2 * φ y)) x v w =
      mvfderiv I φ x w • v + mvfderiv I φ x v • w - inner ℝ v w • mgradient I φ x := by
  have hgrad : mgradient I (fun y ↦ Real.exp (2 * φ y)) x =
      (Real.exp (2 * φ x) * 2) • mgradient I φ x :=
    mgradient_comp_hasDerivAt (f := φ) (g := fun t ↦ Real.exp (2 * t))
      (by simpa using ((hasDerivAt_id (φ x)).const_mul 2).exp) hφ
  have hd : ∀ v, mvfderiv I (fun y ↦ Real.exp (2 * φ y)) x v =
      Real.exp (2 * φ x) * 2 * mvfderiv I φ x v := by
    intro v
    rw [← inner_mgradient, hgrad, real_inner_smul_left, inner_mgradient]
  simp only [conformalConnectionTensor_apply, hd, hgrad]
  match_scalars <;> field_simp

end TauCeti.Manifold

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M] {n : ℕ∞ω}

/-- **Conformal change of the Levi-Civita connection.** If `∇` is a Levi-Civita connection of a
`C¹` metric `g`, then `∇ + A` is a Levi-Civita connection of `f g` for every positive function
`f` of the same regularity, where `A` is the conformal connection tensor of `f` for `g`. -/
theorem isLeviCivitaConnection_rescale_addOneForm
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {cov : CovariantDerivative I E (fun x : M ↦ TangentSpace I x)}
    (hcov : letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      cov.IsLeviCivitaConnection) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
    letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    (cov.addOneForm (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨g.toRiemannianMetric⟩; conformalConnectionTensor I f)).IsLeviCivitaConnection := by
  -- Unpack the hypothesis on `cov`, which does not mention the metric of `f g`.
  have hc := (isMetricCompatible_iff_inner g hn cov).1 (by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact hcov.isMetricCompatible)
  have ht : cov.torsion = 0 := by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact hcov.torsion
  set A := (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
    conformalConnectionTensor I f)
  -- The pairings of `A` with a third vector, written with the inner products of `g`.
  have hA : ∀ (x : M) (v w z : TangentSpace I x), g.inner x (A x v w) z =
      (2 * f x)⁻¹ * (mvfderiv I f x w * g.inner x v z + mvfderiv I f x v * g.inner x w z -
        mvfderiv I f x z * g.inner x v w) := by
    intro x v w z
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    exact inner_conformalConnectionTensor f x v w z
  have hA' : ∀ (x : M) (v w z : TangentSpace I x), g.inner x z (A x v w) =
      (2 * f x)⁻¹ * (mvfderiv I f x w * g.inner x v z + mvfderiv I f x v * g.inner x w z -
        mvfderiv I f x z * g.inner x v w) := fun x v w z ↦ by rw [g.symm, hA]
  -- Compatibility with `f g`: the product rule for `f g(σ, τ)` against compatibility with `g`.
  have hm : ∀ ⦃x : M⦄ ⦃X σ τ : Π x : M, TangentSpace I x⦄,
      MDiffAt (T% X) x → MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      mvfderiv I (fun y ↦ (g.rescale f hf hf_pos).inner y (σ y) (τ y)) x (X x) =
        (g.rescale f hf hf_pos).inner x ((cov.addOneForm A) σ x (X x)) (τ x) +
          (g.rescale f hf hf_pos).inner x (σ x) ((cov.addOneForm A) τ x (X x)) := by
    intro x X σ τ hX hσ hτ
    have hg : MDiffAt (fun y ↦ g.inner y (σ y) (τ y)) x := by
      let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn
      exact mdifferentiableAt_inner hσ hτ
    have hfx : MDiffAt f x := hf.mdifferentiableAt (one_pos.trans_le hn).ne'
    simp only [rescale_inner]
    rw [mvfderiv_fun_mul hfx hg]
    simp only [CovariantDerivative.addOneForm, add_apply, map_add, hA, hA', hc hX hσ hτ,
      smul_apply, smul_eq_mul]
    field_simp [(hf_pos x).ne']
    linear_combination mvfderiv I f x (X x) * g.symm x (σ x) (τ x) -
      mvfderiv I f x (σ x) * g.symm x (X x) (τ x) + mvfderiv I f x (τ x) * g.symm x (σ x) (X x)
  -- Torsion-freeness: `A` is symmetric.
  have htA : (cov.addOneForm A).torsion = 0 := by
    rw [CovariantDerivative.torsion_eq_zero_iff]
    intro X Y x hX hY
    simp only [CovariantDerivative.addOneForm, add_apply]
    rw [← cov.torsion_eq_zero_iff.1 ht hX hY]
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    rw [conformalConnectionTensor_comm f x (Y x)]
    abel
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  exact ⟨(isMetricCompatible_iff_inner _ hn _).2 hm, htA⟩

/-- **Levi-Civita connection under conformal change.** For a positive function `f`, the
Levi-Civita connection of `f g` is the Levi-Civita connection of `g` plus the conformal connection
tensor of `f`, `∇^(f g)_v Y = ∇^g_v Y + (2 f)⁻¹ (df(v) Y + df(Y) v - g(Y, v) grad_g f)`, on every
vector field `Y` differentiable at the point. -/
theorem leviCivitaConnection_rescale_apply
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)) (hn : 1 ≤ n)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) n f) (hf_pos : ∀ x, 0 < f x)
    {Y : Π x : M, TangentSpace I x} {x : M} (hY : MDiffAt (T% Y) x) (v : TangentSpace I x) :
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
        ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M Y x v) =
    (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M Y x v +
        conformalConnectionTensor I f x (Y x) v) := by
  have h := isLeviCivitaConnection_rescale_addOneForm g hn hf hf_pos
    (cov := letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
      letI : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
        IsContMDiffRiemannianBundle.of_le hn;
      CovariantDerivative.leviCivitaConnection I M) (by
    let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
      IsContMDiffRiemannianBundle.of_le hn
    exact CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I)
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
    ⟨(g.rescale f hf hf_pos).toRiemannianMetric⟩
  let _ : IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x) :=
    IsContMDiffRiemannianBundle.of_le hn
  refine ((CovariantDerivative.isLeviCivitaConnection_leviCivitaConnection I).uniqueness I h hY
    v).trans ?_
  simp only [CovariantDerivative.addOneForm, add_apply]

end Bundle.ContMDiffRiemannianMetric
