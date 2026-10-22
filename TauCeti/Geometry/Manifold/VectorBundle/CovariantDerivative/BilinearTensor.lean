/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

-- Access metric compatibility's defining tensor equality without using the section-based
-- characterization, which requires an additional manifold regularity hypothesis.
import all Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

/-!
# The covariant derivative of a field of bilinear forms

Let `∇` be a covariant derivative on a vector bundle `V` and let `b` be a field of continuous
bilinear forms on the fibres of `V`. The covariant derivative of `b` is the tensor

`(∇_X b)(σ, τ) = X (b(σ, τ)) - b(∇_X σ, τ) - b(σ, ∇_X τ)`.

This file constructs it as a continuous trilinear map on each fibre, by the tensoriality criterion
`TensorialAt.mkHom₂`, whenever `b` pairs sections differentiable at the base point to a function
differentiable there. No symmetry, nondegeneracy or positivity of `b` is assumed: besides metrics
of any signature, this applies to the parameter derivative `h = ∂ₜ gₜ` of a family of metrics,
whose covariant derivative appears in the first variation of the Levi-Civita connection.

For the inner product of a Riemannian bundle the tensor is Mathlib's
`CovariantDerivative.derivMetricTensor`, whose vanishing defines metric compatibility.

## Main definitions and results

* `CovariantDerivative.derivBilinearTensor`: the covariant derivative `∇b` of a field of
  bilinear forms `b`, as a map `V x →L[ℝ] V x →L[ℝ] (T_x M →L[ℝ] ℝ)`.
* `CovariantDerivative.derivBilinearTensor_apply`: its value on differentiable sections.
* `CovariantDerivative.derivBilinearTensor_eq_zero_iff`: `∇b` vanishes exactly when `∇` satisfies
  the product rule `v (b(σ, τ)) = b(∇_v σ, τ) + b(σ, ∇_v τ)`.
* `CovariantDerivative.derivBilinearTensor_apply_comm`: `∇b` is symmetric when `b` is.
* `CovariantDerivative.derivBilinearTensor_eq_derivMetricTensor`: for the inner product of a
  Riemannian bundle, `∇b` is `CovariantDerivative.derivMetricTensor`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Ch. 4:
  covariant derivatives of tensor fields.
* `Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric`: the construction of
  `CovariantDerivative.derivMetricTensor`, generalized here from the inner product to an
  arbitrary differentiable field of bilinear forms.
-/

public section

open Bundle FiberBundle
open scoped Manifold ContDiff

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

section General

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  (cov : CovariantDerivative I F V)
  {b : (x : M) → V x →L[ℝ] V x →L[ℝ] ℝ} {σ τ : Π x : M, V x} {x : M}

/-- The function `(σ, τ) ↦ X (b(σ, τ)) - b(∇_X σ, τ) - b(σ, ∇_X τ)` on sections, with values in
the cotangent space at `x`; `CovariantDerivative.derivBilinearTensor` is the tensor it induces. -/
private def derivBilinearTensorAux (b : (x : M) → V x →L[ℝ] V x →L[ℝ] ℝ)
    (σ τ : Π x : M, V x) (x : M) : TangentSpace I x →L[ℝ] ℝ :=
  -- Transfer normability from the model fibre, so that `ContinuousLinearMap.flip` applies.
  letI := (VectorBundle.continuousLinearEquivAt ℝ F V x).isNormableSpace
  mvfderiv I (fun y ↦ b y (σ y) (τ y)) x - (b x).flip (τ x) ∘L cov σ x - b x (σ x) ∘L cov τ x

private theorem derivBilinearTensorAux_apply (σ τ : Π x : M, V x) (v : TangentSpace I x) :
    cov.derivBilinearTensorAux b σ τ x v =
      mvfderiv I (fun y ↦ b y (σ y) (τ y)) x v - b x (cov σ x v) (τ x) - b x (σ x) (cov τ x v) := by
  simp [derivBilinearTensorAux]

private theorem tensorialAt_derivBilinearTensorAux_left
    (hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    (hτ : MDiffAt (T% τ) x) :
    TensorialAt I F (cov.derivBilinearTensorAux b · τ x) x where
  smul {f σ} hf hσ := by
    ext v
    have hfσ : (fun y ↦ b y ((f • σ) y) (τ y)) = fun y ↦ f y * b y (σ y) (τ y) := by
      funext y; simp
    simp only [derivBilinearTensorAux_apply, hfσ, mvfderiv_fun_mul hf (hb hσ hτ),
      cov.isCovariantDerivativeOnUniv.leibniz hσ hf]
    simp [derivBilinearTensorAux_apply]
    ring
  add {σ σ'} hσ hσ' := by
    ext v
    have hsum : (fun y ↦ b y ((σ + σ') y) (τ y)) =
        fun y ↦ b y (σ y) (τ y) + b y (σ' y) (τ y) := by
      funext y; simp
    simp only [derivBilinearTensorAux_apply, hsum, mvfderiv_fun_add (hb hσ hτ) (hb hσ' hτ),
      cov.isCovariantDerivativeOnUniv.add hσ hσ']
    simp [derivBilinearTensorAux_apply]
    ring

private theorem tensorialAt_derivBilinearTensorAux_right
    (hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    (hσ : MDiffAt (T% σ) x) :
    TensorialAt I F (cov.derivBilinearTensorAux b σ · x) x where
  smul {f τ} hf hτ := by
    ext v
    have hfτ : (fun y ↦ b y (σ y) ((f • τ) y)) = fun y ↦ f y * b y (σ y) (τ y) := by
      funext y; simp
    simp only [derivBilinearTensorAux_apply, hfτ, mvfderiv_fun_mul hf (hb hσ hτ),
      cov.isCovariantDerivativeOnUniv.leibniz hτ hf]
    simp [derivBilinearTensorAux_apply]
    ring
  add {τ τ'} hτ hτ' := by
    ext v
    have hsum : (fun y ↦ b y (σ y) ((τ + τ') y)) =
        fun y ↦ b y (σ y) (τ y) + b y (σ y) (τ' y) := by
      funext y; simp
    simp only [derivBilinearTensorAux_apply, hsum, mvfderiv_fun_add (hb hσ hτ) (hb hσ hτ'),
      cov.isCovariantDerivativeOnUniv.add hτ hτ']
    simp [derivBilinearTensorAux_apply]
    ring

variable [ContMDiffVectorBundle 1 F V I] [FiniteDimensional ℝ F]

open scoped Classical in
/-- The **covariant derivative of a field of bilinear forms** `b` at `x`: the tensor
`(σ₀, τ₀, v) ↦ (∇_v b)(σ₀, τ₀)` determined by

`(∇_X b)(σ, τ) = X (b(σ, τ)) - b(∇_X σ, τ) - b(σ, ∇_X τ)`

on sections `σ`, `τ` differentiable at `x`, by `CovariantDerivative.derivBilinearTensor_apply`.
It is defined when `b` pairs sections differentiable at `x` to a function differentiable at `x`,
and is zero otherwise. -/
def derivBilinearTensor (b : (x : M) → V x →L[ℝ] V x →L[ℝ] ℝ) (x : M) :
    V x →L[ℝ] V x →L[ℝ] (TangentSpace I x →L[ℝ] ℝ) :=
  if hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x then
    TensorialAt.mkHom₂ (cov.derivBilinearTensorAux b · · x) x
      (fun _ ↦ cov.tensorialAt_derivBilinearTensorAux_left hb)
      (fun _ ↦ cov.tensorialAt_derivBilinearTensorAux_right hb)
  else 0

/-- The covariant derivative of a field of bilinear forms `b`, evaluated on sections
differentiable at `x`, is `(∇_v b)(σ, τ) = v (b(σ, τ)) - b(∇_v σ, τ) - b(σ, ∇_v τ)`. -/
theorem derivBilinearTensor_apply
    (hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) (v : TangentSpace I x) :
    cov.derivBilinearTensor b x (σ x) (τ x) v =
      mvfderiv I (fun y ↦ b y (σ y) (τ y)) x v - b x (cov σ x v) (τ x) -
        b x (σ x) (cov τ x v) := by
  rw [derivBilinearTensor, dite_eq_left hb, TensorialAt.mkHom₂_apply _ _ hσ hτ,
    derivBilinearTensorAux_apply]

/-- The covariant derivative of a field of bilinear forms `b` is zero at `x` when `b` does not pair
sections differentiable at `x` to a function differentiable at `x`. -/
theorem derivBilinearTensor_eq_zero_of_not
    (hb : ¬ ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x) :
    cov.derivBilinearTensor b x = 0 := by
  simp [derivBilinearTensor, hb]

/-- The covariant derivative of a field of bilinear forms `b`, evaluated on arbitrary vectors in
the fibre, through their extensions to sections by `FiberBundle.extend`. -/
theorem derivBilinearTensor_apply_eq_extend
    (hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x)
    (σ₀ τ₀ : V x) (v : TangentSpace I x) :
    cov.derivBilinearTensor b x σ₀ τ₀ v =
      mvfderiv I (fun y ↦ b y (extend F σ₀ y) (extend F τ₀ y)) x v -
        b x (cov (extend F σ₀) x v) τ₀ - b x σ₀ (cov (extend F τ₀) x v) := by
  simpa using cov.derivBilinearTensor_apply hb (mdifferentiableAt_extend I F σ₀)
    (mdifferentiableAt_extend I F τ₀) v

/-- The covariant derivative of a symmetric field of bilinear forms is symmetric in its two
fibre arguments. -/
theorem derivBilinearTensor_apply_comm (hsymm : ∀ y (v w : V y), b y v w = b y w v)
    (σ₀ τ₀ : V x) :
    cov.derivBilinearTensor b x σ₀ τ₀ = cov.derivBilinearTensor b x τ₀ σ₀ := by
  by_cases hb : ∀ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x
  · ext v
    have hpair : (fun y ↦ b y (extend F σ₀ y) (extend F τ₀ y)) =
        fun y ↦ b y (extend F τ₀ y) (extend F σ₀ y) :=
      funext fun y ↦ hsymm y _ _
    rw [cov.derivBilinearTensor_apply_eq_extend hb, cov.derivBilinearTensor_apply_eq_extend hb,
      hpair, hsymm x σ₀, hsymm x (cov (extend F σ₀) x v)]
    ring
  · simp [cov.derivBilinearTensor_eq_zero_of_not hb]

/-- The covariant derivative of a field of bilinear forms `b` vanishes everywhere exactly when `∇`
satisfies the product rule `v (b(σ, τ)) = b(∇_v σ, τ) + b(σ, ∇_v τ)` for all sections `σ`, `τ`
differentiable at the base point. -/
theorem derivBilinearTensor_eq_zero_iff
    (hb : ∀ x ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      MDiffAt (fun y ↦ b y (σ y) (τ y)) x) :
    (∀ x, cov.derivBilinearTensor b x = 0) ↔
      ∀ ⦃x : M⦄ ⦃σ τ : Π x : M, V x⦄, MDiffAt (T% σ) x → MDiffAt (T% τ) x →
        ∀ v : TangentSpace I x,
          mvfderiv I (fun y ↦ b y (σ y) (τ y)) x v =
            b x (cov σ x v) (τ x) + b x (σ x) (cov τ x v) := by
  refine ⟨fun h x σ τ hσ hτ v ↦ ?_, fun h x ↦ ?_⟩
  · have := congr($(h x) (σ x) (τ x) v)
    rw [cov.derivBilinearTensor_apply (hb x) hσ hτ] at this
    simp only [zero_apply] at this
    linarith
  · ext σ₀ τ₀ v
    rw [cov.derivBilinearTensor_apply_eq_extend (hb x),
      h (mdifferentiableAt_extend I F σ₀) (mdifferentiableAt_extend I F τ₀) v]
    simp

end General

section Riemannian

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle 1 F V I]
  [IsContMDiffRiemannianBundle I 1 F V] [FiniteDimensional ℝ F]
  (cov : CovariantDerivative I F V) {b : (x : M) → V x →L[ℝ] V x →L[ℝ] ℝ}

/-- For a field of bilinear forms given by the inner product of a `C¹` Riemannian bundle, the
covariant derivative is Mathlib's `CovariantDerivative.derivMetricTensor`. -/
theorem derivBilinearTensor_eq_derivMetricTensor (hb : ∀ x (v w : V x), b x v w = inner ℝ v w) :
    cov.derivBilinearTensor b = cov.derivMetricTensor := by
  have hpair (σ τ : Π x : M, V x) :
      (fun y ↦ b y (σ y) (τ y)) = fun y ↦ inner ℝ (σ y) (τ y) :=
    funext fun y ↦ hb y _ _
  funext x
  ext σ₀ τ₀ v
  rw [cov.derivBilinearTensor_apply_eq_extend (fun σ τ hσ hτ ↦ hpair σ τ ▸ hσ.inner_bundle hτ),
    derivMetricTensor_apply_eq_extend, hpair, hb, hb]

/-- A covariant derivative on a `C¹` Riemannian bundle is compatible with the metric exactly when
the covariant derivative of the inner product, viewed as a field of bilinear forms, vanishes. -/
theorem isMetricCompatible_iff_derivBilinearTensor_eq_zero
    (hb : ∀ x (v w : V x), b x v w = inner ℝ v w) :
    cov.IsMetricCompatible ↔ ∀ x, cov.derivBilinearTensor b x = 0 := by
  unfold CovariantDerivative.IsMetricCompatible
  rw [cov.derivBilinearTensor_eq_derivMetricTensor hb]
  exact ⟨fun h x ↦ congrFun h x, fun h ↦ funext h⟩

end Riemannian

end CovariantDerivative
