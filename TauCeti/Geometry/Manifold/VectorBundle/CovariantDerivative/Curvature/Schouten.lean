/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The Schouten tensor of a smooth connection

On a Riemannian manifold of dimension `n`, the Schouten tensor is the bilinear form

`P = (Ric - Scal g / (2 (n - 1))) / (n - 2)`.

It is the trace-adjusted Ricci tensor for which `Ric = (n - 2) P + (tr_g P) g`, and it is the
part of the curvature that the Weyl tensor leaves out: `Rm = W + P ⊙ g`. Under a conformal change
of metric it transforms by the Hessian of the conformal factor, which is why it governs conformal
geometry and the Yamabe problem.

As for `CovariantDerivative.ricciTensor` and `CovariantDerivative.scalarCurvature`, the definition
is made for any smooth connection on a Riemannian tangent bundle; symmetry of `P` needs a
metric-compatible torsion-free connection. The formulas involving `n - 2` assume `n ≠ 2`, the
dimensions in which the Schouten tensor is defined; in dimension `2` the definition divides by
zero and returns `0`.

## Main declarations

* `CovariantDerivative.schoutenTensor`: the Schouten tensor.
* `CovariantDerivative.bilinFormTrace_schoutenTensor`: `tr_g P = Scal / (2 (n - 1))`.
* `CovariantDerivative.ricciTensor_eq_smul_schoutenTensor_add`: `Ric = (n - 2) P + (tr_g P) g`.
* `CovariantDerivative.schoutenTensor_eq_of_curvatureTensor_eq_smul_inner_sub`: constant
  curvature `κ` gives `P = (κ / 2) g`.
* `CovariantDerivative.mdifferentiableAt_schoutenTensor_apply`: for a smooth metric, `P` pairs
  differentiable vector fields to differentiable functions.

## References

* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 2.
-/

public section

open Bundle
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

/-- The Schouten tensor `P = (Ric - Scal g / (2 (n - 1))) / (n - 2)` of a smooth connection on
a Riemannian tangent bundle of real dimension `n`. -/
def schoutenTensor (x : M) : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ :=
  ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 2)⁻¹ •
    (cov.ricciTensor x - (cov.scalarCurvature x /
      (2 * ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1))) • innerₗ (TangentSpace I x))

/-- Evaluation of the Schouten tensor. -/
@[simp]
theorem schoutenTensor_apply (x : M) (u v : TangentSpace I x) :
    cov.schoutenTensor x u v =
      ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 2)⁻¹ *
        (cov.ricciTensor x u v - cov.scalarCurvature x /
          (2 * ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1)) * inner ℝ u v) :=
  (rfl)

/-- The metric trace of the Schouten tensor is `Scal / (2 (n - 1))`, away from dimension `2`. -/
theorem bilinFormTrace_schoutenTensor (x : M)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2) :
    TauCeti.bilinFormTrace (cov.schoutenTensor x) =
      cov.scalarCurvature x / (2 * ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1)) := by
  -- `map_sub` is applied as a term: the subtraction in `schoutenTensor` uses the model-space
  -- instances of `TangentSpace I x`, which `rw` does not match against those of the metric.
  have hsub := map_sub TauCeti.bilinFormTrace (cov.ricciTensor x)
    ((cov.scalarCurvature x / (2 * ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1))) •
      innerₗ (TangentSpace I x))
  rw [map_smul, TauCeti.bilinFormTrace_inner, smul_eq_mul, ← scalarCurvature_apply] at hsub
  rw [schoutenTensor, map_smul, hsub, smul_eq_mul]
  have hn2 : (Module.finrank ℝ (TangentSpace I x) : ℝ) - 2 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hn)
  by_cases hn1 : Module.finrank ℝ (TangentSpace I x) = 1
  · -- In dimension one the curvature, hence the scalar curvature, vanishes.
    have hs : cov.scalarCurvature x = 0 :=
      cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x
        (cov.curvatureTensor_eq_zero_of_finrank_le_one x hn1.le)
    simp [hs]
  · have hn1' : (Module.finrank ℝ (TangentSpace I x) : ℝ) - 1 ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hn1)
    field_simp
    ring

/-- Away from dimension `2`, Ricci curvature decomposes as `Ric = (n - 2) P + (tr_g P) g` in
terms of the Schouten tensor `P`. -/
theorem ricciTensor_eq_smul_schoutenTensor_add (x : M)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2) :
    cov.ricciTensor x =
      ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 2) • cov.schoutenTensor x +
        TauCeti.bilinFormTrace (cov.schoutenTensor x) • innerₗ (TangentSpace I x) := by
  have hn2 : (Module.finrank ℝ (TangentSpace I x) : ℝ) - 2 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hn)
  ext u v
  rw [cov.bilinFormTrace_schoutenTensor x hn, LinearMap.add_apply, LinearMap.add_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    schoutenTensor_apply, innerₗ_apply_apply, smul_eq_mul, smul_eq_mul]
  field_simp
  ring

/-- The Schouten tensor of a metric-compatible torsion-free connection is a symmetric bilinear
form. -/
theorem IsMetricCompatible.schoutenTensor_isSymm
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0) (x : M) :
    (cov.schoutenTensor x).IsSymm :=
  ⟨fun u v ↦ by
    rw [RingHom.id_apply, schoutenTensor_apply, schoutenTensor_apply,
      IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht x u v, real_inner_comm u v]⟩

/-- The Schouten tensor of the constant-curvature model
`R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)` is `(κ / 2) g`, in dimension at least `3`. -/
theorem schoutenTensor_eq_of_curvatureTensor_eq_smul_inner_sub (x : M) (k : ℝ)
    (hn : 3 ≤ Module.finrank ℝ (TangentSpace I x))
    (h : ∀ w u v, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.schoutenTensor x = (k / 2) • innerₗ (TangentSpace I x) := by
  have hn' : (3 : ℝ) ≤ Module.finrank ℝ (TangentSpace I x) := by exact_mod_cast hn
  have hn2 : (Module.finrank ℝ (TangentSpace I x) : ℝ) - 2 ≠ 0 := by linarith
  have hn1 : (Module.finrank ℝ (TangentSpace I x) : ℝ) - 1 ≠ 0 := by linarith
  ext u v
  rw [schoutenTensor_apply, cov.ricciTensor_eq_of_curvatureTensor_eq_smul_inner_sub x k h,
    cov.scalarCurvature_eq_of_curvatureTensor_eq_smul_inner_sub x k h]
  simp only [LinearMap.smul_apply, innerₗ_apply_apply, smul_eq_mul]
  field_simp
  ring

/-- For a smooth metric, the Schouten tensor of a smooth connection pairs two vector fields
differentiable at `x` to a function differentiable at `x`. -/
theorem mdifferentiableAt_schoutenTensor_apply
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    {σ τ : Π x : M, TangentSpace I x} {x : M} (hσ : MDiffAt (T% σ) x) (hτ : MDiffAt (T% τ) x) :
    MDiffAt (fun y ↦ cov.schoutenTensor y (σ y) (τ y)) x := by
  simp only [schoutenTensor_apply, TauCeti.finrank_tangentSpace, div_eq_mul_inv]
  have hS : MDiffAt cov.scalarCurvature x :=
    cov.contMDiff_scalarCurvature.mdifferentiableAt (by simp)
  exact mdifferentiableAt_const.mul ((cov.mdifferentiableAt_ricciTensor_apply hσ hτ).sub
    ((hS.mul mdifferentiableAt_const).mul (TauCeti.Manifold.mdifferentiableAt_inner hσ hτ)))

end CovariantDerivative
