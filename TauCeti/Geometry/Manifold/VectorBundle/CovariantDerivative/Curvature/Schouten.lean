/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Scalar.Basic
import TauCeti.Analysis.InnerProductSpace.AlgebraicCurvature.Schouten
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.FourTensor.Basic

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
* `CovariantDerivative.schoutenTensor_eq_zero_of_curvatureTensor_eq_zero`: zero curvature gives
  `P = 0`.
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
  TauCeti.FourTensor.schouten (cov.curvatureFourTensor x)

/-- Evaluation of the Schouten tensor. -/
@[simp]
theorem schoutenTensor_apply (x : M) (u v : TangentSpace I x) :
    cov.schoutenTensor x u v =
      ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 2)⁻¹ *
        (cov.ricciTensor x u v - cov.scalarCurvature x /
          (2 * ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1)) * inner ℝ u v) := by
  rw [schoutenTensor, TauCeti.FourTensor.schouten_apply_apply,
    cov.ricci_curvatureFourTensor, cov.scalar_curvatureFourTensor]

/-- The metric trace of the Schouten tensor is `Scal / (2 (n - 1))`, away from dimension `2`. -/
theorem bilinFormTrace_schoutenTensor (x : M)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2) :
    TauCeti.bilinFormTrace (cov.schoutenTensor x) =
      cov.scalarCurvature x / (2 * ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 1)) := by
  rw [schoutenTensor, ← cov.scalar_curvatureFourTensor x]
  exact TauCeti.FourTensor.bilinFormTrace_schouten hn fun hn1 ↦ by
    rw [cov.scalar_curvatureFourTensor]
    exact cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x
      (cov.curvatureTensor_eq_zero_of_finrank_le_one x hn1.le)

/-- Away from dimension `2`, Ricci curvature decomposes as `Ric = (n - 2) P + (tr_g P) g` in
terms of the Schouten tensor `P`. -/
theorem ricciTensor_eq_smul_schoutenTensor_add (x : M)
    (hn : Module.finrank ℝ (TangentSpace I x) ≠ 2) :
    cov.ricciTensor x =
      ((Module.finrank ℝ (TangentSpace I x) : ℝ) - 2) • cov.schoutenTensor x +
        TauCeti.bilinFormTrace (cov.schoutenTensor x) • innerₗ (TangentSpace I x) := by
  rw [← cov.ricci_curvatureFourTensor x, schoutenTensor]
  exact TauCeti.FourTensor.ricci_eq_smul_schouten_add hn fun hn1 ↦ by
    rw [cov.scalar_curvatureFourTensor]
    exact cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x
      (cov.curvatureTensor_eq_zero_of_finrank_le_one x hn1.le)

/-- The Schouten tensor of a metric-compatible torsion-free connection is a symmetric bilinear
form. -/
theorem IsMetricCompatible.schoutenTensor_isSymm
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
    (hcov : CovariantDerivative.IsMetricCompatible
      (V := fun y : M ↦ TangentSpace I y) cov) (ht : cov.torsion = 0) (x : M) :
    (cov.schoutenTensor x).IsSymm := by
  rw [schoutenTensor]
  exact LinearMap.BilinForm.isSymm_iff.mp <|
    TauCeti.FourTensor.isSymm_schouten_of_isSymm_ricci <|
      LinearMap.BilinForm.isSymm_iff.mpr <| by
        rw [cov.ricci_curvatureFourTensor x]
        exact hcov.ricciTensor_isSymm cov ht x

/-- A point with zero curvature tensor has zero Schouten tensor. -/
theorem schoutenTensor_eq_zero_of_curvatureTensor_eq_zero (x : M) (h : curvature x = 0) :
    cov.schoutenTensor x = 0 := by
  ext u v
  simp [cov.ricciTensor_eq_zero_of_curvatureTensor_eq_zero x h,
    cov.scalarCurvature_eq_zero_of_curvatureTensor_eq_zero x h]

/-- The Schouten tensor of the constant-curvature model
`R(w,u)v = κ (⟨u,v⟩ w - ⟨w,v⟩ u)` is `(κ / 2) g`, in dimension at least `3`. -/
theorem schoutenTensor_eq_of_curvatureTensor_eq_smul_inner_sub (x : M) (k : ℝ)
    (hn : 3 ≤ Module.finrank ℝ (TangentSpace I x))
    (h : ∀ w u v, curvature x w u v =
      k • (inner ℝ u v • w - inner ℝ w v • u)) :
    cov.schoutenTensor x = (k / 2) • innerₗ (TangentSpace I x) := by
  have hcurv : cov.curvatureFourTensor x =
      k • TauCeti.FourTensor.constantCurvature (TangentSpace I x) :=
    TauCeti.FourTensor.ext_vec fun u v z w ↦ by
      rw [cov.curvatureFourTensor_apply, smul_apply, smul_eq_mul]
      exact TauCeti.FourTensor.inner_eq_mul_constantCurvature h u v z w
  rw [schoutenTensor, hcurv, map_smul, TauCeti.FourTensor.schouten_constantCurvature hn,
    smul_smul, mul_one_div]

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

/-- For a smooth metric, the Schouten tensor of a smooth connection pairs two vector fields that
are `C^∞` at `x` to a function that is `C^∞` at `x`. -/
theorem contMDiffAt_schoutenTensor_apply
    [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)]
    {σ τ : Π x : M, TangentSpace I x} {x : M} (hσ : CMDiffAt ∞ (T% σ) x)
    (hτ : CMDiffAt ∞ (T% τ) x) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y ↦ cov.schoutenTensor y (σ y) (τ y)) x := by
  simp only [schoutenTensor_apply, TauCeti.finrank_tangentSpace, div_eq_mul_inv]
  exact contMDiffAt_const.mul ((cov.contMDiffAt_ricciTensor_apply hσ hτ).sub
    ((cov.contMDiff_scalarCurvature.contMDiffAt.mul contMDiffAt_const).mul
      (ContMDiffAt.inner_bundle (IB := I) (F := E) (E := fun x : M ↦ TangentSpace I x)
        (b := id) hσ hτ)))

end CovariantDerivative
