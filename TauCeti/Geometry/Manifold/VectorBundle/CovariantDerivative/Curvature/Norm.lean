/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Riemann
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Dual
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Bound

/-!
# The full norm of the Riemann curvature tensor

The Hilbert tensor product of four tangent spaces gives a basis-independent Hilbert–Schmidt
norm of the metric-lowered Riemann curvature tensor. Its square is the sum of all squared
coefficients in any orthonormal basis. The norm controls every four-vector evaluation and is
uniformly bounded on compact sets when the fibre metric is continuous.

The inner-product convention is `Rm(u, v, w, z) = ⟨R(u, v)w, z⟩`.

The normalization results are adapted from the formalizations in
[frenzymath/lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
[frenzymath/PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Bundle
open scoped ContDiff Manifold TensorProduct

noncomputable section

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- Cache the normed-space structure of the fourfold Hilbert tensor product, so that the
continuous-scalar-action search can reuse it. -/
local instance instNormedSpaceTensorFour (x : M) :
    NormedSpace ℝ ((TangentSpace I x ⊗[ℝ] TangentSpace I x) ⊗[ℝ]
      (TangentSpace I x ⊗[ℝ] TangentSpace I x)) := inferInstance

/-- The functional on the fourfold Hilbert tensor product induced by the Riemann tensor. -/
private def riemannTensorLinear (x : M) :
    ((TangentSpace I x ⊗[ℝ] TangentSpace I x) ⊗[ℝ]
      (TangentSpace I x ⊗[ℝ] TangentSpace I x)) →ₗ[ℝ] ℝ :=
  TensorProduct.lift
    ((TensorProduct.lift.equiv (RingHom.id ℝ) _ _ ℝ).toLinearMap.comp
      (TensorProduct.lift (cov.riemannCurvatureTensor x)))

/-- The tensor-product functional agrees with the original tensor on pure tensors. -/
private theorem riemannTensorLinear_tmul (x : M) (u v w z : TangentSpace I x) :
    cov.riemannTensorLinear x ((u ⊗ₜ[ℝ] v) ⊗ₜ[ℝ] (w ⊗ₜ[ℝ] z)) =
      cov.riemannCurvatureTensor x u v w z := by
  simp [riemannTensorLinear]

/-- The full Hilbert–Schmidt norm of the metric-lowered Riemann curvature tensor. -/
def riemannCurvatureNorm (x : M) : ℝ :=
  ‖(cov.riemannTensorLinear x).toContinuousLinearMap‖

/-- The full Riemann curvature norm is nonnegative. -/
theorem riemannCurvatureNorm_nonneg (x : M) : 0 ≤ cov.riemannCurvatureNorm x :=
  norm_nonneg _

/-- The square of the full Riemann curvature norm is the sum of all squared coefficients in any
orthonormal basis. -/
theorem riemannCurvatureNorm_sq_eq_sum {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) :
    cov.riemannCurvatureNorm x ^ 2 = ∑ i, ∑ j, ∑ k, ∑ l,
      (cov.riemannCurvatureTensor x (b i) (b j) (b k) (b l)) ^ 2 := by
  let e := (b.tensorProduct b).tensorProduct (b.tensorProduct b)
  simpa only [riemannCurvatureNorm, Fintype.sum_prod_type, e,
    OrthonormalBasis.tensorProduct_apply, LinearMap.coe_toContinuousLinearMap',
    riemannTensorLinear_tmul] using e.norm_dual (cov.riemannTensorLinear x).toContinuousLinearMap

/-- The full Riemann curvature norm controls every four-vector evaluation. -/
theorem abs_riemannCurvatureTensor_le (x : M) (u v w z : TangentSpace I x) :
    |cov.riemannCurvatureTensor x u v w z| ≤
      cov.riemannCurvatureNorm x * ‖u‖ * ‖v‖ * ‖w‖ * ‖z‖ := by
  have h := (cov.riemannTensorLinear x).toContinuousLinearMap.le_opNorm
    ((u ⊗ₜ[ℝ] v) ⊗ₜ[ℝ] (w ⊗ₜ[ℝ] z))
  simpa only [LinearMap.coe_toContinuousLinearMap', riemannTensorLinear_tmul,
    Real.norm_eq_abs, TensorProduct.norm_tmul, riemannCurvatureNorm, mul_assoc] using h

/-- A uniform bound `C` on orthonormal coefficients bounds the full norm by `n² C`, where
`n` is the dimension of the tangent space. -/
theorem riemannCurvatureNorm_le_of_bound {ι : Type*} [Fintype ι] (x : M)
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) {C : ℝ}
    (hR : ∀ i j k l,
      |cov.riemannCurvatureTensor x (b i) (b j) (b k) (b l)| ≤ C) :
    cov.riemannCurvatureNorm x ≤ (Fintype.card ι : ℝ) ^ 2 * C := by
  cases isEmpty_or_nonempty ι with
  | inl hι =>
    have hsq := cov.riemannCurvatureNorm_sq_eq_sum x b
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at hsq
    have hnorm : cov.riemannCurvatureNorm x = 0 := sq_eq_zero_iff.mp hsq
    simp [hnorm]
  | inr hι =>
    obtain ⟨i⟩ := hι
    have hC : 0 ≤ C := (abs_nonneg _).trans (hR i i i i)
    apply (sq_le_sq₀ (cov.riemannCurvatureNorm_nonneg x)
      (mul_nonneg (sq_nonneg _) hC)).mp
    rw [cov.riemannCurvatureNorm_sq_eq_sum x b]
    calc
      _ ≤ ∑ _i : ι, ∑ _j : ι, ∑ _k : ι, ∑ _l : ι, C ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦
          Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun l _ ↦ ?_
        exact sq_le_sq.mpr ((hR i j k l).trans_eq (abs_of_nonneg hC).symm)
      _ = _ := by simp; ring

variable [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]

/-- The full Riemann curvature norm of a smooth connection is uniformly bounded on every compact
set when the tangent metric is continuous. -/
theorem exists_riemannCurvatureNorm_le_of_isCompact {K : Set M} (hK : IsCompact K) :
    ∃ C > 0, ∀ x ∈ K, cov.riemannCurvatureNorm x ≤ C := by
  obtain ⟨C, hC⟩ := cov.exists_norm_curvatureTensor_le_of_isCompact
    (I := I) (F := E) (V := TangentSpace I) hK
  refine ⟨(Module.finrank ℝ E : ℝ) ^ 2 * max C 0 + 1, by positivity, ?_⟩
  intro x hx
  let b := stdOrthonormalBasis ℝ (TangentSpace I x)
  have hcoeff i j k l :
      |cov.riemannCurvatureTensor x (b i) (b j) (b k) (b l)| ≤ max C 0 := by
    rw [riemannCurvatureTensor_apply]
    calc
      _ ≤ ‖cov.curvatureTensor x (b i) (b j) (b k)‖ * ‖b l‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ C * ‖b i‖ * ‖b j‖ * ‖b k‖ * ‖b l‖ :=
        mul_le_mul_of_nonneg_right (hC x hx _ _ _) (norm_nonneg _)
      _ = C := by simp only [b.orthonormal.1, mul_one]
      _ ≤ max C 0 := le_max_left _ _
  have hb := cov.riemannCurvatureNorm_le_of_bound x b hcoeff
  have hbound : cov.riemannCurvatureNorm x ≤ (Module.finrank ℝ E : ℝ) ^ 2 * max C 0 := by
    simpa only [Fintype.card_fin, VectorBundle.finrank_eq ℝ E (TangentSpace I) x] using hb
  linarith

end CovariantDerivative
