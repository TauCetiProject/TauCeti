/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci

/-!
# Quadratic Ricci and curvature contractions

The metric trace of `R(u, ·) ·` is the vector dual to Ricci. Applying a bilinear form to
that trace identifies the metric-variation correction in the fixed-input Ricci evolution.
The contraction of curvature with a symmetric bilinear form is symmetric in its two
uncontracted arguments.

## References

* P. Topping, *Lectures on the Ricci Flow*, CUP (2006), §2.5.
* [Poincaré Conjecture](https://github.com/frenzymath/PoincareConjecture).
* [Lean evaluation submissions](https://github.com/frenzymath/lean-eval-submissions).
-/

public noncomputable section

open Bundle
open scoped ContDiff Manifold RealInnerProductSpace

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I 2 E (fun x : M ↦ TangentSpace I x)]
  {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [ContMDiffCovariantDerivative cov ∞]

/-- The metric trace of `R(u, ·) ·`, paired with a vector, is Ricci curvature. -/
theorem IsMetricCompatible.sum_inner_curvatureTensor_self_eq_ricciTensor
    (hcov : CovariantDerivative.IsMetricCompatible (V := (TangentSpace I : M → Type _)) cov)
    (ht : cov.torsion = 0) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    (∑ i, inner ℝ (cov.curvatureTensor x u (b i) (b i)) v) = cov.ricciTensor x u v := by
  rw [IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht x u v,
    cov.ricciTensor_eq_sum_inner x b v u]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [hcov.inner_curvatureTensor_swap_pairs ht]
  exact real_inner_comm _ _

/-- Contracting the vector-valued curvature trace against a bilinear form gives its
coefficient pairing with Ricci. The bilinear form need not be symmetric. -/
theorem IsMetricCompatible.sum_bilinear_curvatureTensor_self_eq_sum_mul
    (hcov : CovariantDerivative.IsMetricCompatible (V := (TangentSpace I : M → Type _)) cov)
    (ht : cov.torsion = 0) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ) (u v : TangentSpace I x) :
    (∑ i, B (cov.curvatureTensor x u (b i) (b i)) v) =
      ∑ j, cov.ricciTensor x u (b j) * B (b j) v := by
  calc
    _ = ∑ i, ∑ j, inner ℝ (b j) (cov.curvatureTensor x u (b i) (b i)) * B (b j) v := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      nth_rw 1 [← b.sum_repr' (cov.curvatureTensor x u (b i) (b i))]
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Finset.sum_mul]
      have hc : (∑ i, inner ℝ (b j) (cov.curvatureTensor x u (b i) (b i))) =
          cov.ricciTensor x u (b j) := by
        calc
          _ = ∑ i, inner ℝ (cov.curvatureTensor x u (b i) (b i)) (b j) :=
            Finset.sum_congr rfl fun i _ ↦ real_inner_comm _ _
          _ = _ := hcov.sum_inner_curvatureTensor_self_eq_ricciTensor ht x b u (b j)
      rw [hc]

/-- Contracting curvature with a symmetric bilinear form leaves a symmetric two-tensor. -/
theorem IsMetricCompatible.sum_mul_inner_curvatureTensor_comm
    (hcov : CovariantDerivative.IsMetricCompatible (V := (TangentSpace I : M → Type _)) cov)
    (ht : cov.torsion = 0) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x))
    (B : TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ)
    (hB : ∀ p q, B p q = B q p) (u v : TangentSpace I x) :
    (∑ i, ∑ j, B (b i) (b j) * inner ℝ (cov.curvatureTensor x u (b i) (b j)) v) =
      ∑ i, ∑ j, B (b i) (b j) * inner ℝ (cov.curvatureTensor x v (b i) (b j)) u := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [hB (b j) (b i), hcov.inner_curvatureTensor_swap_pairs ht,
    cov.curvatureTensor_antisymm x (b i) v]
  simp only [LinearMap.neg_apply, inner_neg_left]
  rw [hcov.inner_curvatureTensor_eq_neg]
  simp only [neg_neg, real_inner_comm]

/-- The coefficient square of Ricci is symmetric in its uncontracted inputs. -/
theorem IsMetricCompatible.sum_ricciTensor_mul_comm
    (hcov : CovariantDerivative.IsMetricCompatible (V := (TangentSpace I : M → Type _)) cov)
    (ht : cov.torsion = 0) (x : M) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ (TangentSpace I x)) (u v : TangentSpace I x) :
    (∑ i, cov.ricciTensor x u (b i) * cov.ricciTensor x (b i) v) =
      ∑ i, cov.ricciTensor x v (b i) * cov.ricciTensor x (b i) u := by
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht x u (b i),
    IsMetricCompatible.ricciTensor_comm (cov := cov) hcov ht x (b i) v]
  exact mul_comm _ _

end CovariantDerivative
