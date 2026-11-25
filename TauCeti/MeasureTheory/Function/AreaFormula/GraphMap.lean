/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Calculus.FDeriv.WithLp

/-!
# The area of a graph in every codimension

Let `E` and `F` be finite-dimensional real inner product spaces. For a linear map `A : E → F`, the
graph map `v ↦ (v, A v)` into the Euclidean product `WithLp 2 (E × F)` has norm determinant
`√det(I + A* A)` (`LinearMap.normDet_graph`): its Gram matrix in an orthonormal basis `b` of `E`
is `⟪b_i, b_j⟫ + ⟪A b_i, A b_j⟫`, the matrix of `I + A* A`.

Consequently, for a Lipschitz `φ : E → F` and a measurable `s ⊆ E`, the `dim E`-dimensional
Euclidean Hausdorff measure of the graph of `φ` over `s` is
`∫_s √det(I + Dφ(x)* Dφ(x)) dx` (`LipschitzWith.euclideanHausdorffMeasure_graph_image`): the graph
parametrization `x ↦ (x, φ x)` is Lipschitz and injective, so the area formula for injective
Lipschitz maps applies, and at every point where `φ` is differentiable, almost every point by
Rademacher's theorem, its derivative is the graph map of `Dφ(x)`.

For the identity of a plane, the graph map `x ↦ (x, x)` scales areas by `2 = √det(2I)`
(`LinearMap.normDet_graph_id_of_finrank_eq_two`), while the codimension-one surface factor
`√(1 + ‖A‖²)` with the operator norm `‖id‖ = 1` would give `√2`.

This is the first part of §2.2 of the GeometricMeasureTheory roadmap.

## Main results

* `LinearMap.normDet_graph`: the norm determinant of a linear graph map.
* `LipschitzWith.euclideanHausdorffMeasure_graph_image`: the area of a Lipschitz graph.
-/

public section

noncomputable section

open MeasureTheory Set Module
open scoped NNReal ENNReal RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

namespace LinearMap

/-- The graph map `v ↦ (v, A v)` of a linear map, into the Euclidean product. -/
def graphL (A : E →ₗ[ℝ] F) : E →ₗ[ℝ] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 ℝ (E × F)).symm.toLinearMap ∘ₗ LinearMap.id.prod A

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
@[simp]
theorem graphL_apply (A : E →ₗ[ℝ] F) (v : E) : graphL A v = WithLp.toLp 2 (v, A v) :=
  (rfl)

/-- **The norm determinant of a linear graph.** The graph map `v ↦ (v, A v)` into
`WithLp 2 (E × F)` has norm determinant `√det(I + A* A)`. -/
theorem normDet_graph (A : E →ₗ[ℝ] F) :
    (graphL A).normDet = Real.sqrt (LinearMap.det (1 + LinearMap.adjoint A ∘ₗ A)) := by
  let b := stdOrthonormalBasis ℝ E
  have hgram : Matrix.gram ℝ (fun i => graphL A (b i)) =
      LinearMap.toMatrix b.toBasis b.toBasis (1 + LinearMap.adjoint A ∘ₗ A) := by
    ext i j
    simp only [Matrix.gram_apply, graphL_apply, WithLp.prod_inner_apply, LinearMap.toMatrix_apply,
      OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
      OrthonormalBasis.repr_apply_apply, LinearMap.add_apply, one_apply_eq_self,
      LinearMap.comp_apply, inner_add_right, LinearMap.adjoint_inner_right]
  have hsq : (graphL A).normDet ^ 2 = LinearMap.det (1 + LinearMap.adjoint A ∘ₗ A) := by
    have h := (graphL A).normDet_sq_eq_det_gram b
    simp only [RCLike.ofReal_real_eq_id, id_eq] at h
    rw [h, hgram, LinearMap.det_toMatrix]
  rw [← hsq, Real.sqrt_sq (graphL A).normDet_nonneg]

/-- **The graph of the identity of a plane.** If `dim E = 2`, the graph map `x ↦ (x, x)` has norm
determinant `2 = √det(2I)`. -/
theorem normDet_graph_id_of_finrank_eq_two (hE : finrank ℝ E = 2) :
    (graphL (LinearMap.id : E →ₗ[ℝ] E)).normDet = 2 := by
  rw [normDet_graph, LinearMap.adjoint_id, LinearMap.id_comp,
    show (1 + LinearMap.id : E →ₗ[ℝ] E) = (2 : ℝ) • LinearMap.id by
      ext v; simp [two_smul],
    LinearMap.det_smul, LinearMap.det_id, hE]
  rw [show ((2 : ℝ) ^ 2 * 1) = 2 ^ 2 by ring, Real.sqrt_sq zero_le_two]

end LinearMap

namespace LipschitzWith

/-- The graph parametrization `x ↦ (x, f x)` of a Lipschitz map into the `L²` product is
Lipschitz. -/
theorem graph {α β : Type*} [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : ℝ≥0} {f : α → β}
    (hf : LipschitzWith K f) :
    LipschitzWith ((2 : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal * max 1 K)
      (fun x ↦ WithLp.toLp 2 (x, f x)) :=
  (WithLp.prod_lipschitzWith_toLp 2 α β).comp (LipschitzWith.id.prodMk hf)

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] {K : ℝ≥0}
  {φ : E → F} {s : Set E}

/-- **The area of a Lipschitz graph.** For a Lipschitz `φ : E → F` and a measurable `s ⊆ E`, the
`dim E`-dimensional Euclidean Hausdorff measure of the graph of `φ` over `s` is
`∫_s √det(I + Dφ(x)* Dφ(x)) dx`. The integrand is defined at the points where `φ` is
differentiable, which is almost every point. -/
theorem euclideanHausdorffMeasure_graph_image (hφ : LipschitzWith K φ) (hs : MeasurableSet s) :
    μHE[finrank ℝ E] ((fun x ↦ WithLp.toLp 2 (x, φ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.sqrt (LinearMap.det
        (1 + LinearMap.adjoint (fderiv ℝ φ x : E →ₗ[ℝ] F) ∘ₗ (fderiv ℝ φ x : E →ₗ[ℝ] F)))) := by
  rw [← hφ.graph.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hs
    (fun x _ y _ hxy ↦ congrArg Prod.fst (WithLp.toLp_injective 2 hxy))]
  refine setLIntegral_congr_fun_ae hs ?_
  filter_upwards [hφ.ae_differentiableAt] with x hx _
  rw [← LinearMap.normDet_graph]
  congr 2
  ext v
  exact (TauCeti.fderiv_toLp_prodMk_apply (f := fun w ↦ w) differentiableAt_fun_id hx v).trans
    (by simp)

end LipschitzWith
