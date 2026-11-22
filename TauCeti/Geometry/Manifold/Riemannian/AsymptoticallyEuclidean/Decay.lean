/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Infinity
public import TauCeti.Analysis.Calculus.ContDiff.SymbolClass.Matrix
public import TauCeti.Geometry.Manifold.Riemannian.AsymptoticallyEuclidean.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.Calculus.ContDiff.Matrix

/-!
# Decay of the metric coefficients of an asymptotically Euclidean end

Let `φ` be an asymptotically Euclidean end of order `t > 0`, with pulled-back metric coefficients
`g_ij`. By definition the entries of `g - 1` are `O₂(‖x‖ ^ (-t))`: they decay like `‖x‖ ^ (-t)`,
their first derivatives like `‖x‖ ^ (-t - 1)` and their second derivatives like
`‖x‖ ^ (-t - 2)`. In the language of `TauCeti.IsSymbolAtInfinity` they are symbols of order
`-t` and regularity `2` at infinity
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_pullbackMetricCoeff_sub_one`).

This file shows that the other metric quantities expressed through `g_ij` differ from their
Euclidean values at the same rate. The matrix `g` is positive definite at every point of the end
(`TauCeti.IsAsymptoticallyEuclideanEnd.posDef_pullbackMetricCoeff`), so it has an inverse
`g⁻¹ = (g^ij)` and a positive determinant. The entries of `g⁻¹ - 1`
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_inv_pullbackMetricCoeff_sub_one`) and
the volume density `√(det g)` minus `1`
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_sqrt_det_pullbackMetricCoeff_sub_one`)
are again `O₂(‖x‖ ^ (-t))`. These are the estimates by which the inverse metric and the Riemannian
volume of an end are compared with the Euclidean ones, for instance when the ADM flux is related
to the scalar curvature.

The proofs apply the composition rule `TauCeti.IsSymbolAtInfinity.comp_sub` to inversion and to
`A ↦ √(det A)`, which are smooth at the identity matrix; the matrices are normed by the `L^∞`
operator norm, which only enters the proofs, through the reduction of matrix-valued symbols to
their entries (`TauCeti.isSymbolAlong_matrix_iff`).

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §8 and §9.
* S. Cecchini, R. Zeidler, *The positive mass theorem and distance estimates in the spin
  setting*, arXiv:2108.11972, Definition 2.1.
-/

public section

open Asymptotics Bundle Function Manifold Metric Set Filter Bornology
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

namespace IsAsymptoticallyEuclideanEnd

variable {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}

/-- The pulled-back metric coefficients of an end are positive definite at every point of the
exterior of its ball: they are the Gram matrix of the images `dφ_x eᵢ` of a basis under the
invertible differential. -/
theorem posDef_pullbackMetricCoeff (h : IsAsymptoticallyEuclideanEnd I t R φ)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ (closedBall 0 R)ᶜ) :
    (pullbackMetricCoeff I φ x).PosDef := by
  obtain ⟨e, he⟩ := h.isInvertible_mfderiv x hx
  rw [pullbackMetricCoeff_def]
  refine Matrix.posDef_gram_of_linearIndependent ?_
  rw [← he]
  exact (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.linearIndependent.map'
    e.toLinearEquiv.toLinearMap e.toLinearEquiv.ker

/-- **The metric coefficients of an end decay.** The entries `g_ij - δ_ij` of the pulled-back
metric coefficients of an end of order `t` are symbols of order `-t` and regularity `2` at
infinity: they are `O₂(‖x‖ ^ (-t))`. -/
theorem isSymbolAtInfinity_pullbackMetricCoeff_sub_one (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (i j : Fin n) :
    IsSymbolAtInfinity 2 (-t) fun x ↦ (pullbackMetricCoeff I φ x - 1) i j := by
  have hU : (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∈ cobounded _ :=
    isBounded_def.1 isBounded_closedBall
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  refine isSymbolAtInfinity_iff.2 ⟨?_, fun k hk ↦ IsBigO.of_bound C ?_⟩
  · filter_upwards [hU] with x hx
    simp only [Matrix.sub_apply]
    exact ((h.contDiffOn_pullbackMetricCoeff i j).contDiffAt
      (isClosed_closedBall.isOpen_compl.mem_nhds hx)).sub contDiffAt_const
  · filter_upwards [hU] with x hx
    have hx0 : 0 < ‖x‖ := h.radius_pos.trans (by simpa using hx)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact hC k hk i j x hx

end IsAsymptoticallyEuclideanEnd

/-! ### Inverse metric and volume density -/

section Matrix

open scoped Matrix.Norms.Operator

namespace IsAsymptoticallyEuclideanEnd

variable {t R : ℝ} {φ : EuclideanSpace ℝ (Fin n) → M}

/-- **The inverse metric of an end.** For an end of order `t > 0`, the entries `g^ij - δ_ij` of
the inverse of the pulled-back metric coefficients are symbols of order `-t` and regularity `2`
at infinity: the inverse metric is `O₂(‖x‖ ^ (-t))`-close to the Euclidean one. -/
theorem isSymbolAtInfinity_inv_pullbackMetricCoeff_sub_one
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) (i j : Fin n) :
    IsSymbolAtInfinity 2 (-t) fun x ↦ ((pullbackMetricCoeff I φ x)⁻¹ - 1) i j := by
  have hg : IsSymbolAtInfinity 2 (-t) fun x ↦ pullbackMetricCoeff I φ x - 1 :=
    isSymbolAlong_matrix_iff.2 h.isSymbolAtInfinity_pullbackMetricCoeff_sub_one
  simpa only [Matrix.nonsing_inv_eq_ringInverse] using
    isSymbolAlong_matrix_iff.1 (hg.ringInverse_sub_one (neg_neg_of_pos ht)) i j

/-- **The volume density of an end.** For an end of order `t > 0`, the Riemannian volume density
`√(det g)` of the pulled-back metric coefficients, minus `1`, is a symbol of order `-t` and
regularity `2` at infinity: the volume density is `O₂(‖x‖ ^ (-t))`-close to the Euclidean one. -/
theorem isSymbolAtInfinity_sqrt_det_pullbackMetricCoeff_sub_one
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    IsSymbolAtInfinity 2 (-t) fun x ↦ √(pullbackMetricCoeff I φ x).det - 1 := by
  have hg : IsSymbolAtInfinity 2 (-t) fun x ↦ pullbackMetricCoeff I φ x - 1 :=
    isSymbolAlong_matrix_iff.2 h.isSymbolAtInfinity_pullbackMetricCoeff_sub_one
  -- `A ↦ √(det A)` is smooth at the identity matrix, where the determinant is `1`.
  have hG : ContDiffAt ℝ (max 2 1 : ℕ) (fun B : Matrix (Fin n) (Fin n) ℝ ↦ √B.det) 1 :=
    (Real.contDiffAt_sqrt (by simp)).comp _ (ContDiffAt.matrix_det fun i j ↦
      (Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.contDiffAt)
  simpa using hg.comp_sub (neg_neg_of_pos ht) hG

end IsAsymptoticallyEuclideanEnd

end Matrix

end TauCeti
