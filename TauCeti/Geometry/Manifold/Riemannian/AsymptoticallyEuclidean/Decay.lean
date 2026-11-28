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
import TauCeti.Analysis.SpecialFunctions.Pow.Asymptotics
import TauCeti.Topology.Instances.Matrix

/-!
# Decay of the metric coefficients of an asymptotically Euclidean end

Let `φ` be an asymptotically Euclidean end of order `t > 0`, with pulled-back metric coefficients
`g_ij`. By definition the entries of `g - 1` are `O₂(‖x‖ ^ (-t))`: they decay like `‖x‖ ^ (-t)`,
their first derivatives like `‖x‖ ^ (-t - 1)` and their second derivatives like
`‖x‖ ^ (-t - 2)`. In the language of `TauCeti.IsSymbolAtInfinity` they are symbols of order
`-t` and regularity `2` at infinity
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_pullbackMetricCoeff_sub_one`).
In particular, for `t > 0`, `g_ij → δ_ij` and `∂g_ij = o(‖x‖⁻¹)` as `‖x‖ → ∞`
(`TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_pullbackMetricCoeff` and
`TauCeti.IsAsymptoticallyEuclideanEnd.isLittleO_fderiv_pullbackMetricCoeff`).

This file shows that the other metric quantities expressed through `g_ij` differ from their
Euclidean values at the same rate. The matrix `g` is positive definite at every point of the end
(`TauCeti.IsAsymptoticallyEuclideanEnd.posDef_pullbackMetricCoeff`), so it has an inverse
`g⁻¹ = (g^ij)` and a positive determinant. The entries of `g⁻¹ - 1`
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_inv_pullbackMetricCoeff_sub_one`) and
the volume density `√(det g)` minus `1`
(`TauCeti.IsAsymptoticallyEuclideanEnd.isSymbolAtInfinity_sqrt_det_pullbackMetricCoeff_sub_one`)
are again `O₂(‖x‖ ^ (-t))`. As consequences, the pulled-back metric matrix, its determinant, and
its inverse converge to `1` along `Bornology.cobounded`
(`TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_pullbackMetricCoeff_one`,
`TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_det_pullbackMetricCoeff_one`,
`TauCeti.IsAsymptoticallyEuclideanEnd.tendsto_inv_pullbackMetricCoeff_one`), and outside a large
ball `‖x‖ > R₁` the determinant is at least `1 / 4` (hence `√(det g) ≥ 1 / 2`), the inverse
entries satisfy `|g⁻¹_ij| ≤ 2` and `g⁻¹ - 1 = O(‖x‖ ^ (-t))`, and `g - 1` together with its
derivatives of order `k ≤ 2` satisfies uniform `O(‖x‖ ^ (-t - k))` bounds
(`TauCeti.IsAsymptoticallyEuclideanEnd.exists_asymptotic_bounds`). These are the estimates by
which the inverse metric and the Riemannian volume of an end are compared with the Euclidean ones,
for instance when the ADM flux is related to the scalar curvature.

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

/-- The metric coefficients of an end of positive order tend to `δ_ij` at infinity, since
`|g_ij - δ_ij| ≤ C |x| ^ (-t)`. -/
theorem tendsto_pullbackMetricCoeff (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t)
    (i j : Fin n) :
    Tendsto (fun x ↦ pullbackMetricCoeff I φ x i j) (Bornology.cobounded _)
      (𝓝 (if i = j then 1 else 0)) := by
  simpa [Matrix.sub_apply, Matrix.one_apply] using
    (h.isSymbolAtInfinity_pullbackMetricCoeff_sub_one i j).tendsto_of_sub (neg_lt_zero.2 ht)

/-- For positive decay order `t > 0`, the pulled-back metric matrix approaches the identity matrix
along `Bornology.cobounded`. -/
theorem tendsto_pullbackMetricCoeff_one (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    Tendsto (pullbackMetricCoeff I φ)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ by
    simpa [Matrix.one_apply] using h.tendsto_pullbackMetricCoeff ht i j

/-- The derivatives of the metric coefficients of an end of positive order are `o(|x|⁻¹)` at
infinity, since `|∂g_ij| ≤ C |x| ^ (-t - 1)`. -/
theorem isLittleO_fderiv_pullbackMetricCoeff (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) (i j : Fin n) :
    (fun x ↦ fderiv ℝ (fun y ↦ pullbackMetricCoeff I φ y i j) x) =o[Bornology.cobounded _]
      fun x ↦ ‖x‖⁻¹ := by
  have h1 : (fun x ↦ fderiv ℝ (fun y ↦ pullbackMetricCoeff I φ y i j) x)
      =O[Bornology.cobounded _] fun x ↦ ‖x‖ ^ (-t - 1) :=
    (h.isSymbolAtInfinity_pullbackMetricCoeff_sub_one i j).fderiv.isBigO.congr_left fun x ↦ by
      simp [Matrix.sub_apply, fderiv_sub_const]
  exact h1.trans_isLittleO ((isLittleO_norm_rpow_norm_rpow_cobounded (by linarith)).congr_right
    fun _ ↦ Real.rpow_neg_one _)

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
      ((Matrix.entryLinearMap ℝ ℝ i j).toContinuousLinearMap.contDiff.contDiffAt
        ).congr_of_eventuallyEq (.of_forall fun B ↦
          ((congrFun (LinearMap.coe_toContinuousLinearMap' _) B).trans
            (Matrix.entryLinearMap_apply ..)).symm))
  simpa using hg.comp_sub (neg_neg_of_pos ht) hG

/-- For positive decay order `t > 0`, the determinant of the pulled-back metric matrix converges to
`1` along `Bornology.cobounded`. -/
theorem tendsto_det_pullbackMetricCoeff_one (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) :
    Tendsto (fun x ↦ (pullbackMetricCoeff I φ x).det)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) := by
  have hc : Tendsto (fun A : Matrix (Fin n) (Fin n) ℝ ↦ A.det) (𝓝 1) (𝓝 1) := by
    simpa only [id_eq, Matrix.det_one] using
      (continuous_id.matrix_det.continuousAt (x := (1 : Matrix (Fin n) (Fin n) ℝ))).tendsto
  exact hc.comp (h.tendsto_pullbackMetricCoeff_one ht)

/-- For positive decay order `t > 0`, the inverse of the pulled-back metric matrix converges to the
identity matrix along `Bornology.cobounded`. -/
theorem tendsto_inv_pullbackMetricCoeff_one (h : IsAsymptoticallyEuclideanEnd I t R φ)
    (ht : 0 < t) :
    Tendsto (fun x ↦ (pullbackMetricCoeff I φ x)⁻¹)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n))) (𝓝 1) :=
  tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ by
    simpa [Matrix.sub_apply, Matrix.one_apply] using
      (h.isSymbolAtInfinity_inv_pullbackMetricCoeff_sub_one ht i j).tendsto_of_sub
        (neg_lt_zero.2 ht)

/-- For positive decay order `t > 0`, the entries of `(pullbackMetricCoeff I φ x)⁻¹` are eventually
bounded in absolute value by `2` along `Bornology.cobounded`. -/
private theorem eventually_abs_inv_pullbackMetricCoeff_le
    (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      ∀ i j : Fin n, |(pullbackMetricCoeff I φ x)⁻¹ i j| ≤ 2 := by
  rw [eventually_all]; intro i; rw [eventually_all]; intro j
  have hij : Tendsto (fun x ↦ (pullbackMetricCoeff I φ x)⁻¹ i j)
      (Bornology.cobounded (EuclideanSpace ℝ (Fin n)))
      (𝓝 ((1 : Matrix (Fin n) (Fin n) ℝ) i j)) :=
    (continuous_apply_apply i j).continuousAt.tendsto.comp
      (h.tendsto_inv_pullbackMetricCoeff_one ht)
  filter_upwards [Metric.tendsto_nhds.1 hij 1 one_pos] with x hx
  rw [Real.dist_eq, Matrix.one_apply] at hx
  split_ifs at hx <;> linarith [abs_sub_abs_le_abs_sub ((pullbackMetricCoeff I φ x)⁻¹ i j) 1,
    abs_sub_abs_le_abs_sub ((pullbackMetricCoeff I φ x)⁻¹ i j) 0]

/-- For `0 < t`, outside a sufficiently large ball of radius `R₁ ≥ max R 1`:
* the metric determinant satisfies `1 / 4 ≤ det (g(x))` (hence `1 / 2 ≤ √(det (g(x)))`);
* the metric entries satisfy `|g_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* the inverse metric entries satisfy `|g⁻¹_ij(x)| ≤ 2` and
  `|g⁻¹_ij(x) - δ_ij| ≤ C₁ ‖x‖ ^ (-t)`;
* all derivatives of order `k ≤ 2` of `g_ij - δ_ij` are bounded by `C₁ ‖x‖ ^ (-t - k)`. -/
theorem exists_asymptotic_bounds (h : IsAsymptoticallyEuclideanEnd I t R φ) (ht : 0 < t) :
    ∃ R₁ C₁ : ℝ, max R 1 ≤ R₁ ∧ 0 ≤ C₁ ∧
      ∀ x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R₁)ᶜ,
        (1 / 4 ≤ (pullbackMetricCoeff I φ x).det ∧ (pullbackMetricCoeff I φ x).det ≠ 0 ∧
          1 / 2 ≤ Real.sqrt (pullbackMetricCoeff I φ x).det) ∧
        (∀ i j : Fin n,
          |(pullbackMetricCoeff I φ x - 1) i j| ≤ C₁ * ‖x‖ ^ (-t) ∧
          |(pullbackMetricCoeff I φ x)⁻¹ i j| ≤ 2 ∧
          |((pullbackMetricCoeff I φ x)⁻¹ - 1) i j| ≤ C₁ * ‖x‖ ^ (-t) ∧
          ∀ k ≤ 2, ‖iteratedFDeriv ℝ k (fun y ↦ (pullbackMetricCoeff I φ y - 1) i j) x‖ ≤
            C₁ * ‖x‖ ^ (-t - k)) := by
  obtain ⟨C, hC⟩ := h.exists_norm_iteratedFDeriv_le
  -- Combine eventual determinant positivity, inverse-entry bounds, and the exterior radius.
  have hdet_ev : ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      (1 / 4 : ℝ) < (pullbackMetricCoeff I φ x).det :=
    (h.tendsto_det_pullbackMetricCoeff_one ht).eventually (Ioi_mem_nhds (by norm_num))
  have hinv_sym : (fun x (p : Fin n × Fin n) ↦ ((pullbackMetricCoeff I φ x)⁻¹ - 1) p.1 p.2)
      =O[Bornology.cobounded (EuclideanSpace ℝ (Fin n))] fun x ↦ ‖x‖ ^ (-t) :=
    isBigO_pi.2 fun p ↦ (h.isSymbolAtInfinity_inv_pullbackMetricCoeff_sub_one ht p.1 p.2).isBigO
  obtain ⟨M_inv, -, hM_inv⟩ := hinv_sym.exists_nonneg
  have hinv_diff_ev : ∀ᶠ x in Bornology.cobounded (EuclideanSpace ℝ (Fin n)),
      ∀ i j : Fin n, |((pullbackMetricCoeff I φ x)⁻¹ - 1) i j| ≤ M_inv * ‖x‖ ^ (-t) := by
    filter_upwards [hM_inv.bound] with x hx i j
    have hnorm : |((pullbackMetricCoeff I φ x)⁻¹ - 1) i j| ≤
        ‖fun p : Fin n × Fin n ↦ ((pullbackMetricCoeff I φ x)⁻¹ - 1) p.1 p.2‖ :=
      norm_le_pi_norm (fun p : Fin n × Fin n ↦ ((pullbackMetricCoeff I φ x)⁻¹ - 1) p.1 p.2) (i, j)
    refine hnorm.trans ?_
    simpa [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) _)] using hx
  have hev := ((hdet_ev.and (h.eventually_abs_inv_pullbackMetricCoeff_le ht)).and
    hinv_diff_ev).and (tendsto_norm_cobounded_atTop.eventually (Ioi_mem_atTop (max R 1)))
  obtain ⟨R₀, -, hR₀⟩ := Filter.hasBasis_cobounded_norm.eventually_iff.1 hev
  -- Choose a common exterior radius `R₁` and uniform constant `C₁`.
  set R₁ : ℝ := max (max R 1) R₀
  set C₁ : ℝ := max (max C 0) M_inv
  refine ⟨R₁, C₁, le_max_left _ _, le_trans (le_max_right C 0) (le_max_left _ _), fun x hx ↦ ?_⟩
  have hrx₁ : R₁ < ‖x‖ := by simpa using hx
  have ⟨⟨⟨hdet_gt, hinv_le⟩, hinv_diff⟩, hrx_max⟩ := hR₀ ((le_max_right _ _).trans hrx₁.le)
  have hrx : x ∈ (closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ := by
    simpa using (le_max_left R 1).trans_lt hrx_max
  have hdet_ne : (pullbackMetricCoeff I φ x).det ≠ 0 :=
    ((by norm_num : (0 : ℝ) < 1 / 4).trans hdet_gt).ne'
  refine ⟨⟨hdet_gt.le, hdet_ne, Real.le_sqrt_of_sq_le (by linarith)⟩, fun i j ↦ ?_⟩
  have hC0 : C ≤ max C 0 := le_max_left C 0
  have hC1 : max C 0 ≤ C₁ := le_max_left _ _
  have hM1 : M_inv ≤ C₁ := le_max_right _ _
  have h0 : |(pullbackMetricCoeff I φ x - 1) i j| ≤ C * ‖x‖ ^ (-t) := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, Nat.cast_zero, sub_zero] using
      hC 0 (Nat.zero_le 2) i j x hrx
  refine ⟨h0.trans
      (mul_le_mul_of_nonneg_right (hC0.trans hC1) (Real.rpow_nonneg (norm_nonneg x) _)),
    hinv_le i j,
    (hinv_diff i j).trans (mul_le_mul_of_nonneg_right hM1 (Real.rpow_nonneg (norm_nonneg x) _)),
    fun k hk ↦ (hC k hk i j x hrx).trans
      (mul_le_mul_of_nonneg_right (hC0.trans hC1) (Real.rpow_nonneg (norm_nonneg x) _))⟩

end IsAsymptoticallyEuclideanEnd

end Matrix

end TauCeti
