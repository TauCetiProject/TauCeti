/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.QuadraticForm
public import TauCeti.Probability.Moments.HansonWright
import TauCeti.Probability.Independence.Integration

/-!
# Concentration of distances to subspaces

For independent centered variance-one sub-Gaussian coordinates, squared distance to a subspace
has mean equal to its codimension. The Hanson–Wright inequality gives concentration of this
squared distance and, consequently, concentration of the distance around the square root of
codimension. The estimates also apply to an independent random subspace of fixed codimension;
measurability and independence are imposed on its orthogonal-complement projection.

These estimates supply distance bounds in invertibility arguments for random matrices.

## Main results

* `Submodule.integral_infDist_sq_eq_finrank_orthogonal`: the mean squared distance.
* `ProbabilityTheory.iIndepFun.measureReal_abs_infDist_sub_sqrt_finrank_gt_le`: concentration
  around the square root of codimension for a fixed subspace.
* `ProbabilityTheory.iIndepFun.measureReal_infDist_lt_one_sub_mul_sqrt_le_of_indepFun`: the
  lower-tail bound for an independent random subspace of fixed codimension.

## References

* R. Vershynin, *High-Dimensional Probability*, 2018, Theorem 6.3.2 and Exercise 6.3.4.
* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, 2008, §4.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace Submodule

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {X : ι → Ω → ℝ}

/-- Square-integrable coordinates have integrable squared distance to every subspace. No
independence or centering assumption is needed. -/
theorem integrable_infDist_sq {𝕜 : Type*} [RCLike 𝕜]
    (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) {Y : ι → Ω → 𝕜}
    (hY : ∀ i, MemLp (Y i) 2 P) :
    Integrable (fun ω ↦ Metric.infDist (WithLp.toLp 2 (fun i ↦ Y i ω)) (U : Set _) ^ 2) P := by
  have hx : AEMeasurable (fun ω ↦ WithLp.toLp 2 (fun i ↦ Y i ω)) P :=
    (PiLp.continuous_toLp 2 (fun _ : ι ↦ 𝕜)).measurable.comp_aemeasurable
      (AEMeasurable.of_eval fun i ↦ (hY i).aemeasurable)
  have hi : Integrable (fun ω ↦ ∑ i, ‖Y i ω‖ ^ 2) P :=
    integrable_finsetSum _ fun i _ ↦
      (memLp_two_iff_integrable_sq_norm (hY i).aestronglyMeasurable).mp (hY i)
  refine hi.mono (((Metric.continuous_infDist_pt _).measurable.comp_aemeasurable hx).pow_const
    2).aestronglyMeasurable (.of_forall fun ω ↦ ?_)
  have hdist := Metric.infDist_le_dist_of_mem (x := WithLp.toLp 2 (fun i ↦ Y i ω)) U.zero_mem
  rw [dist_zero_right] at hdist
  simpa only [Real.norm_eq_abs, abs_sq,
    abs_of_nonneg (Finset.sum_nonneg fun i _ ↦ sq_nonneg ‖Y i ω‖),
    EuclideanSpace.norm_sq_eq] using
      (sq_le_sq₀ Metric.infDist_nonneg (norm_nonneg _)).2 hdist

/-- For centered, variance-one, square-integrable pairwise independent coordinates, the integral
of squared distance to a subspace is its codimension. Sub-Gaussianity is not required. -/
theorem integral_infDist_sq_eq_finrank_orthogonal (U : Submodule ℝ (EuclideanSpace ℝ ι))
    [IsFiniteMeasure P] (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[P] X j)
    (hX : ∀ i, MemLp (X i) 2 P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1) :
    ∫ ω, Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) ^ 2 ∂P =
      (Module.finrank ℝ Uᗮ : ℝ) := by
  classical
  let e := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
  let A := e.symm Uᗮ.starProjection
  have hquad (ω : Ω) : (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) =
      Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) ^ 2 := by
    rw [← Matrix.inner_toEuclideanCLM A (WithLp.toLp 2 (fun i ↦ X i ω))
      (WithLp.toLp 2 (fun i ↦ X i ω)), e.apply_symm_apply]
    exact U.re_inner_starProjection_orthogonal_eq_infDist_sq _
  have h := TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun
    hindep (fun i ↦ (hX i).integrable (by norm_num))
    (fun i ↦ by simpa only [Real.norm_eq_abs, sq_abs] using (hX i).integrable_sq) hmean A
  simp only [star_trivial, hquad, Real.norm_eq_abs, sq_abs, hvar, RCLike.ofReal_real_eq_id,
    id_eq, mul_one] at h
  rw [h.2]
  exact (LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun ι ℝ).toBasis
    Uᗮ.starProjection.toLinearMap).symm.trans Uᗮ.trace_starProjection

end Submodule

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {X : ι → Ω → ℝ}

/-- Squared distance to an independent random subspace of codimension `d` satisfies the
Hanson–Wright bound. The coordinate variance proxy is `K`, rather than its square root. -/
theorem measureReal_abs_infDist_sq_sub_gt_le_of_indepFun
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Ω → Submodule ℝ (EuclideanSpace ℝ ι))
    (hU : AEMeasurable (fun ω ↦ (U ω)ᗮ.starProjection) P)
    (hUX : IndepFun (fun ω ↦ (U ω)ᗮ.starProjection) (fun ω i ↦ X i ω) P)
    {d : ℕ} (hd : ∀ᵐ ω ∂P, Module.finrank ℝ (U ω)ᗮ = d) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 - d|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * d)) (t / K)) := by
  classical
  let e := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
  let A (ω : Ω) := e.symm ((U ω)ᗮ.starProjection)
  have he : Measurable e.symm :=
    e.symm.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hA : AEMeasurable A P := he.comp_aemeasurable hU
  have hAX : IndepFun A (fun ω i ↦ X i ω) P := hUX.comp he measurable_id
  have hAeq (ω : Ω) : A ω = LinearMap.toMatrix
      (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis
      (U ω)ᗮ.starProjection.toLinearMap := rfl
  have hF : ∀ᵐ ω ∂P, ∑ i, ∑ j, A ω i j ^ 2 ≤ (d : ℝ) := by
    filter_upwards [hd] with ω hω
    simpa only [hAeq, Real.norm_eq_abs, sq_abs, hω] using
      ((U ω)ᗮ.sum_norm_sq_toMatrix_starProjection (EuclideanSpace.basisFun ι ℝ)).le
  have hop : ∀ᵐ ω ∂P, ‖A ω‖ ≤ 1 := .of_forall fun ω ↦ by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, e.apply_symm_apply]
    exact (U ω)ᗮ.starProjection_norm_le
  have hquad (ω : Ω) : (fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) =
      Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 := by
    let x := WithLp.toLp 2 (fun i ↦ X i ω)
    rw [← Matrix.inner_toEuclideanCLM (A ω) x x, e.apply_symm_apply]
    exact (U ω).re_inner_starProjection_orthogonal_eq_infDist_sq x
  have htr (ω : Ω) : ∑ i, A ω i i * ∫ ω', X i ω' ^ 2 ∂P =
      (Module.finrank ℝ (U ω)ᗮ : ℝ) := by
    simp only [hvar, mul_one, hAeq]
    simpa only [Matrix.trace, Matrix.diag] using
      ((LinearMap.trace_eq_matrix_trace ℝ (EuclideanSpace.basisFun ι ℝ).toBasis
        (U ω)ᗮ.starProjection.toLinearMap).symm.trans (U ω)ᗮ.trace_starProjection)
  have hbound := hindep.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    hX hA hAX hF hop ht
  simp only [mul_one] at hbound
  convert hbound using 1
  apply measureReal_congr
  filter_upwards [hd] with ω hω
  simp only [hquad, htr, hω]

/-- Squared distance to a fixed subspace concentrates around its codimension. -/
theorem measureReal_abs_infDist_sq_sub_finrank_gt_le
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) ^ 2 -
        Module.finrank ℝ Uᗮ|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * Module.finrank ℝ Uᗮ)) (t / K)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  exact hindep.measureReal_abs_infDist_sq_sub_gt_le_of_indepFun hX hvar (fun _ ↦ U)
    aemeasurable_const (indepFun_const_left _ _) (.of_forall fun _ ↦ rfl) ht

/-- Distance to an independent random subspace of codimension `d` concentrates around `√d`.
The harmless enlargement `max K 1` makes the statement valid also for empty coordinate types
and zero variance proxies. -/
theorem measureReal_abs_infDist_sub_sqrt_gt_le_of_indepFun
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Ω → Submodule ℝ (EuclideanSpace ℝ ι))
    (hU : AEMeasurable (fun ω ↦ (U ω)ᗮ.starProjection) P)
    (hUX : IndepFun (fun ω ↦ (U ω)ᗮ.starProjection) (fun ω i ↦ X i ω) P)
    {d : ℕ} (hd : ∀ᵐ ω ∂P, Module.finrank ℝ (U ω)ᗮ = d) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) - √d|} ≤
      2 * exp (-t ^ 2 / (3200 * (max (K : ℝ) 1) ^ 2)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  -- Zero codimension means the subspace is the whole space, so the distance is zero.
  rcases d.eq_zero_or_pos with rfl | hdpos
  · have hempty : {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω))
        (U ω : Set _) - √(0 : ℝ)|} =ᵐ[P] ∅ := by
      filter_upwards [hd] with ω hω
      have htop : U ω = ⊤ := Submodule.orthogonal_eq_bot_iff.mp (Submodule.finrank_eq_zero.mp hω)
      simp [htop, Metric.infDist_zero_of_mem, not_lt.mpr ht]
    rw [Nat.cast_zero, measureReal_congr hempty, measureReal_empty]
    positivity
  let C : ℝ≥0 := max K 1
  let s : ℝ := max (√(d : ℝ) * t) (t ^ 2)
  have hC : 1 ≤ (C : ℝ) := by exact_mod_cast le_max_right K 1
  have hCp : 0 < (C : ℝ) := by positivity
  have hdp : 0 < (d : ℝ) := Nat.cast_pos.mpr hdpos
  have hs : 0 ≤ s := (sq_nonneg t).trans (le_max_right _ _)
  have hbound := hindep.measureReal_abs_infDist_sq_sub_gt_le_of_indepFun
    (fun i ↦ (hX i).mono (le_max_left K 1)) hvar U hU hUX hd hs
  -- A distance deviation forces both the linear and quadratic squared-distance thresholds.
  have hsub : {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) - √d|} ⊆
      {ω | s < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 - d|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    let a := Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _)
    have ha : 0 ≤ a := Metric.infDist_nonneg
    have hab : |a - √d| ≤ a + √d :=
      abs_le.mpr ⟨by linarith, by nlinarith [sqrt_nonneg (d : ℝ)]⟩
    have heq : |a ^ 2 - d| = |a - √d| * (a + √d) := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ a + √d), ← abs_mul]
      congr 1
      nlinarith [sq_sqrt hdp.le]
    rw [heq]
    refine max_lt_iff.mpr ⟨?_, ?_⟩
    · simpa only [mul_comm] using
        (mul_lt_mul_of_pos_right hω (sqrt_pos.mpr hdp)).trans_le
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha) (abs_nonneg (a - √d)))
    · nlinarith [mul_self_lt_mul_self ht hω,
        mul_le_mul_of_nonneg_left hab (abs_nonneg (a - √d))]
  -- In either Bernstein regime the exponent dominates `t² / C²`.
  have hst : (d : ℝ) * t ^ 2 ≤ s ^ 2 := by
    have hh := (sq_le_sq₀ (mul_nonneg (sqrt_nonneg (d : ℝ)) ht) hs).2 (le_max_left _ _)
    nlinarith [sq_sqrt hdp.le]
  have hmin : t ^ 2 / (C : ℝ) ^ 2 ≤
      min (s ^ 2 / ((C : ℝ) ^ 2 * d)) (s / C) := by
    refine le_min ((div_le_div_iff₀ (by positivity) (by positivity)).2 ?_) ?_
    · nlinarith [mul_le_mul_of_nonneg_left hst (sq_nonneg (C : ℝ))]
    · exact (div_le_div_of_nonneg_left (sq_nonneg t) hCp (by nlinarith)).trans
        (div_le_div_of_nonneg_right (le_max_right _ _) hCp.le)
  refine (measureReal_mono hsub).trans (hbound.trans ?_)
  gcongr
  convert mul_le_mul_of_nonpos_left hmin (by norm_num : -(1 / 3200 : ℝ) ≤ 0) using 1
  simp only [C, NNReal.coe_max, NNReal.coe_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Distance to a fixed subspace has a dimension-free sub-Gaussian deviation bound around the
square root of its codimension. -/
theorem measureReal_abs_infDist_sub_sqrt_finrank_gt_le
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) -
        √(Module.finrank ℝ Uᗮ : ℝ)|} ≤
      2 * exp (-t ^ 2 / (3200 * (max (K : ℝ) 1) ^ 2)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  exact hindep.measureReal_abs_infDist_sub_sqrt_gt_le_of_indepFun hX hvar (fun _ ↦ U)
    aemeasurable_const (indepFun_const_left _ _) (.of_forall fun _ ↦ rfl) ht

/-- The lower tail at a fixed fraction of the typical distance is exponentially small in
codimension. The subspace may be random, provided its projection is independent of the vector. -/
theorem measureReal_infDist_lt_one_sub_mul_sqrt_le_of_indepFun
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Ω → Submodule ℝ (EuclideanSpace ℝ ι))
    (hU : AEMeasurable (fun ω ↦ (U ω)ᗮ.starProjection) P)
    (hUX : IndepFun (fun ω ↦ (U ω)ᗮ.starProjection) (fun ω i ↦ X i ω) P)
    {d : ℕ} (hd : ∀ᵐ ω ∂P, Module.finrank ℝ (U ω)ᗮ = d)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) < (1 - ε) * √d} ≤
      2 * exp (-(ε ^ 2 * d) / (3200 * (max (K : ℝ) 1) ^ 2)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hbound := hindep.measureReal_abs_infDist_sub_sqrt_gt_le_of_indepFun
    hX hvar U hU hUX hd (mul_nonneg hε (sqrt_nonneg (d : ℝ)))
  rw [mul_pow, sq_sqrt (Nat.cast_nonneg d)] at hbound
  refine (measureReal_mono fun ω hω ↦ ?_).trans hbound
  simp only [Set.mem_ofPred_eq] at hω ⊢
  exact lt_abs.mpr (Or.inr (by nlinarith))

end ProbabilityTheory.iIndepFun
