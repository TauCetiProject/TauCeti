/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Trace
public import TauCeti.Probability.Moments.HansonWright
import TauCeti.Probability.Independence.Integration
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Concentration of distances to subspaces

For independent centered variance-one sub-Gaussian coordinates, squared distance to a subspace
has mean equal to its codimension. The Hanson–Wright inequality gives concentration of this
squared distance and, consequently, concentration of the distance around the square root of
codimension. The estimates also apply to independent random subspaces with varying codimension;
measurability and independence are imposed on their orthogonal-complement projections.

These estimates supply distance bounds in invertibility arguments for random matrices.

## Main results

* `Submodule.integral_infDist_sq_eq_finrank_orthogonal`: the mean squared distance.
* `ProbabilityTheory.iIndepFun.measureReal_abs_infDist_sub_sqrt_finrank_gt_le`: concentration
  around the square root of codimension for a fixed subspace.
* `ProbabilityTheory.iIndepFun.measureReal_infDist_lt_one_sub_mul_sqrt_le_of_indepFun`: the
  lower-tail bound under lower bounds on codimension and coordinate second moments.

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

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- For centered, unit-second-moment, square-integrable pairwise independent real or complex
coordinates, the integral of squared distance to a subspace is its codimension over the scalar
field. Sub-Gaussianity is not required. -/
theorem integral_infDist_sq_eq_finrank_orthogonal {𝕜 : Type*} [RCLike 𝕜]
    (U : Submodule 𝕜 (EuclideanSpace 𝕜 ι)) {X : ι → Ω → 𝕜}
    [IsFiniteMeasure P] (hindep : Pairwise fun i j ↦ X i ⟂ᵢ[P] X j)
    (hX : ∀ i, MemLp (X i) 2 P)
    (hmean : ∀ i, ∫ ω, X i ω ∂P = 0) (hvar : ∀ i, ∫ ω, ‖X i ω‖ ^ 2 ∂P = 1) :
    ∫ ω, Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) ^ 2 ∂P =
      (Module.finrank 𝕜 Uᗮ : ℝ) := by
  classical
  let e := Matrix.toEuclideanCLM (n := ι) (𝕜 := 𝕜)
  let A := e.symm Uᗮ.starProjection
  have hquad (ω : Ω) : RCLike.re (star (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω)) =
      Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) ^ 2 := by
    exact U.re_star_dotProduct_toEuclideanCLM_symm_starProjection_orthogonal _
  have h := TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun
    hindep (fun i ↦ (hX i).integrable (by norm_num))
    (fun i ↦ (memLp_two_iff_integrable_sq_norm (hX i).aestronglyMeasurable).mp (hX i)) hmean A
  have htr : ∑ i, A i i = (Module.finrank 𝕜 Uᗮ : 𝕜) := by
    simpa only [Matrix.trace, Matrix.diag] using Uᗮ.trace_toEuclideanCLM_symm_starProjection
  rw [← integral_congr_ae (.of_forall hquad), integral_re h.1, h.2]
  simp only [hvar, RCLike.ofReal_one, mul_one, htr, RCLike.natCast_re]

end Submodule

namespace ProbabilityTheory.iIndepFun

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {X : ι → Ω → ℝ}

/-- Squared distance to an independent random subspace of codimension at most `d` satisfies the
Hanson–Wright bound. The coordinate variance proxy is `K`, rather than its square root. -/
theorem measureReal_abs_infDist_sq_sub_gt_le_of_indepFun
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Ω → Submodule ℝ (EuclideanSpace ℝ ι))
    (hU : AEMeasurable (fun ω ↦ (U ω)ᗮ.starProjection) P)
    (hUX : IndepFun (fun ω ↦ (U ω)ᗮ.starProjection) (fun ω i ↦ X i ω) P)
    {d : ℕ} (hd : ∀ᵐ ω ∂P, Module.finrank ℝ (U ω)ᗮ ≤ d) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 -
        Module.finrank ℝ (U ω)ᗮ|} ≤
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
      (U ω)ᗮ.starProjection.toLinearMap :=
    ((U ω)ᗮ.starProjection).toEuclideanCLM_symm_eq_toMatrix
  have hF : ∀ᵐ ω ∂P, ∑ i, ∑ j, A ω i j ^ 2 ≤ (d : ℝ) := by
    filter_upwards [hd] with ω hω
    calc
      ∑ i, ∑ j, A ω i j ^ 2 = (Module.finrank ℝ (U ω)ᗮ : ℝ) := by
        simpa only [hAeq, Real.norm_eq_abs, sq_abs] using
          (U ω)ᗮ.sum_norm_sq_toMatrix_starProjection (EuclideanSpace.basisFun ι ℝ)
      _ ≤ d := by exact_mod_cast hω
  have hop : ∀ᵐ ω ∂P, ‖A ω‖ ≤ 1 := .of_forall fun ω ↦ by
    rw [← Matrix.l2_opNorm_toEuclideanCLM, e.apply_symm_apply]
    exact (U ω)ᗮ.starProjection_norm_le
  have hquad (ω : Ω) : (fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) =
      Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 := by
    exact (U ω).re_star_dotProduct_toEuclideanCLM_symm_starProjection_orthogonal _
  have htr (ω : Ω) : ∑ i, A ω i i * ∫ ω', X i ω' ^ 2 ∂P =
      (Module.finrank ℝ (U ω)ᗮ : ℝ) := by
    simpa only [hvar, mul_one, Matrix.trace, Matrix.diag] using
      (U ω)ᗮ.trace_toEuclideanCLM_symm_starProjection
  have hbound := hindep.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    hX hA hAX hF hop ht
  simp only [mul_one] at hbound
  simpa only [hquad, htr] using hbound

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
    aemeasurable_const (indepFun_const_left _ _) (.of_forall fun _ ↦ le_rfl) ht

/-- Distance to an independent random subspace concentrates around the square root of its
codimension, which may vary with the subspace. The harmless enlargement `max K 1` also covers
empty coordinate types and zero variance proxies. -/
theorem measureReal_abs_infDist_sub_sqrt_gt_le_of_indepFun
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, ∫ ω, X i ω ^ 2 ∂P = 1)
    (U : Ω → Submodule ℝ (EuclideanSpace ℝ ι))
    (hU : AEMeasurable (fun ω ↦ (U ω)ᗮ.starProjection) P)
    (hUX : IndepFun (fun ω ↦ (U ω)ᗮ.starProjection) (fun ω i ↦ X i ω) P)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) -
        √(Module.finrank ℝ (U ω)ᗮ : ℝ)|} ≤
      2 * exp (-t ^ 2 / (3200 * (max (K : ℝ) 1) ^ 2)) := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rcases ht.eq_or_lt with rfl | ht
  · simp only [sq, zero_mul, neg_zero, zero_div, exp_zero, mul_one]
    exact (measureReal_mono (Set.subset_univ _)).trans (by rw [probReal_univ]; norm_num)
  let C : ℝ≥0 := max K 1
  have hC : 1 ≤ (C : ℝ) := by exact_mod_cast le_max_right K 1
  have hCp : 0 < (C : ℝ) := by positivity
  let e := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
  let A (ω : Ω) := e.symm ((U ω)ᗮ.starProjection)
  have he : Measurable e.symm :=
    e.symm.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hA : AEMeasurable A P := he.comp_aemeasurable hU
  have hAX : IndepFun A (fun ω i ↦ X i ω) P := hUX.comp he measurable_id
  have htr (ω : Ω) : (A ω).trace = (Module.finrank ℝ (U ω)ᗮ : ℝ) :=
    (U ω)ᗮ.trace_toEuclideanCLM_symm_starProjection
  -- Normalize at the larger squared-distance threshold in the two Bernstein regimes.
  let s (M : Matrix ι ι ℝ) := max (√M.trace * t) (t ^ 2)
  have hs (M : Matrix ι ι ℝ) : 0 < s M := (sq_pos_of_pos ht).trans_le (le_max_right _ _)
  let B (ω : Ω) := (s (A ω))⁻¹ • A ω
  have hnorm : Measurable (fun M : Matrix ι ι ℝ ↦ (s M)⁻¹ • M) := by dsimp [s]; fun_prop
  have hB : AEMeasurable B P := hnorm.comp_aemeasurable hA
  have hBX : IndepFun B (fun ω i ↦ X i ω) P := hAX.comp hnorm measurable_id
  have hF : ∀ᵐ ω ∂P, ∑ i, ∑ j, B ω i j ^ 2 ≤ (t ^ 2)⁻¹ := .of_forall fun ω ↦ by
    have hr : 0 ≤ (A ω).trace := by rw [htr]; positivity
    have hsum : ∑ i, ∑ j, A ω i j ^ 2 = (A ω).trace := by
      rw [htr]
      simpa only [A, e, ContinuousLinearMap.toEuclideanCLM_symm_eq_toMatrix,
        Real.norm_eq_abs, sq_abs] using
        (U ω)ᗮ.sum_norm_sq_toMatrix_starProjection (EuclideanSpace.basisFun ι ℝ)
    have hst : (A ω).trace * t ^ 2 ≤ s (A ω) ^ 2 := by
      have hh := (sq_le_sq₀ (mul_nonneg (sqrt_nonneg _) ht.le) (hs _).le).2
        (le_max_left (√(A ω).trace * t) (t ^ 2))
      nlinarith [sq_sqrt hr]
    simp only [B, Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hsum]
    rw [inv_pow, inv_mul_eq_div, ← one_div (t ^ 2)]
    exact (div_le_div_iff₀ (sq_pos_of_pos (hs _)) (sq_pos_of_pos ht)).2 (by simpa using hst)
  have hop : ∀ᵐ ω ∂P, ‖B ω‖ ≤ (t ^ 2)⁻¹ := .of_forall fun ω ↦ by
    have hAn : ‖A ω‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM, e.apply_symm_apply]
      exact (U ω)ᗮ.starProjection_norm_le
    simp only [B, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hs _))]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr (hs _).le) hAn).trans
      (inv_anti₀ (sq_pos_of_pos ht) (le_max_right _ _))
  have hbound := hindep.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    (fun i ↦ (hX i).mono (le_max_left K 1)) hB hBX hF hop (by norm_num : (0 : ℝ) ≤ 1)
  -- A distance deviation exceeds both squared-distance thresholds before normalization.
  have hsub : {ω | t < |Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) -
        √(Module.finrank ℝ (U ω)ᗮ : ℝ)|} ⊆
      {ω | 1 < |(fun i ↦ X i ω) ⬝ᵥ B ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, B ω i i * ∫ ω', X i ω' ^ 2 ∂P|} := by
    intro ω hω
    have hquad : (fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) =
        Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 :=
      (U ω).re_star_dotProduct_toEuclideanCLM_symm_starProjection_orthogonal _
    have hdiag : ∑ i, A ω i i = (A ω).trace := by simp only [Matrix.trace, Matrix.diag]
    simp only [Set.mem_ofPred_eq, B, Matrix.smul_mulVec, dotProduct_smul,
      Matrix.smul_apply, smul_eq_mul, hvar, mul_one, ← Finset.mul_sum, hdiag,
      hquad, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr (hs _))]
    rw [inv_mul_eq_div, lt_div_iff₀ (hs _), one_mul]
    let a := Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _)
    have ha : 0 ≤ a := Metric.infDist_nonneg
    have hr : 0 ≤ (A ω).trace := by rw [htr]; positivity
    have hω' : t < |a - √(A ω).trace| := by simpa only [Set.mem_ofPred_eq, htr, a] using hω
    have hab : |a - √(A ω).trace| ≤ a + √(A ω).trace :=
      abs_le.mpr ⟨by linarith, by nlinarith [sqrt_nonneg (A ω).trace]⟩
    have heq : |a ^ 2 - (A ω).trace| = |a - √(A ω).trace| * (a + √(A ω).trace) := by
      rw [← abs_of_nonneg (by positivity : 0 ≤ a + √(A ω).trace), ← abs_mul]
      congr 1
      nlinarith [sq_sqrt hr]
    rw [heq]
    refine max_lt_iff.mpr ⟨?_, ?_⟩
    · by_cases hr0 : (A ω).trace = 0
      · simp only [hr0, sqrt_zero, zero_mul, add_zero, sub_zero, abs_of_nonneg ha] at hω' ⊢
        have ha' : 0 < a := ht.trans hω'
        positivity
      · simpa only [mul_comm] using
          (mul_lt_mul_of_pos_right hω' (sqrt_pos.mpr (lt_of_le_of_ne hr (Ne.symm hr0)))).trans_le
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha)
              (abs_nonneg (a - √(A ω).trace)))
    · nlinarith [mul_self_lt_mul_self ht.le hω',
        mul_le_mul_of_nonneg_left hab (abs_nonneg (a - √(A ω).trace))]
  -- Both normalized matrix parameters give an exponent at least `t² / C²`.
  refine (measureReal_mono hsub).trans (hbound.trans ?_)
  have hmin : t ^ 2 / (C : ℝ) ^ 2 ≤
      min (1 ^ 2 / ((C : ℝ) ^ 2 * (t ^ 2)⁻¹)) (1 / ((C : ℝ) * (t ^ 2)⁻¹)) := by
    refine le_min (by field_simp; rfl) ?_
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    field_simp
    nlinarith [mul_nonneg (sq_nonneg t) (by nlinarith : 0 ≤ (C : ℝ) ^ 2 - C)]
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
    aemeasurable_const (indepFun_const_left _ _) ht

/-- The lower tail is exponentially small in any lower bound `d` on the codimension.
Coordinate second moments may exceed one, and the independent subspace may have varying rank. -/
theorem measureReal_infDist_lt_one_sub_mul_sqrt_le_of_indepFun
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, 1 ≤ ∫ ω, X i ω ^ 2 ∂P)
    (U : Ω → Submodule ℝ (EuclideanSpace ℝ ι))
    (hU : AEMeasurable (fun ω ↦ (U ω)ᗮ.starProjection) P)
    (hUX : IndepFun (fun ω ↦ (U ω)ᗮ.starProjection) (fun ω i ↦ X i ω) P)
    {d : ℕ} (hd : ∀ᵐ ω ∂P, d ≤ Module.finrank ℝ (U ω)ᗮ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) < (1 - ε) * √d} ≤
      2 * exp (-(ε ^ 2 * d) / (3200 * (max (K : ℝ) 1) ^ 2)) := by
  classical
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  by_cases hd0 : d = 0
  · subst d
    simp [not_lt.mpr Metric.infDist_nonneg]
  by_cases hε1 : 1 ≤ ε
  · have hempty : {ω | Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω))
        (U ω : Set _) < (1 - ε) * √d} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_lt.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith)
        (sqrt_nonneg _)) Metric.infDist_nonneg)
    rw [hempty, measureReal_empty]
    positivity
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have hεle : ε ≤ 1 := (lt_of_not_ge hε1).le
  let C : ℝ≥0 := max K 1
  have hC : 1 ≤ (C : ℝ) := by exact_mod_cast le_max_right K 1
  let e := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)
  let A (ω : Ω) := e.symm ((U ω)ᗮ.starProjection)
  have he : Measurable e.symm :=
    e.symm.toAlgEquiv.toLinearMap.continuous_of_finiteDimensional.measurable
  have hA : AEMeasurable A P := he.comp_aemeasurable hU
  have hAX : IndepFun A (fun ω i ↦ X i ω) P := hUX.comp he measurable_id
  have htr (ω : Ω) : (A ω).trace = (Module.finrank ℝ (U ω)ᗮ : ℝ) :=
    (U ω)ᗮ.trace_toEuclideanCLM_symm_starProjection
  -- Dividing the projection by its rank bounds both matrix parameters by `1 / d`.
  let B (ω : Ω) := (A ω).trace⁻¹ • A ω
  have hnorm : Measurable (fun M : Matrix ι ι ℝ ↦ M.trace⁻¹ • M) := by fun_prop
  have hB : AEMeasurable B P := hnorm.comp_aemeasurable hA
  have hBX : IndepFun B (fun ω i ↦ X i ω) P := hAX.comp hnorm measurable_id
  have hF : ∀ᵐ ω ∂P, ∑ i, ∑ j, B ω i j ^ 2 ≤ (d : ℝ)⁻¹ := by
    filter_upwards [hd] with ω hω
    have hr : 0 < (A ω).trace := by rw [htr]; exact hdpos.trans_le (by exact_mod_cast hω)
    have hsum : ∑ i, ∑ j, A ω i j ^ 2 = (A ω).trace := by
      rw [htr]
      simpa only [A, e, ContinuousLinearMap.toEuclideanCLM_symm_eq_toMatrix,
        Real.norm_eq_abs, sq_abs] using
        (U ω)ᗮ.sum_norm_sq_toMatrix_starProjection (EuclideanSpace.basisFun ι ℝ)
    simp only [B, Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hsum]
    calc
      (A ω).trace⁻¹ ^ 2 * (A ω).trace = (A ω).trace⁻¹ := by field_simp
      _ ≤ (d : ℝ)⁻¹ := inv_anti₀ hdpos (by rw [htr]; exact_mod_cast hω)
  have hop : ∀ᵐ ω ∂P, ‖B ω‖ ≤ (d : ℝ)⁻¹ := by
    filter_upwards [hd] with ω hω
    have hr : 0 < (A ω).trace := by rw [htr]; exact hdpos.trans_le (by exact_mod_cast hω)
    have hAn : ‖A ω‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM, e.apply_symm_apply]
      exact (U ω)ᗮ.starProjection_norm_le
    simp only [B, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
    exact (mul_le_of_le_one_right (inv_nonneg.mpr hr.le) hAn).trans
      (inv_anti₀ hdpos (by rw [htr]; exact_mod_cast hω))
  have hbound := hindep.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    (fun i ↦ (hX i).mono (le_max_left K 1)) hB hBX hF hop hε
  -- The mean of the normalized quadratic form is at least one, even without isotropy.
  have hsub : {ω | Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) <
      (1 - ε) * √d} ≤ᵐ[P] {ω | ε < |(fun i ↦ X i ω) ⬝ᵥ B ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, B ω i i * ∫ ω', X i ω' ^ 2 ∂P|} := by
    filter_upwards [hd] with ω hω hdist
    have hr : 0 < (A ω).trace := by rw [htr]; exact hdpos.trans_le (by exact_mod_cast hω)
    have hdiag (i : ι) : 0 ≤ A ω i i := by
      simp only [A, e, ContinuousLinearMap.toEuclideanCLM_symm_eq_toMatrix]
      exact ((LinearMap.posSemidef_toMatrix_iff (EuclideanSpace.basisFun ι ℝ)).mpr
        ⟨(U ω)ᗮ.starProjection_isSymmetric, (U ω)ᗮ.re_inner_starProjection_nonneg⟩).diag_nonneg
    have hm : 1 ≤ ∑ i, B ω i i * ∫ ω', X i ω' ^ 2 ∂P := by
      calc
        1 = ∑ i, B ω i i := by
          simp only [B, Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
          simpa only [Matrix.trace, Matrix.diag] using (inv_mul_cancel₀ hr.ne').symm
        _ ≤ _ := Finset.sum_le_sum fun i _ ↦ le_mul_of_one_le_right
          (mul_nonneg (inv_nonneg.mpr hr.le) (hdiag i)) (hvar i)
    have hquad : (fun i ↦ X i ω) ⬝ᵥ B ω *ᵥ (fun i ↦ X i ω) =
        (A ω).trace⁻¹ * Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U ω : Set _) ^ 2 := by
      simp only [B, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      congr 1
      exact (U ω).re_star_dotProduct_toEuclideanCLM_symm_starProjection_orthogonal _
    have hsq := (sq_lt_sq₀ Metric.infDist_nonneg (by positivity : 0 ≤ (1 - ε) * √d)).2 hdist
    rw [mul_pow, sq_sqrt (Nat.cast_nonneg d)] at hsq
    have hrd : (d : ℝ) ≤ (A ω).trace := by rw [htr]; exact_mod_cast hω
    have hq : (A ω).trace⁻¹ * Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω))
        (U ω : Set _) ^ 2 < 1 - ε := by
      rw [inv_mul_eq_div, div_lt_iff₀ hr]
      nlinarith [mul_nonneg (sub_nonneg.mpr hεle) (sub_nonneg.mpr hrd),
        mul_nonneg (mul_nonneg hε (sub_nonneg.mpr hεle)) (Nat.cast_nonneg d)]
    rw [hquad]
    exact lt_abs.mpr (.inr (by linarith))
  refine (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    (hbound.trans ?_)
  have hCp : 0 < (C : ℝ) := by positivity
  have hmin : ε ^ 2 * d / (C : ℝ) ^ 2 ≤
      min (ε ^ 2 / ((C : ℝ) ^ 2 * (d : ℝ)⁻¹)) (ε / ((C : ℝ) * (d : ℝ)⁻¹)) := by
    refine le_min (by field_simp; rfl) ?_
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    have hεsq : ε ^ 2 ≤ ε := by nlinarith
    field_simp
    nlinarith [mul_le_mul_of_nonneg_right hεsq (by positivity : 0 ≤ (C : ℝ)),
      mul_nonneg hε (sub_nonneg.mpr hC)]
  gcongr
  convert mul_le_mul_of_nonpos_left hmin (by norm_num : -(1 / 3200 : ℝ) ≤ 0) using 1
  simp only [C, NNReal.coe_max, NNReal.coe_one, div_eq_mul_inv, mul_inv_rev]
  ring

/-- For a fixed subspace, the lower tail is exponentially small in its codimension.
The coordinate second moments need only be bounded below by one. -/
theorem measureReal_infDist_lt_one_sub_mul_sqrt_finrank_le
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (hvar : ∀ i, 1 ≤ ∫ ω, X i ω ^ 2 ∂P)
    (U : Submodule ℝ (EuclideanSpace ℝ ι)) {ε : ℝ} (hε : 0 ≤ ε) :
    P.real {ω | Metric.infDist (WithLp.toLp 2 (fun i ↦ X i ω)) (U : Set _) <
        (1 - ε) * √(Module.finrank ℝ Uᗮ : ℝ)} ≤
      2 * exp (-(ε ^ 2 * Module.finrank ℝ Uᗮ) / (3200 * (max (K : ℝ) 1) ^ 2)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  exact hindep.measureReal_infDist_lt_one_sub_mul_sqrt_le_of_indepFun hX hvar (fun _ ↦ U)
    aemeasurable_const (indepFun_const_left _ _) (.of_forall fun _ ↦ le_rfl) hε

end ProbabilityTheory.iIndepFun
