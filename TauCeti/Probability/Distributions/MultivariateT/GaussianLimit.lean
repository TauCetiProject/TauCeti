/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateT.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Concentration
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Gaussian limits of multivariate t laws

At fixed location and positive semidefinite scale, multivariate t laws converge weakly to the
Gaussian law with that location and covariance as the degrees of freedom tend to infinity.
The scale may be singular or zero, and the coordinate type may be empty.

In the Gaussian--chi-squared construction, the chi-squared variable divided by its degree has
mean one and variance twice the reciprocal degree. Its law therefore concentrates at one.
Lifting this variable to the positive half-line makes the reciprocal-square-root map continuous,
so convergence of product measures and continuous pushforwards gives the Gaussian limit.

## Main result

* `TauCeti.Probability.tendsto_multivariateTMeasure_atTop`: the Gaussian limit in
  `ProbabilityMeasure`.

## References

* S. Kotz and S. Nadarajah, *Multivariate t Distributions and Their Applications*, Cambridge
  University Press, 2004, chapter 1.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

/-- The normalized chi-squared law, carried by the positive half-line. -/
private def normalizedChiSquared (ν : Ioi (0 : ℝ)) : ProbabilityMeasure (Ioi (0 : ℝ)) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure ν.2.le
  let _ := (MeasurableEmbedding.subtype_coe measurableSet_Ioi).isProbabilityMeasure_comap
    (μ := chiSquaredMeasure ν) (by simpa using ae_pos_chiSquaredMeasure ν.2)
  exact ⟨((chiSquaredMeasure ν).comap Subtype.val).map
    (fun x : Ioi (0 : ℝ) => (⟨x.1 / ν.1, mem_Ioi.mpr (div_pos x.2 ν.2)⟩ : Ioi (0 : ℝ))),
    inferInstance⟩

private theorem map_val_normalizedChiSquared (ν : Ioi (0 : ℝ)) :
    (normalizedChiSquared ν : Measure (Ioi (0 : ℝ))).map Subtype.val =
      (chiSquaredMeasure ν).map (fun x => x / ν.1) := by
  simp only [normalizedChiSquared, ProbabilityMeasure.coe_mk]
  rw [Measure.map_map measurable_subtype_coe (by fun_prop)]
  simp only [Function.comp_def]
  have hcomp : (fun x : Ioi (0 : ℝ) => x.1 / ν.1) =
      (fun x : ℝ => x / ν.1) ∘ Subtype.val := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) measurable_subtype_coe,
    map_comap_subtype_coe measurableSet_Ioi,
    Measure.restrict_eq_self_of_ae_mem (ae_pos_chiSquaredMeasure ν.2)]

private theorem tendsto_normalizedChiSquared :
    Tendsto normalizedChiSquared atTop
      (𝓝 (Measure.dirac (⟨1, mem_Ioi.mpr zero_lt_one⟩ : Ioi (0 : ℝ))).toProbabilityMeasure) := by
  have hmem (ν : Ioi (0 : ℝ)) : MemLp id 2 (chiSquaredMeasure ν) := by
    rw [chiSquaredMeasure_eq_gammaMeasure ν.2]
    exact memLp_id_gammaMeasure (half_pos ν.2) one_half_pos
  apply ProbabilityMeasure.tendsto_dirac_of_integral_dist_sq_tendsto_zero
  · intro ν
    let _ := isProbabilityMeasure_chiSquaredMeasure ν.2.le
    have h : MemLp (fun x : ℝ => dist x 1) 2
        ((chiSquaredMeasure ν).map (fun x => x / ν.1)) := by
      apply (memLp_map_measure_iff (by fun_prop) (by fun_prop)).2
      simpa only [Function.comp_def, dist_eq_norm, Pi.sub_apply, id_eq, div_eq_mul_inv] using
        (((hmem ν).mul_const ν.1⁻¹).sub (memLp_const 1)).norm
    rw [← map_val_normalizedChiSquared] at h
    exact (memLp_map_measure_iff (by fun_prop) measurable_subtype_coe.aemeasurable).1 h
  · have hmoment (ν : Ioi (0 : ℝ)) :
        ∫ x, dist x (⟨1, mem_Ioi.mpr zero_lt_one⟩ : Ioi (0 : ℝ)) ^ 2
          ∂(normalizedChiSquared ν : Measure (Ioi (0 : ℝ))) = 2 / ν.1 := by
      simp only [Subtype.dist_eq]
      rw [← (MeasurableEmbedding.subtype_coe measurableSet_Ioi).integral_map
        (fun x : ℝ => dist x 1 ^ 2), map_val_normalizedChiSquared,
        integral_map (by fun_prop) (by fun_prop)]
      have hv := variance_mul_const ν.1⁻¹ id (chiSquaredMeasure ν)
      rw [variance_eq_integral (by fun_prop), integral_mul_const] at hv
      simp only [id_eq] at hv
      rw [integral_id_chiSquaredMeasure ν.2.le, mul_inv_cancel₀ ν.2.ne',
        variance_id_chiSquaredMeasure ν.2.le] at hv
      simp only [Real.dist_eq, sq_abs, div_eq_mul_inv]
      rw [hv]
      field_simp
    simp_rw [hmoment]
    have hν : Tendsto (fun ν : Ioi (0 : ℝ) => (ν : ℝ)) atTop atTop := by
      rw [← map_val_Ioi_atTop (0 : ℝ)]
      exact tendsto_map
    exact tendsto_const_nhds.div_atTop hν

private theorem map_prod_normalizedChiSquared {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (ν : Ioi (0 : ℝ)) :
    ((multivariateGaussian 0 S).toProbabilityMeasure.prod (normalizedChiSquared ν)).map
        (fun z => m + √(z.2.1⁻¹) • z.1) =
      (⟨multivariateTMeasure m S ν,
        isProbabilityMeasure_multivariateTMeasure m ν.2 hS⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ ι)) := by
  let _ := isProbabilityMeasure_chiSquaredMeasure ν.2.le
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
    ProbabilityMeasure.coe_mk, Measure.coe_toProbabilityMeasure]
  rw [multivariateTMeasure_of_posSemidef m ν.2 hS]
  have hreal : (fun z : EuclideanSpace ℝ ι × Ioi (0 : ℝ) =>
      m + √(z.2.1⁻¹) • z.1) = (fun z : EuclideanSpace ℝ ι × ℝ => m + √(z.2⁻¹) • z.1) ∘
      Prod.map id Subtype.val := rfl
  rw [hreal, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ measurable_id measurable_subtype_coe,
    map_val_normalizedChiSquared, Measure.map_id]
  have hprodmap : (multivariateGaussian 0 S).prod
      ((chiSquaredMeasure ν).map (fun x => x / ν.1)) =
      ((multivariateGaussian 0 S).prod (chiSquaredMeasure ν)).map
        (Prod.map id (fun x => x / ν.1)) := by
    simpa only [Measure.map_id, id_eq] using
      Measure.map_prod_map (multivariateGaussian 0 S) (chiSquaredMeasure ν)
        measurable_id (measurable_id.div_const ν.1)
  rw [hprodmap, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, inv_div]

/-- At fixed location and positive semidefinite scale, multivariate t laws converge weakly to
the Gaussian law with that location and covariance as the degrees of freedom tend to infinity.
This includes singular and zero scales and empty coordinate types. -/
theorem tendsto_multivariateTMeasure_atTop {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ ι)) (fun ν : Ioi (0 : ℝ) =>
      (⟨multivariateTMeasure m S ν,
        isProbabilityMeasure_multivariateTMeasure m ν.2 hS⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ ι))) atTop
      (𝓝 (multivariateGaussian m S).toProbabilityMeasure) := by
  let G := (multivariateGaussian 0 S).toProbabilityMeasure
  let f : EuclideanSpace ℝ ι × Ioi (0 : ℝ) → EuclideanSpace ℝ ι :=
    fun z => m + √(z.2.1⁻¹) • z.1
  have hf : Continuous f := by
    exact continuous_const.add
      ((Real.continuous_sqrt.comp
        ((continuous_subtype_val.comp continuous_snd).inv₀
          (fun z => z.2.2.ne'))).smul continuous_fst)
  have hprod : Tendsto (fun ν => G.prod (normalizedChiSquared ν)) atTop
      (𝓝 (G.prod
        (Measure.dirac (⟨1, mem_Ioi.mpr zero_lt_one⟩ : Ioi (0 : ℝ))).toProbabilityMeasure)) := by
    exact (ProbabilityMeasure.continuous_prod.tendsto _).comp
      (tendsto_const_nhds.prodMk_nhds tendsto_normalizedChiSquared)
  have hlim := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hprod hf
  have htarget : (G.prod
      (Measure.dirac (⟨1, mem_Ioi.mpr zero_lt_one⟩ : Ioi (0 : ℝ))).toProbabilityMeasure).map f =
        (multivariateGaussian m S).toProbabilityMeasure := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_prod,
      G, Measure.coe_toProbabilityMeasure]
    rw [Measure.prod_dirac, Measure.map_map hf.measurable measurable_prodMk_right]
    simpa [f, Function.comp_def, add_comm] using
      map_affine_multivariateGaussian 0 hS (1 : Matrix ι ι ℝ) m
  rw [htarget] at hlim
  simpa only [G, f, map_prod_normalizedChiSquared m hS] using hlim

end TauCeti.Probability
