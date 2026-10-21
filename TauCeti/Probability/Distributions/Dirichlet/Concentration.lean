/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Moments
public import TauCeti.Probability.Distributions.Categorical
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Concentration
import TauCeti.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.AtTopBotIxx

/-!
# Dirichlet concentration at a fixed probability vector

For a strictly positive probability vector `p`, the Dirichlet law with parameters `c * p`
converges weakly to the point mass at `p` as the total concentration `c` tends to infinity.
Its mean squared Euclidean distance from `p` is exactly
`(1 - ∑ i, p.weights i ^ 2) / (c + 1)`. The formula also includes a single category, where
the law is already a point mass and this distance is zero.

The calculation sums the existing coordinate variance formulas. The weak limit follows
from the second-moment concentration criterion for probability measures.

At the opposite extreme, when the total concentration tends to zero, the law converges to the
categorical mixture of the simplex vertices. This follows by coupling a simplex point with a
vertex chosen using its own coordinates: the mean squared distance of this coupling is
`1 - ‖x‖ ^ 2`, whose Dirichlet expectation tends to zero.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem sum_coe_weights (p : Convexity.StdSimplex ℝ≥0 ι) :
    ∑ i, (p.weights i : ℝ) = 1 := by
  exact_mod_cast p.total_of_fintype

omit [Nonempty ι] in
private theorem sum_mul_coe_weights (p : Convexity.StdSimplex ℝ≥0 ι) (c : ℝ) :
    ∑ i, c * (p.weights i : ℝ) = c := by
  rw [← Finset.mul_sum, sum_coe_weights, mul_one]

/-- The expected squared norm of a Dirichlet vector with concentration vector `c p`, where `p` is
a probability vector. As `c` tends to zero this tends to one, forcing the law towards the
vertices of the simplex. -/
theorem integral_norm_sq_dirichletMeasure_smul (p : Convexity.StdSimplex ℝ≥0 ι)
    (hp : ∀ i, 0 < p.weights i) {c : ℝ} (hc : 0 < c) :
    ∫ x, ‖x‖ ^ 2 ∂dirichletMeasure (fun i ↦ c * (p.weights i : ℝ)) =
      (c * ∑ i, (p.weights i : ℝ) ^ 2 + 1) / (c + 1) := by
  have ha (i : ι) : 0 < c * (p.weights i : ℝ) := mul_pos hc (by exact_mod_cast hp i)
  let _ := isProbabilityMeasure_dirichletMeasure ha
  have hcoord (i : ι) :
      ∫ x, (x i) ^ 2 ∂dirichletMeasure (fun j ↦ c * (p.weights j : ℝ)) =
        (p.weights i : ℝ) * (1 - p.weights i) / (c + 1) + (p.weights i : ℝ) ^ 2 := by
    have hv := variance_eval_dirichletMeasure ha i
    rw [variance_eq_sub (memLp_eval_dirichletMeasure i 2),
      integral_eval_dirichletMeasure ha, sum_mul_coe_weights] at hv
    calc
      _ = c * (p.weights i : ℝ) * (c - c * (p.weights i : ℝ)) /
            (c ^ 2 * (c + 1)) + (c * (p.weights i : ℝ) / c) ^ 2 :=
        eq_add_of_sub_eq hv
      _ = _ := by field_simp
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun i _ ↦ (memLp_eval_dirichletMeasure i 2).integrable_sq]
  simp_rw [hcoord, Finset.sum_add_distrib, ← Finset.sum_div, mul_sub, mul_one,
    Finset.sum_sub_distrib, sum_coe_weights, ← pow_two]
  field_simp
  ring

/-- Decreasing the total concentration at fixed strictly positive weights makes the Dirichlet
laws converge weakly to the categorical law on the simplex vertices with the same weights. -/
theorem tendsto_dirichletMeasure_concentration_atBot [MeasurableSpace ι]
    [MeasurableSingletonClass ι] (p : Convexity.StdSimplex ℝ≥0 ι) (hp : ∀ i, 0 < p.weights i) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ ι)) (fun c : Ioi (0 : ℝ) ↦
      (⟨dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)),
        isProbabilityMeasure_dirichletMeasure
          (fun i ↦ mul_pos c.2 (by exact_mod_cast hp i))⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ ι))) atBot
      (𝓝 ((categoricalMeasure p).map (EuclideanSpace.basisFun ι ℝ)).toProbabilityMeasure) := by
  have ha (c : Ioi (0 : ℝ)) (i : ι) : 0 < (c : ℝ) * (p.weights i : ℝ) :=
    mul_pos c.2 (by exact_mod_cast hp i)
  have hsqrt_mem (c : Ioi (0 : ℝ)) :
      MemLp (fun x : EuclideanSpace ℝ ι ↦ √(1 - ‖x‖ ^ 2)) 2
        (dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) := by
    let _ := isProbabilityMeasure_dirichletMeasure (ha c)
    apply MemLp.of_bound (by fun_prop) 1
    filter_upwards [ae_norm_le_one_dirichletMeasure] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_one.2 (by nlinarith [sq_nonneg ‖x‖])
  have hmoment (c : Ioi (0 : ℝ)) :
      ∫ x, √(1 - ‖x‖ ^ 2) ^ 2 ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) =
        (c : ℝ) * (1 - ∑ i, (p.weights i : ℝ) ^ 2) / ((c : ℝ) + 1) := by
    let _ := isProbabilityMeasure_dirichletMeasure (ha c)
    have hsq : ∀ᵐ x ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)),
        √(1 - ‖x‖ ^ 2) ^ 2 = 1 - ‖x‖ ^ 2 := by
      filter_upwards [ae_norm_le_one_dirichletMeasure] with x hx
      exact Real.sq_sqrt (by nlinarith [norm_nonneg x])
    rw [integral_congr_ae hsq,
      integral_sub (integrable_const _) (memLp_id_dirichletMeasure 2).norm.integrable_sq,
      integral_const, probReal_univ, one_smul, integral_norm_sq_dirichletMeasure_smul p hp c.2]
    have hc1 : (c : ℝ) + 1 ≠ 0 := (add_pos c.2 zero_lt_one).ne'
    field_simp
    ring
  refine ProbabilityMeasure.tendsto_of_lipschitz_approx_of_integral_sq_tendsto_zero
    (d := fun _ x ↦ √(1 - ‖x‖ ^ 2)) hsqrt_mem ?_ fun f K _ hK c ↦
      ⟨fun x ↦ ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i), ?_, ?_, ?_⟩
  · have hcoe : Tendsto (fun c : Ioi (0 : ℝ) ↦ (c : ℝ)) atBot (𝓝 0) := by
      have h : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
      rwa [← map_coe_Ioi_atBot (0 : ℝ), tendsto_map'_iff, Function.comp_def] at h
    have hquot : Tendsto (fun c : Ioi (0 : ℝ) ↦
        (c : ℝ) * (1 - ∑ i, (p.weights i : ℝ) ^ 2) / ((c : ℝ) + 1)) atBot
        (𝓝 (0 * (1 - ∑ i, (p.weights i : ℝ) ^ 2) / (0 + 1))) :=
      (hcoe.mul_const _).div (hcoe.add_const 1) (by norm_num)
    simpa only [ProbabilityMeasure.coe_mk, hmoment, zero_mul, zero_div] using hquot
  · let _ := isProbabilityMeasure_dirichletMeasure (ha c)
    exact integrable_finsetSum _ fun i _ ↦
      ((memLp_eval_dirichletMeasure i 1).integrable (by norm_num)).mul_const _
  · let _ := isProbabilityMeasure_dirichletMeasure (ha c)
    simp only [ProbabilityMeasure.coe_mk, Measure.coe_toProbabilityMeasure]
    rw [integral_map (measurable_of_finite _).aemeasurable hK.continuous.aestronglyMeasurable,
      integral_categoricalMeasure, integral_finsetSum _ fun i _ ↦
        ((memLp_eval_dirichletMeasure i 1).integrable (by norm_num)).mul_const _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_mul_const, integral_eval_dirichletMeasure (ha c), sum_mul_coe_weights,
      mul_div_cancel_left₀ _ c.2.ne', smul_eq_mul]
  · simp only [ProbabilityMeasure.coe_mk]
    filter_upwards [ae_pos_dirichletMeasure (ha c), ae_sum_eq_one_dirichletMeasure (ha c)]
      with x hx0 hx1
    calc
      |f x - ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i)| =
          |∑ i, x i * (f x - f (EuclideanSpace.basisFun ι ℝ i))| := by
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hx1, one_mul]
      _ ≤ ∑ i, x i * |f x - f (EuclideanSpace.basisFun ι ℝ i)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans_eq (Finset.sum_congr rfl fun i _ ↦ ?_)
        rw [abs_mul, abs_of_pos (hx0 i)]
      _ ≤ ∑ i, x i * (K * dist x (EuclideanSpace.basisFun ι ℝ i)) := by
        refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left ?_ (hx0 i).le
        simpa [Real.dist_eq] using hK.dist_le_mul x (EuclideanSpace.basisFun ι ℝ i)
      _ = K * ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ ↦ by ring
      _ ≤ K * √(1 - ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (EuclideanSpace.sum_mul_dist_basisFun_le_sqrt (fun i ↦ (hx0 i).le) hx1) K.coe_nonneg

/-- The mean squared distance from the fixed mean of a Dirichlet law is the sum of its
coordinate variances. It decays inversely with one plus the total concentration. -/
theorem integral_norm_sub_sq_dirichletMeasure_smul (p : Convexity.StdSimplex ℝ ι)
    (hp : ∀ i, 0 < p.weights i) {c : ℝ} (hc : 0 < c) :
    ∫ x, ‖x - (EuclideanSpace.equiv ι ℝ).symm p.weights‖ ^ 2
      ∂dirichletMeasure (fun i ↦ c * p.weights i) =
        (1 - ∑ i, p.weights i ^ 2) / (c + 1) := by
  have ha (i : ι) : 0 < c * p.weights i := mul_pos hc (hp i)
  let _ := isProbabilityMeasure_dirichletMeasure ha
  have hsum : ∑ i, c * p.weights i = c := by simp [← Finset.mul_sum]
  have hcoord (i : ι) :
      ∫ x, (x i - p.weights i) ^ 2 ∂dirichletMeasure (fun j ↦ c * p.weights j) =
        p.weights i * (1 - p.weights i) / (c + 1) := by
    have hv := variance_eval_dirichletMeasure ha i
    rw [variance_eq_integral (by fun_prop), integral_eval_dirichletMeasure ha, hsum,
      mul_div_cancel_left₀ _ hc.ne'] at hv
    rw [hv]
    field_simp
  simp only [EuclideanSpace.real_norm_sq_eq, PiLp.sub_apply,
    PiLp.continuousLinearEquiv_symm_apply]
  have hint (i : ι) : Integrable (fun x : EuclideanSpace ℝ ι ↦ (x i - p.weights i) ^ 2)
      (dirichletMeasure (fun j ↦ c * p.weights j)) := by
    simpa only [Pi.sub_apply] using
      ((memLp_eval_dirichletMeasure (a := fun j ↦ c * p.weights j) i 2).sub
        (memLp_const (p.weights i))).integrable_sq
  rw [integral_finsetSum _ fun i _ ↦ hint i]
  simp_rw [hcoord, ← Finset.sum_div]
  congr 1
  simp [mul_sub, mul_one, Finset.sum_sub_distrib, ← sq]

/-- Increasing the total concentration at fixed strictly positive simplex weights makes the
Dirichlet laws converge weakly to the point mass at those weights. -/
theorem tendsto_dirichletMeasure_concentration_atTop (p : Convexity.StdSimplex ℝ ι)
    (hp : ∀ i, 0 < p.weights i) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ ι)) (fun c : Ioi (0 : ℝ) ↦
      (⟨dirichletMeasure (fun i ↦ (c : ℝ) * p.weights i),
        isProbabilityMeasure_dirichletMeasure (fun i ↦ mul_pos c.2 (hp i))⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ ι))) atTop
      (𝓝 (⟨Measure.dirac ((EuclideanSpace.equiv ι ℝ).symm p.weights), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  apply ProbabilityMeasure.tendsto_dirac_of_integral_dist_sq_tendsto_zero
  · intro c
    let _ := isProbabilityMeasure_dirichletMeasure (fun i ↦ mul_pos c.2 (hp i))
    simpa only [dist_eq_norm, Pi.sub_apply, id_eq, ProbabilityMeasure.coe_mk] using
      ((memLp_id_dirichletMeasure (a := fun i ↦ (c : ℝ) * p.weights i) 2).sub
        (memLp_const ((EuclideanSpace.equiv ι ℝ).symm p.weights))).norm
  · simp only [ProbabilityMeasure.coe_mk, dist_eq_norm]
    have hcoe : Tendsto (fun c : Ioi (0 : ℝ) ↦ (c : ℝ)) atTop atTop := by
      rw [← map_val_Ioi_atTop (0 : ℝ)]
      exact tendsto_map
    have hlim : Tendsto (fun c : Ioi (0 : ℝ) ↦
        (1 - ∑ i, p.weights i ^ 2) / ((c : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 1 hcoe)
    convert hlim using 1
    ext c
    exact integral_norm_sub_sq_dirichletMeasure_smul p hp c.2

end TauCeti.Probability
