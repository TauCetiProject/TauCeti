/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Moments
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Concentration
public import TauCeti.MeasureTheory.Measure.Dirac
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Algebra.Order.Field
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
private theorem sum_mul_dist_single_le_sqrt (x : EuclideanSpace ℝ ι)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∑ i, x i = 1) :
    ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ≤ Real.sqrt (1 - ‖x‖ ^ 2) := by
  classical
  have hdist (i : ι) :
      dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 = ‖x‖ ^ 2 - 2 * x i + 1 := by
    rw [EuclideanSpace.basisFun_apply, dist_eq_norm, norm_sub_sq_real,
      EuclideanSpace.inner_single_right]
    simp
  have hweighted :
      ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 = 1 - ‖x‖ ^ 2 := by
    simp_rw [hdist]
    calc
      ∑ i, x i * (‖x‖ ^ 2 - 2 * x i + 1) =
          ∑ i, (x i * ‖x‖ ^ 2 - 2 * (x i) ^ 2 + x i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ‖x‖ ^ 2 * ∑ i, x i - 2 * ∑ i, (x i) ^ 2 + ∑ i, x i := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ← Finset.mul_sum]
        ring
      _ = 1 - ‖x‖ ^ 2 := by
        rw [hx1, ← EuclideanSpace.real_norm_sq_eq]
        ring
  apply Real.le_sqrt_of_sq_le
  calc
    (∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i)) ^ 2 ≤
        (∑ i, x i) * ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) ^ 2 := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      · exact fun i _ ↦ hx0 i
      · exact fun i _ ↦ mul_nonneg (hx0 i) (sq_nonneg _)
      · intro i _
        rw [mul_pow]
        ring_nf
        exact le_rfl
    _ = 1 - ‖x‖ ^ 2 := by rw [hx1, one_mul, hweighted]

/-- The expected squared norm of a Dirichlet vector with concentration vector `c p`, where `p` is
a probability vector. As `c` tends to zero this tends to one, forcing the law towards the
vertices of the simplex. -/
theorem integral_norm_sq_dirichletMeasure_smul (p : Convexity.StdSimplex ℝ≥0 ι)
    (hp : ∀ i, 0 < p.weights i) {c : ℝ} (hc : 0 < c) :
    ∫ x, ‖x‖ ^ 2 ∂dirichletMeasure (fun i ↦ c * (p.weights i : ℝ)) =
      (c * ∑ i, (p.weights i : ℝ) ^ 2 + 1) / (c + 1) := by
  classical
  have ha (i : ι) : 0 < c * (p.weights i : ℝ) := by
    exact mul_pos hc (by exact_mod_cast hp i)
  let _ := isProbabilityMeasure_dirichletMeasure ha
  have hp_total : ∑ i, (p.weights i : ℝ) = 1 := by exact_mod_cast p.total_of_fintype
  have hsum : ∑ i, c * (p.weights i : ℝ) = c := by
    rw [← Finset.mul_sum]
    rw [hp_total, mul_one]
  have hcoord (i : ι) :
      ∫ x, (x i) ^ 2 ∂dirichletMeasure (fun j ↦ c * (p.weights j : ℝ)) =
        (p.weights i : ℝ) * (1 - p.weights i) / (c + 1) + (p.weights i : ℝ) ^ 2 := by
    have hv := variance_eval_dirichletMeasure ha i
    rw [variance_eq_sub (memLp_eval_dirichletMeasure i 2),
      integral_eval_dirichletMeasure ha, hsum] at hv
    calc
      _ = c * (p.weights i : ℝ) * (c - c * (p.weights i : ℝ)) /
            (c ^ 2 * (c + 1)) + (c * (p.weights i : ℝ) / c) ^ 2 :=
        eq_add_of_sub_eq hv
      _ = _ := by
        field_simp
  simp only [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ fun i _ ↦ (memLp_eval_dirichletMeasure i 2).integrable_sq]
  simp_rw [hcoord, Finset.sum_add_distrib, ← Finset.sum_div]
  field_simp
  ring_nf
  rw [Finset.sum_sub_distrib, hp_total]
  ring

/-- Decreasing the total concentration at fixed strictly positive weights makes the Dirichlet
laws converge weakly to the finite mixture of point masses at the simplex vertices. -/
theorem tendsto_dirichletMeasure_concentration_atBot (p : Convexity.StdSimplex ℝ≥0 ι)
    (hp : ∀ i, 0 < p.weights i) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ ι)) (fun c : Ioi (0 : ℝ) ↦
      (⟨dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)),
        isProbabilityMeasure_dirichletMeasure
          (fun i ↦ mul_pos c.2 (by exact_mod_cast hp i))⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ ι))) atBot
      (nhds (⟨∑ i, p.weights i • Measure.dirac (EuclideanSpace.basisFun ι ℝ i),
        TauCeti.isProbabilityMeasure_sum_smul_dirac p.total_of_fintype
          (EuclideanSpace.basisFun ι ℝ)⟩ :
            ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  classical
  apply MeasureTheory.tendsto_iff_forall_lipschitz_integral_tendsto.2
  rintro f hbound ⟨K, hK⟩
  let g : BoundedContinuousFunction (EuclideanSpace ℝ ι) ℝ :=
    ⟨⟨f, hK.continuous⟩, hbound⟩
  have htarget :
      ∫ x, f x ∂(∑ i, p.weights i • Measure.dirac (EuclideanSpace.basisFun ι ℝ i)) =
        ∑ i, (p.weights i : ℝ) * f (EuclideanSpace.basisFun ι ℝ i) := by
    rw [integral_finsetSum_measure]
    · simp only [EuclideanSpace.basisFun_apply, integral_smul_nnreal_measure,
        integral_dirac, NNReal.smul_def, smul_eq_mul]
    · exact fun i _ ↦ (integrable_dirac (by simp)).smul_measure (by simp)
  have herror (c : Ioi (0 : ℝ)) :
      dist
          (∫ x, f x ∂dirichletMeasure
            (fun i ↦ (c : ℝ) * (p.weights i : ℝ)))
          (∑ i, (p.weights i : ℝ) * f (EuclideanSpace.basisFun ι ℝ i)) ≤
        K * Real.sqrt
          (∫ x, (1 - ‖x‖ ^ 2) ∂dirichletMeasure
            (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) := by
    have ha (i : ι) : 0 < (c : ℝ) * (p.weights i : ℝ) :=
      mul_pos c.2 (by exact_mod_cast hp i)
    let _ := isProbabilityMeasure_dirichletMeasure ha
    have hsum : ∑ i, (c : ℝ) * (p.weights i : ℝ) = c := by
      rw [← Finset.mul_sum]
      have hp_total : ∑ i, (p.weights i : ℝ) = 1 := by
        exact_mod_cast p.total_of_fintype
      rw [hp_total, mul_one]
    have hf : Integrable f (dirichletMeasure
        (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) :=
      g.integrable (dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)))
    have hlinear : Integrable
        (fun x : EuclideanSpace ℝ ι ↦
          ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i))
        (dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) := by
      apply integrable_finsetSum Finset.univ
      intro i _
      exact ((memLp_eval_dirichletMeasure i 1).integrable (by norm_num)).mul_const _
    have hlinear_integral :
        ∫ x, (∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i))
            ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) =
          ∑ i, (p.weights i : ℝ) * f (EuclideanSpace.basisFun ι ℝ i) := by
      rw [integral_finsetSum _ fun i _ ↦
        ((memLp_eval_dirichletMeasure i 1).integrable (by norm_num)).mul_const _]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_mul_const, integral_eval_dirichletMeasure ha, hsum,
        mul_div_cancel_left₀ _ c.2.ne']
    have hpoint : ∀ᵐ x ∂dirichletMeasure
        (fun i ↦ (c : ℝ) * (p.weights i : ℝ)),
        |f x - ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i)| ≤
          K * Real.sqrt (1 - ‖x‖ ^ 2) := by
      filter_upwards [ae_pos_dirichletMeasure ha, ae_sum_eq_one_dirichletMeasure ha]
        with x hx0 hx1
      calc
        |f x - ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i)| =
            |∑ i, x i * (f x - f (EuclideanSpace.basisFun ι ℝ i))| := by
          congr 1
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hx1, one_mul]
        _ ≤ ∑ i, |x i * (f x - f (EuclideanSpace.basisFun ι ℝ i))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, x i * |f x - f (EuclideanSpace.basisFun ι ℝ i)| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_pos (hx0 i)]
        _ ≤ ∑ i, x i * (K * dist x (EuclideanSpace.basisFun ι ℝ i)) := by
          apply Finset.sum_le_sum
          intro i _
          apply mul_le_mul_of_nonneg_left _ (hx0 i).le
          simpa [Real.dist_eq] using hK.dist_le_mul x (EuclideanSpace.basisFun ι ℝ i)
        _ = K * ∑ i, x i * dist x (EuclideanSpace.basisFun ι ℝ i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ ≤ K * Real.sqrt (1 - ‖x‖ ^ 2) :=
          mul_le_mul_of_nonneg_left
            (sum_mul_dist_single_le_sqrt x (fun i ↦ (hx0 i).le) hx1) K.coe_nonneg
    have hsqrt_mem : MemLp (fun x : EuclideanSpace ℝ ι ↦ Real.sqrt (1 - ‖x‖ ^ 2)) 2
        (dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) := by
      apply MemLp.of_bound (by fun_prop) 1
      filter_upwards [ae_norm_le_one_dirichletMeasure] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_one.2 (by nlinarith [sq_nonneg ‖x‖])
    have hfirst :
        ∫ x, Real.sqrt (1 - ‖x‖ ^ 2)
            ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) ≤
          Real.sqrt
            (∫ x, (1 - ‖x‖ ^ 2)
              ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) := by
      have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
        (ae_of_all _ fun _ ↦ Real.sqrt_nonneg _)
        (ae_of_all _ fun _ ↦ (zero_le_one : (0 : ℝ) ≤ 1))
        (by simpa using hsqrt_mem)
        (by simpa using (memLp_const (1 : ℝ) :
          MemLp (fun _ : EuclideanSpace ℝ ι ↦ (1 : ℝ)) 2
            (dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)))))
      have hsquare :
          ∫ x, Real.sqrt (1 - ‖x‖ ^ 2) ^ 2
              ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) =
            ∫ x, (1 - ‖x‖ ^ 2)
              ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) := by
        apply integral_congr_ae
        filter_upwards [ae_norm_le_one_dirichletMeasure] with x hx
        rw [Real.sq_sqrt]
        nlinarith [norm_nonneg x]
      simpa only [mul_one, Real.one_rpow, integral_const, probReal_univ, one_smul,
        one_mul, one_pow, Real.rpow_two, ← one_div, ← Real.sqrt_eq_rpow,
        Real.sqrt_one, hsquare] using h
    calc
      _ = ‖∫ x, (f x - ∑ i, x i * f (EuclideanSpace.basisFun ι ℝ i))
          ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))‖ := by
        rw [integral_sub hf hlinear, hlinear_integral, Real.dist_eq, Real.norm_eq_abs]
      _ ≤ ∫ x, K * Real.sqrt (1 - ‖x‖ ^ 2)
          ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) :=
        norm_integral_le_of_norm_le (hsqrt_mem.integrable (by norm_num) |>.const_mul K) <|
          hpoint.mono fun x hx ↦ by simpa [Real.norm_eq_abs] using hx
      _ ≤ K * Real.sqrt
          (∫ x, (1 - ‖x‖ ^ 2)
            ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) := by
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hfirst K.coe_nonneg
  have hmoment (c : Ioi (0 : ℝ)) :
      ∫ x, (1 - ‖x‖ ^ 2)
          ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ)) =
        (c : ℝ) * (1 - ∑ i, (p.weights i : ℝ) ^ 2) / ((c : ℝ) + 1) := by
    have ha (i : ι) : 0 < (c : ℝ) * (p.weights i : ℝ) :=
      mul_pos c.2 (by exact_mod_cast hp i)
    let _ := isProbabilityMeasure_dirichletMeasure ha
    rw [integral_sub (integrable_const _) (memLp_id_dirichletMeasure 2).norm.integrable_sq,
      integral_const, probReal_univ, one_smul,
      integral_norm_sq_dirichletMeasure_smul p hp c.2]
    have hc1 : (c : ℝ) + 1 ≠ 0 := ne_of_gt (add_pos c.2 zero_lt_one)
    have h1c : 1 + (c : ℝ) ≠ 0 := ne_of_gt (add_pos zero_lt_one c.2)
    field_simp [hc1, h1c]
    ring
  have hcoe : Tendsto (fun c : Ioi (0 : ℝ) ↦ (c : ℝ)) atBot (𝓝 0) := by
    have h : Tendsto (id : ℝ → ℝ) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left inf_le_left
    rw [← map_coe_Ioi_atBot (0 : ℝ), tendsto_map'_iff, Function.comp_def] at h
    exact h
  have hzero : Tendsto (fun c : Ioi (0 : ℝ) ↦ K * Real.sqrt
      ((c : ℝ) * (1 - ∑ i, (p.weights i : ℝ) ^ 2) / ((c : ℝ) + 1)))
      atBot (𝓝 0) := by
    let A : ℝ := 1 - ∑ i, (p.weights i : ℝ) ^ 2
    have hnum : Tendsto (fun c : Ioi (0 : ℝ) ↦ (c : ℝ) * A) atBot (𝓝 (0 * A)) :=
      hcoe.mul tendsto_const_nhds
    have hden : Tendsto (fun c : Ioi (0 : ℝ) ↦ (c : ℝ) + 1) atBot (𝓝 (0 + 1)) :=
      hcoe.add tendsto_const_nhds
    have hquot := hnum.div hden (by norm_num : (0 : ℝ) + 1 ≠ 0)
    simpa [A] using hquot.sqrt.const_mul (K : ℝ)
  change Tendsto (fun c : Ioi (0 : ℝ) ↦
      ∫ x, f x ∂dirichletMeasure (fun i ↦ (c : ℝ) * (p.weights i : ℝ))) atBot
    (𝓝 (∫ x, f x ∂(∑ i, p.weights i • Measure.dirac (EuclideanSpace.basisFun ι ℝ i))))
  rw [htarget]
  apply tendsto_iff_dist_tendsto_zero.2
  exact squeeze_zero (fun _ ↦ dist_nonneg)
    (fun c ↦ (herror c).trans_eq (by rw [hmoment c])) hzero

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
