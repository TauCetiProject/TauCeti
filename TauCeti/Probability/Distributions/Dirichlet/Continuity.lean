/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Dirichlet.Density
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Analysis.SpecialFunctions.Gamma

/-!
# Weak continuity of Dirichlet laws

Dirichlet laws depend jointly weakly continuously on their positive concentration parameters.
The result uses the ordinary coordinate topology on positive shape vectors and the weak
topology on `ProbabilityMeasure (EuclideanSpace ℝ ι)`. It includes a single category, whose law
is the point mass at one.

The chart densities can diverge at the simplex boundary. Locally in parameter space they are
bounded by a constant multiple of the integrable chart density with all shapes halved.
Dominated convergence for bounded continuous test functions then gives weak continuity.
The construction uses `dirichletMeasure_eq_map_withDensity_dirichletChartPDF` and Mathlib's
bounded-continuous-test-function characterization of weak convergence.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Multivariate Distributions*, vol. 1,
  2nd ed., Wiley, 2000, Chapter 49.
-/

public section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- At each chart point the Dirichlet density is continuous in all positive shapes, even if
the chart point lies on or outside the simplex boundary. -/
@[fun_prop]
theorem continuous_dirichletChartPDFReal [DecidableEq ι] (i₀ : ι)
    (x : {i // i ≠ i₀} → ℝ) :
    Continuous (fun a : ι → Ioi (0 : ℝ) ↦
      dirichletChartPDFReal (fun i ↦ a i) i₀ x) := by
  let : Nonempty ι := ⟨i₀⟩
  by_cases hx : x ∈ dirichletChartRegion i₀
  · have hx' := mem_dirichletChartRegion_iff.mp hx
    simp only [dirichletChartPDFReal_of_mem _ hx]
    refine (continuous_Gamma_sum_div_prod.mul
      (continuous_finsetProd _ fun j _ ↦ ?_)).mul ?_
    · exact (Real.continuous_const_rpow (hx'.1 j).ne').comp (by fun_prop)
    · exact (Real.continuous_const_rpow (sub_pos.mpr hx'.2).ne').comp (by fun_prop)
  · simp only [dirichletChartPDFReal_of_notMem _ hx]
    exact continuous_const

private theorem eventually_dirichletChartPDFReal_le [DecidableEq ι] (i₀ : ι)
    (a : ι → Ioi (0 : ℝ)) :
    ∃ C : ℝ, ∀ᶠ b in 𝓝 a, ∀ x,
      dirichletChartPDFReal (fun i ↦ b i) i₀ x ≤
        C * dirichletChartPDFReal (fun i ↦ (a i : ℝ) / 2) i₀ x := by
  let : Nonempty ι := ⟨i₀⟩
  let N (b : ι → ℝ) := Real.Gamma (∑ i, b i) / ∏ i, Real.Gamma (b i)
  have hN (b : ι → ℝ) (hb : ∀ i, 0 < b i) : 0 < N b :=
    div_pos (Real.Gamma_pos_of_pos
      (Finset.sum_pos (fun i _ ↦ hb i) Finset.univ_nonempty))
      (Finset.prod_pos fun i _ ↦ Real.Gamma_pos_of_pos (hb i))
  have hhalf : 0 < N (fun i ↦ (a i : ℝ) / 2) := hN _ fun i ↦ half_pos (a i).2
  refine ⟨(N (fun i ↦ a i) + 1) / N (fun i ↦ (a i : ℝ) / 2), ?_⟩
  have hupper : ∀ᶠ b in 𝓝 a, N (fun i ↦ b i) < N (fun i ↦ a i) + 1 :=
    continuous_Gamma_sum_div_prod.continuousAt (gt_mem_nhds (lt_add_one _))
  have hlower : ∀ᶠ b in 𝓝 a, ∀ i, (a i : ℝ) / 2 < (b i : ℝ) := by
    rw [eventually_all]
    intro i
    exact (by fun_prop : Continuous (fun b : ι → Ioi (0 : ℝ) ↦ (b i : ℝ))).continuousAt
      (lt_mem_nhds (half_lt_self (a i).2))
  filter_upwards [hupper, hlower] with b hb hba x
  by_cases hx : x ∈ dirichletChartRegion i₀
  · have hx' := mem_dirichletChartRegion_iff.mp hx
    have hsum : 0 ≤ ∑ j, x j := Finset.sum_nonneg fun j _ ↦ (hx'.1 j).le
    have hcoord (j : {i // i ≠ i₀}) : x j ≤ 1 :=
      (Finset.single_le_sum (fun j _ ↦ (hx'.1 j).le) (Finset.mem_univ j)).trans hx'.2.le
    have hprod : (∏ j, x j ^ ((b j : ℝ) - 1)) ≤
        ∏ j, x j ^ ((a j : ℝ) / 2 - 1) := by
      exact Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (hx'.1 j).le _)
        fun j _ ↦ Real.rpow_le_rpow_of_exponent_ge (hx'.1 j) (hcoord j)
          (sub_le_sub_right (hba j).le 1)
    have hrest := Real.rpow_le_rpow_of_exponent_ge (sub_pos.mpr hx'.2)
      (sub_le_self 1 hsum) (sub_le_sub_right (hba i₀).le 1)
    rw [dirichletChartPDFReal_of_mem _ hx, dirichletChartPDFReal_of_mem _ hx]
    calc
      _ ≤ (N (fun i ↦ a i) + 1) * (∏ j, x j ^ ((a j : ℝ) / 2 - 1)) *
          (1 - ∑ j, x j) ^ ((a i₀ : ℝ) / 2 - 1) :=
        mul_le_mul (mul_le_mul hb.le hprod
          (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx'.1 j).le _)
          (add_nonneg (hN _ fun i ↦ (a i).2).le zero_le_one)) hrest
          (Real.rpow_nonneg (sub_pos.mpr hx'.2).le _)
          (mul_nonneg (add_nonneg (hN _ fun i ↦ (a i).2).le zero_le_one)
            (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx'.1 j).le _))
      _ = _ := by
        dsimp only [N] at hhalf ⊢
        simp only [← mul_assoc, div_mul_cancel₀ _ hhalf.ne']
  · simp [dirichletChartPDFReal_of_notMem _ hx]

/-- Dirichlet laws depend jointly weakly continuously on every positive concentration
parameter, including when there is just one category. -/
theorem continuous_dirichletMeasure [Nonempty ι] :
    Continuous (Y := ProbabilityMeasure (EuclideanSpace ℝ ι)) (fun a : ι → Ioi (0 : ℝ) ↦
      (⟨dirichletMeasure (fun i ↦ a i),
        isProbabilityMeasure_dirichletMeasure (fun i ↦ (a i).2)⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.2
  intro f
  have heq (a : ι → Ioi (0 : ℝ)) :
      ∫ x, f x ∂dirichletMeasure (fun i ↦ a i) =
        ∫ x, dirichletChartPDFReal (fun i ↦ a i) i₀ x * f (dirichletChart i₀ x) := by
    rw [dirichletMeasure_eq_map_withDensity_dirichletChartPDF (fun i ↦ (a i).2) i₀,
      integral_map measurable_dirichletChart.aemeasurable f.continuous.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul (measurable_dirichletChartPDF _ _)
        (ae_of_all _ fun _ ↦ by
          rw [dirichletChartPDF_eq_ofReal]
          exact ENNReal.ofReal_lt_top)]
    simp only [dirichletChartPDF_eq_ofReal,
      ENNReal.toReal_ofReal (dirichletChartPDFReal_nonneg (fun i ↦ (a i).2) i₀ _), smul_eq_mul]
  simp only [ProbabilityMeasure.coe_mk, heq]
  refine continuous_iff_continuousAt.2 fun a ↦ ?_
  obtain ⟨C, hC⟩ := eventually_dirichletChartPDFReal_le i₀ a
  apply continuousAt_of_dominated
    (bound := fun x ↦ C * dirichletChartPDFReal (fun i ↦ (a i : ℝ) / 2) i₀ x * ‖f‖)
  · exact .of_forall fun b ↦ ((measurable_dirichletChartPDFReal _ _).mul
      (f.continuous.measurable.comp measurable_dirichletChart)).aestronglyMeasurable
  · filter_upwards [hC] with b hb
    exact ae_of_all _ fun x ↦ by
      rw [norm_mul, Real.norm_of_nonneg (dirichletChartPDFReal_nonneg
        (fun i ↦ (b i).2) i₀ x)]
      exact mul_le_mul (hb x) (f.norm_coe_le_norm _) (norm_nonneg _)
        ((dirichletChartPDFReal_nonneg (fun i ↦ (b i).2) i₀ x).trans (hb x))
  · exact ((integrable_dirichletChartPDFReal (fun i ↦ half_pos (a i).2) i₀).const_mul C).mul_const _
  · exact ae_of_all _ fun x ↦
      ((continuous_dirichletChartPDFReal i₀ x).mul continuous_const).continuousAt

end TauCeti.Probability

namespace Continuous

variable {T ι : Type*} [TopologicalSpace T] [Fintype ι] [Nonempty ι]

/-- A continuous vector of positive shape parameters gives a weakly continuous Dirichlet law. -/
@[fun_prop]
theorem dirichletMeasure {a : T → ι → ℝ} (ha : Continuous a)
    (hpos : ∀ t i, 0 < a t i) :
    Continuous (Y := ProbabilityMeasure (EuclideanSpace ℝ ι)) (fun t ↦
      (⟨TauCeti.Probability.dirichletMeasure (a t),
        TauCeti.Probability.isProbabilityMeasure_dirichletMeasure (hpos t)⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  exact TauCeti.Probability.continuous_dirichletMeasure.comp
    (continuous_pi fun i ↦ ((continuous_apply i).comp ha).subtype_mk fun t ↦ hpos t i)

end Continuous
