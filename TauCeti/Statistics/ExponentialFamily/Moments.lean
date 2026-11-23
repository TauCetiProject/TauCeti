/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.ExponentialFamily.Basic

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner

/-!
# Exponential moments at interior natural parameters

An interior parameter admits a strictly positive exponential moment of the norm under its
tilted law. In finite dimensions, a finite family of signed directions bounds the norm.
Consequently, the statistic belongs to every finite `Lᵖ` space under the tilted law.

## References

* L. D. Brown, *Fundamentals of Statistical Exponential Families* (1986), Theorem 2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace NNReal

namespace TauCeti

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {ν : Measure X} {T : X → E} {η : E} {r : ℝ}

/-- An integrable exponential envelope gives a whole ball of integrable weights. -/
theorem ball_subset_naturalParameterSpace
    (hT : AEStronglyMeasurable T ν)
    (h : Integrable (fun x ↦ exp (⟪η, T x⟫ + r * ‖T x‖)) ν) :
    Metric.ball η r ⊆ naturalParameterSpace ν T := by
  intro t ht
  rw [mem_naturalParameterSpace]
  have ht' : ‖t - η‖ ≤ r := by simpa only [dist_eq_norm] using (Metric.mem_ball.mp ht).le
  refine h.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
  calc
    ⟪t, T x⟫ = ⟪η, T x⟫ + ⟪t - η, T x⟫ := by rw [inner_sub_left]; ring
    _ ≤ ⟪η, T x⟫ + r * ‖T x‖ := by
      gcongr
      exact (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right ht' (norm_nonneg _))

/-- An interior natural parameter gives almost-everywhere strong measurability of the
statistic in finite dimensions, by recovering its coordinates from the exponential weights. -/
theorem aestronglyMeasurable_of_mem_interior_naturalParameterSpace [FiniteDimensional ℝ E]
    (hη : η ∈ interior (naturalParameterSpace ν T)) : AEStronglyMeasurable T ν := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hη)
  let b := stdOrthonormalBasis ℝ E
  have hmeas {t : E} (ht : t ∈ naturalParameterSpace ν T) :
      AEMeasurable (fun x ↦ ⟪t, T x⟫) ν :=
    aemeasurable_of_aemeasurable_exp (mem_naturalParameterSpace.mp ht).aemeasurable
  have hcoord (i : Fin (Module.finrank ℝ E)) :
      AEStronglyMeasurable (fun x ↦ b.repr (T x) i) ν := by
    let c := δ / 2
    have hc : 0 < c := half_pos hδ
    have hpert : η + c • b i ∈ naturalParameterSpace ν T := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left,
        norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs, abs_of_pos hc]
      exact half_lt_self hδ
    have hm := ((hmeas hpert).sub (hmeas (interior_subset hη))).div_const c
    have heq (x : X) : (⟪η + c • b i, T x⟫ - ⟪η, T x⟫) / c = b.repr (T x) i := by
      rw [inner_add_left, add_sub_cancel_left, real_inner_smul_left, mul_div_cancel_left₀ _ hc.ne',
        b.repr_apply_apply]
    exact (hm.congr (ae_of_all _ heq)).aestronglyMeasurable
  simpa only [b.sum_repr] using Finset.aestronglyMeasurable_fun_sum Finset.univ
    (f := fun i x ↦ b.repr (T x) i • b i) (fun i _ ↦
      (hcoord i).smul (aestronglyMeasurable_const (b := b i)))

/-- At an interior natural parameter in finite dimensions, an integrable exponential weight
dominates all the weights in a small ball, including an extra exponential factor in the norm. -/
theorem exists_integrable_exp_inner_add_mul_norm [FiniteDimensional ℝ E]
    (hη : η ∈ interior (naturalParameterSpace ν T)) :
    ∃ r > 0, Integrable (fun x ↦ exp (⟪η, T x⟫ + r * ‖T x‖)) ν := by
  have hT := aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hη)
  classical
  let d := Module.finrank ℝ E
  let b := stdOrthonormalBasis ℝ E
  let r : ℝ := δ / (d + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  let direction (s : Fin d → Bool) : E := ∑ i, (if s i then r else -r) • b i
  have hdir (s : Fin d → Bool) : ‖direction s‖ ≤ (d : ℝ) * r := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs]
    have habs (i : Fin d) : |if s i then r else -r| = r := by
      split <;> simp [abs_of_pos hr]
    simp [habs]
  have hpar (s : Fin d → Bool) : η + direction s ∈ naturalParameterSpace ν T := by
    apply hball
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
    refine (hdir s).trans_lt ?_
    have hδr : r * (d + 1) = δ := div_mul_cancel₀ _ (by positivity)
    linarith
  refine ⟨r, hr, (integrable_finsetSum Finset.univ fun s _ ↦
    mem_naturalParameterSpace.mp (hpar s)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)⟩
  let s : Fin d → Bool := fun i ↦ decide (0 ≤ b.repr (T x) i)
  have hnorm : ‖T x‖ ≤ ∑ i, |b.repr (T x) i| := calc
    ‖T x‖ = ‖∑ i, b.repr (T x) i • b i‖ := by rw [b.sum_repr]
    _ ≤ _ := by
      simpa [norm_smul, b.orthonormal.norm_eq_one, Real.norm_eq_abs] using
        (norm_sum_le Finset.univ fun i ↦ b.repr (T x) i • b i)
  have hsign (i : Fin d) :
      (if s i then r else -r) * ⟪b i, T x⟫ = r * |b.repr (T x) i| := by
    rw [← b.repr_apply_apply]
    by_cases hi : 0 ≤ b.repr (T x) i
    · simp [s, hi, abs_of_nonneg hi]
    · simp [s, hi, abs_of_neg (lt_of_not_ge hi)]
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
  refine le_trans (exp_le_exp.mpr ?_) (Finset.single_le_sum
    (f := fun s ↦ exp ⟪η + direction s, T x⟫) (fun _ _ ↦ (exp_pos _).le) (Finset.mem_univ s))
  simp only [direction, inner_add_left, sum_inner, real_inner_smul_left, hsign,
    ← Finset.mul_sum]
  gcongr

/-- In finite dimensions, lying in the interior of the natural domain is equivalent to
having an integrable exponential envelope of strictly positive radius. -/
theorem mem_interior_naturalParameterSpace_iff [FiniteDimensional ℝ E] :
    η ∈ interior (naturalParameterSpace ν T) ↔
      AEStronglyMeasurable T ν ∧
        ∃ r > 0, Integrable (fun x ↦ exp (⟪η, T x⟫ + r * ‖T x‖)) ν :=
  ⟨fun hη ↦ ⟨aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη,
    exists_integrable_exp_inner_add_mul_norm hη⟩, fun ⟨hT, r, hr, h⟩ ↦
      mem_interior_iff_mem_nhds.mpr
        (Metric.mem_nhds_iff.mpr ⟨r, hr, ball_subset_naturalParameterSpace hT h⟩)⟩

/-- Under a tilt at an interior natural parameter, the norm of the statistic has a positive
exponential moment. -/
theorem exists_integrable_exp_norm_exponentialFamilyMeasure [FiniteDimensional ℝ E]
    (hη : η ∈ interior (naturalParameterSpace ν T)) :
    ∃ r > 0, Integrable (fun x ↦ exp (r * ‖T x‖)) (exponentialFamilyMeasure ν T η) := by
  obtain ⟨r, hr, h⟩ := exists_integrable_exp_inner_add_mul_norm hη
  refine ⟨r, hr, ?_⟩
  rw [exponentialFamilyMeasure_def,
    integrable_tilted_iff (mem_naturalParameterSpace.mp (interior_subset hη))]
  simpa only [exp_add, smul_eq_mul] using h

/-- The statistic has finite moments of every finite order under an interior tilt. -/
theorem memLp_exponentialFamilyMeasure [FiniteDimensional ℝ E]
    (hη : η ∈ interior (naturalParameterSpace ν T)) (p : ℝ≥0) :
    MemLp T p (exponentialFamilyMeasure ν T η) := by
  let P := exponentialFamilyMeasure ν T η
  have hP : P ≪ ν := by
    dsimp only [P]
    rw [exponentialFamilyMeasure_def]
    exact tilted_absolutelyContinuous ν _
  have hTP := (aestronglyMeasurable_of_mem_interior_naturalParameterSpace hη).mono_ac hP
  obtain ⟨r, hr, h⟩ := exists_integrable_exp_norm_exponentialFamilyMeasure hη
  refine (memLp_norm_iff hTP).mp (memLp_of_mem_interior_integrableExpSet ?_ p)
  rw [mem_interior_iff_mem_nhds]
  refine Metric.mem_nhds_iff.mpr ⟨r, hr, fun t ht ↦ ?_⟩
  refine h.mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_exp]
  have ht' : |t| < r := by simpa [Real.dist_eq] using Metric.mem_ball.mp ht
  exact mul_le_mul_of_nonneg_right ((le_abs_self t).trans ht'.le) (norm_nonneg _)

end TauCeti
