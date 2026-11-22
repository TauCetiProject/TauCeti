/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.Complex.DividedDifference.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pi
import TauCeti.Analysis.Calculus.DSlope.Integral
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc

/-!
# Analyticity and integral representation of coordinate divided differences

Whenever `f : (ι → ℂ) → E` (with `ι` finite and `E` complete) is analytic at `z` and
`update z i ζ`, `TauCeti.partialDslope i f ζ` is analytic at `z`
(`TauCeti.analyticAt_partialDslope`). In particular, the divided difference of an entire function
is entire (`TauCeti.differentiable_partialDslope`) and admits the integral representation
`g z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt` (`TauCeti.partialDslope_eq_integral`).

## Main results

* `TauCeti.analyticAt_partialDslope`: `partialDslope i f ζ` is analytic at `z` when `f` is
  analytic at `z` and `update z i ζ`.
* `TauCeti.partialDslope_eq_integral`: integral representation of `partialDslope i f ζ` for
  entire `f`.
* `TauCeti.differentiable_partialDslope`: `partialDslope i f ζ` is entire when `f` is.
-/

public section

open Function Metric Set

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]
variable [CompleteSpace E]

/-- Local integral representation on `ball z r` across `ζ = z i` when `f` is complex
differentiable on `ball z r`. -/
private theorem partialDslope_eq_integral_partialDeriv_of_mem_ball [Fintype ι] {f : (ι → ℂ) → E}
    {z : ι → ℂ} {r : ℝ} (hr : 0 < r) (hf : DifferentiableOn ℂ f (ball z r)) (i : ι)
    {q : ι → ℂ} (hq : q ∈ ball z r) :
    partialDslope i f (z i) q =
      ∫ t in (0 : ℝ)..1, partialDeriv i f (update q i (z i + t • (q i - z i))) := by
  have hmem (w : ℂ) (hw : w ∈ ball (z i) r) : update q i w ∈ ball z r := by
    rw [mem_ball, dist_pi_lt_iff hr]
    intro j
    by_cases hj : j = i
    · subst hj; simpa using hw
    · simpa [hj] using (dist_le_pi_dist q z j).trans_lt (mem_ball.mp hq)
  have hline : DifferentiableOn ℂ (fun w ↦ f (update q i w)) (ball (z i) r) :=
    hf.comp (fun w _ ↦ (hasFDerivAt_update q w).differentiableAt.differentiableWithinAt) hmem
  have hqi : q i ∈ ball (z i) r :=
    mem_ball.mpr ((dist_le_pi_dist q z i).trans_lt (mem_ball.mp hq))
  have hseg : segment ℝ (z i) (q i) ⊆ ball (z i) r :=
    (convex_ball (z i) r).segment_subset (mem_ball_self hr) hqi
  rw [partialDslope_apply,
    dslope_eq_integral_deriv isOpen_ball (hline.contDiffOn isOpen_ball) hseg]
  refine intervalIntegral.integral_congr fun t ht ↦ ?_
  have hpt : z i + t • (q i - z i) ∈ ball (z i) r :=
    hseg (segment_eq_image' ℝ (z i) (q i) ▸
      mem_image_of_mem _ (uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1) ▸ ht))
  rw [partialDeriv_eq_deriv_update
    ((hf _ (hmem _ hpt)).differentiableAt (isOpen_ball.mem_nhds (hmem _ hpt))) i]
  simp only [update_idem, update_self]

/-- **Local analyticity of the coordinate divided difference.** If `f : (ι → ℂ) → E` is analytic at
`z` and at `update z i ζ`, then `partialDslope i f ζ` is analytic at `z`. On the hyperplane
`z i = ζ`, the two analyticity hypotheses coincide. -/
theorem analyticAt_partialDslope [Fintype ι] {f : (ι → ℂ) → E} {z : ι → ℂ} {i : ι} {ζ : ℂ}
    (hfz : AnalyticAt ℂ f z) (hfζ : AnalyticAt ℂ f (update z i ζ)) :
    AnalyticAt ℂ (partialDslope i f ζ) z := by
  rcases ne_or_eq (z i) ζ with hne | rfl
  · have hupd_diff : Differentiable ℂ (fun q : ι → ℂ ↦ update q i ζ) :=
      differentiable_pi.mpr fun j ↦ by
        by_cases hj : j = i
        · subst hj; simp
        · simpa [hj] using differentiable_apply j
    have hupd_an : AnalyticAt ℂ (fun q : ι → ℂ ↦ update q i ζ) z :=
      hupd_diff.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem
    have hinv : AnalyticAt ℂ (fun q : ι → ℂ ↦ (q i - ζ)⁻¹) z :=
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι ↦ ℂ) i).analyticAt z |>.sub
        analyticAt_const).inv (sub_ne_zero.mpr hne)
    refine (hinv.smul (hfz.sub (hfζ.comp_of_eq hupd_an rfl))).congr ?_
    filter_upwards [(continuousAt_apply i z).eventually_ne hne] with q hq
    exact (partialDslope_of_ne hq).symm
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hfz.eventually_analyticAt
    have hf_diff : DifferentiableOn ℂ f (ball z r) :=
      fun y hy ↦ (hball (mem_ball.mp hy)).differentiableAt.differentiableWithinAt
    have harg_an (t : ℂ) : AnalyticAt ℂ
        (fun p : (ι → ℂ) × ℂ ↦ update p.1 i (z i + p.2 * (p.1 i - z i))) (z, t) :=
      (differentiable_pi.mpr fun j ↦ by
        by_cases hj : j = i
        · subst hj; simp only [update_self]; fun_prop
        · simp only [update_of_ne hj]; fun_prop).differentiableOn.analyticAt_of_finiteDimensional
          Filter.univ_mem
    have hpf_an : AnalyticAt ℂ (partialDeriv i f) z := by
      rw [partialDeriv_def]
      exact ((ContinuousLinearMap.apply ℂ E (Pi.single i 1)).analyticAt _).comp hfz.fderiv
    have han := analyticAt_integral_smul (isCompact_Icc.image Complex.continuous_ofReal)
      (Complex.continuous_ofReal.comp (continuous_subtypeVal.comp continuous_projIcc))
      (fun t ↦ ⟨projIcc 0 1 zero_le_one t, (projIcc 0 1 zero_le_one t).property, rfl⟩)
      (fun t _ ↦ hpf_an.comp_of_eq (harg_an t) (by simp))
      ((continuous_const (y := (1 : ℂ))).integrableOn_Ioc :
        MeasureTheory.Integrable _ (MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)))
    refine han.congr ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr)] with q hq
    rw [partialDslope_eq_integral_partialDeriv_of_mem_ball hr hf_diff i hq,
      intervalIntegral.integral_of_le zero_le_one]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
    simp only [one_smul, Function.comp_apply, projIcc_of_mem zero_le_one (Ioc_subset_Icc_self ht),
      Complex.real_smul]

/-- **Integral representation of the divided difference.** For an entire `f`,
`partialDslope i f ζ z = ∫₀¹ ∂ᵢ f (update z i (ζ + t (z i - ζ))) dt`. -/
theorem partialDslope_eq_integral [Finite ι] {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) (z : ι → ℂ) :
    partialDslope i f ζ z =
      ∫ t in (0 : ℝ)..1, partialDeriv i f (update z i (ζ + t * (z i - ζ))) := by
  rw [partialDslope_apply, dslope_eq_integral_deriv isOpen_univ
    (differentiable_comp_update hf z i).contDiff.contDiffOn (subset_univ _)]
  congr 1 with t
  rw [Complex.real_smul, (hasDerivAt_comp_update (hf _)).deriv]

/-- **The divided difference of an entire function is entire.** -/
theorem differentiable_partialDslope [Finite ι] {f : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (i : ι) (ζ : ℂ) : Differentiable ℂ (partialDslope i f ζ) := by
  have := Fintype.ofFinite ι
  intro z
  exact (analyticAt_partialDslope
    (hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem)
    (hf.differentiableOn.analyticAt_of_finiteDimensional Filter.univ_mem)).differentiableAt

end TauCeti
