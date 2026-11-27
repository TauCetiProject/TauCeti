/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.DeGiorgi
public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import TauCeti.Analysis.BoundedVariation.Weighted.ReducedBoundary
import TauCeti.Analysis.Distribution.TestFunction.Divergence
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Topology.Algebra.Module.Trace

/-!
# The weighted Gauss–Green formula

Let `W` be a `C¹` weight on a finite-dimensional real inner product space `E` of dimension
`n ≥ 2`, with measure `μ = e^{−W} · volume`, and let `U` be a set of locally finite perimeter in
an open set `Ω`, with reduced boundary `∂*U` and outer normal `ν_U`. For every `C¹` vector field
`X` with compact support in `Ω`,

`∫_U div_μ X dμ = ∫_{∂*U} ⟨X, ν_U⟩ e^{−W} dHⁿ⁻¹`,

where `div_μ X = div X − ⟨∇W, X⟩` is the weighted divergence
(`TauCeti.integral_weightedDivergence_eq_integral_reducedBoundary`). This is the Euclidean
Gauss–Green formula with surface measure
(`TauCeti.integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal`) applied to the
field `e^{−W} X`, whose divergence is `e^{−W} div_μ X` (`TauCeti.trace_fderiv_exp_neg_smul`).

The same identity holds without compact support when `μ` is finite, `U` is Lebesgue measurable of
finite weighted perimeter, `X` is bounded with bounded derivative and `DW X ∈ L¹(μ)`
(`TauCeti.integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded`): the formula for
the cut-off fields `χ(x / (k + 1)) X(x)` passes to the limit by dominated convergence, the
boundary side being dominated by `‖X‖_∞ e^{−W}`, which is integrable on `∂*U` because its
integral is the weighted perimeter.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), equation (3.1).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Module Filter
open scoped Topology
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {W : E → ℝ} {Ω : Opens E} {s : Set E}

/-- **The weighted Gauss–Green formula.** For a `C¹` weight `W`, in dimension `n ≥ 2`, a set `s`
of locally finite perimeter in `Ω` and a `C¹` vector field `X` with compact support in `Ω`,
`∫_s div_μ X dμ = ∫_{∂*s} ⟨X, ν_s⟩ e^{−W} dHⁿ⁻¹`, where `div_μ X = div X − DW X`. -/
theorem integral_weightedDivergence_eq_integral_reducedBoundary (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hu : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn volume U (s.indicator 1) ≠ ∞)
    {X : E → E} (hX : ContDiff ℝ 1 X) (hc : HasCompactSupport X) (hXΩ : tsupport X ⊆ Ω) :
    ∫ x, (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) - fderiv ℝ W x (X x)) *
        Real.exp (-W x) * s.indicator 1 x =
      ∫ x in reducedBoundary volume Ω s, ⟪X x, outerNormal volume Ω s x⟫ * Real.exp (-W x)
        ∂μHE[finrank ℝ E - 1] := by
  have hWd := hW.differentiable one_ne_zero
  have hφ : ContDiff ℝ 1 fun y => Real.exp (-W y) • X y := hW.neg.exp.smul hX
  have key := integral_trace_fderiv_mul_indicator_eq_setIntegral_inner_outerNormal hn hu hfin hφ
    hc.smul_left ((tsupport_smul_subset_right _ _).trans hXΩ)
  simp_rw [trace_fderiv_exp_neg_smul (hWd _) (hX.differentiable one_ne_zero _),
    real_inner_smul_left] at key
  rw [key]
  congr 1 with x
  ring

/-- The left side of the weighted Gauss–Green formula for the cut-off fields `g k • X` tends to
the one for `X`, by dominated convergence. -/
private theorem tendsto_integral_weightedDivergence_cutoff (hW : ContDiff ℝ 1 W)
    (hμ : Integrable fun x => Real.exp (-W x)) (hs : NullMeasurableSet s) {X : E → E}
    (hX : ContDiff ℝ 1 X) {C C' : ℝ} (hXC : ∀ x, ‖X x‖ ≤ C) (hXC' : ∀ x, ‖fderiv ℝ X x‖ ≤ C')
    (hWX : Integrable fun x => fderiv ℝ W x (X x) * Real.exp (-W x)) {g : ℕ → E → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hg : ∀ k, ContDiff ℝ 1 (g k)) (hg1 : ∀ k x, |g k x| ≤ 1)
    (hgt : ∀ x, Tendsto (g · x) atTop (𝓝 1))
    (hgd : ∀ k x, ‖fderiv ℝ (g k) x‖ ≤ 1 / ((k : ℝ) + 1) * B) :
    Tendsto (fun k => ∫ x, (g k x * LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) +
      fderiv ℝ (g k) x (X x) - g k x * fderiv ℝ W x (X x)) * Real.exp (-W x) * s.indicator 1 x)
      atTop (𝓝 (∫ x, (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) - fderiv ℝ W x (X x)) *
        Real.exp (-W x) * s.indicator 1 x)) := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hXC 0)
  have hgX (k : ℕ) (x : E) : ‖fderiv ℝ (g k) x (X x)‖ ≤ 1 / ((k : ℝ) + 1) * B * C :=
    ((fderiv ℝ (g k) x).le_opNorm _).trans (mul_le_mul (hgd k x) (hXC x) (norm_nonneg _)
      (by positivity))
  have hgX' (k : ℕ) (x : E) : ‖fderiv ℝ (g k) x (X x)‖ ≤ B * C :=
    (hgX k x).trans (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hB
      (div_le_one_of_le₀ (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (by positivity))) hC)
  have hgt' (x : E) : Tendsto (fun k => fderiv ℝ (g k) x (X x)) atTop (𝓝 0) :=
    squeeze_zero_norm (hgX · x) (by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.mul_const B).mul_const C)
  have htrC (x : E) : ‖LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E)‖ ≤ ‖traceCLM ℝ E‖ * C' := by
    rw [← traceCLM_apply]
    exact ((traceCLM ℝ E).le_opNorm _).trans (by gcongr; exact hXC' x)
  refine tendsto_integral_of_dominated_convergence
    (fun x => (‖traceCLM ℝ E‖ * C' + B * C) * Real.exp (-W x) +
      ‖fderiv ℝ W x (X x) * Real.exp (-W x)‖) (fun k => ?_) ((hμ.const_mul _).add hWX.norm)
    (fun k => Eventually.of_forall fun x => ?_) (Eventually.of_forall fun x => ?_)
  · refine (Continuous.aestronglyMeasurable ?_).mul (aestronglyMeasurable_const.indicator₀ hs)
    have := (hg k).continuous
    have := ((hg k).continuous_fderiv one_ne_zero).clm_apply hX.continuous
    have := (hW.continuous_fderiv one_ne_zero).clm_apply hX.continuous
    have := hW.continuous
    have : Continuous fun x => LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) :=
      ((traceCLM ℝ E).continuous.comp (hX.continuous_fderiv one_ne_zero)).congr fun x => by simp
    fun_prop
  · have he : 0 < Real.exp (-W x) := Real.exp_pos _
    have hind : ‖s.indicator (1 : E → ℝ) x‖ ≤ 1 := by by_cases hx : x ∈ s <;> simp [hx]
    rw [norm_mul, norm_mul, Real.norm_of_nonneg he.le, norm_mul, Real.norm_of_nonneg he.le]
    refine (mul_le_of_le_one_right (by positivity) hind).trans ?_
    have h1 : ‖g k x * LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) +
        fderiv ℝ (g k) x (X x) - g k x * fderiv ℝ W x (X x)‖ ≤
        ‖traceCLM ℝ E‖ * C' + B * C + ‖fderiv ℝ W x (X x)‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_
        (hgX' k x))) ?_) <;> rw [norm_mul, Real.norm_eq_abs]
      · exact (mul_le_of_le_one_left (norm_nonneg _) (hg1 k x)).trans (htrC x)
      · exact mul_le_of_le_one_left (norm_nonneg _) (hg1 k x)
    nlinarith
  · have h := ((((hgt x).mul_const
      (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E))).add (hgt' x)).sub ((hgt x).mul_const
      (fderiv ℝ W x (X x)))).mul_const (Real.exp (-W x) * s.indicator 1 x)
    simpa only [one_mul, add_zero, mul_assoc] using h

/-- For a bounded continuous field `X`, the boundary integrand `⟨X, ν_s⟩ e^{−W}` of the weighted
Gauss–Green formula is integrable on the reduced boundary of a set of finite weighted perimeter:
it is dominated by `‖X‖_∞ e^{−W}`, whose integral there is a multiple of the weighted perimeter. -/
private theorem integrable_inner_outerNormal_mul_exp_neg (hW : ContDiff ℝ 1 W)
    (hn : 2 ≤ finrank ℝ E) (hs : NullMeasurableSet s (volume.restrict ((⊤ : Opens E) : Set E)))
    (hP : weightedPerimeter W ⊤ s ≠ ∞) {X : E → E} (hX : Continuous X) {C : ℝ}
    (hXC : ∀ x, ‖X x‖ ≤ C) :
    Integrable (fun x => ⟪X x, outerNormal volume ⊤ s x⟫ * Real.exp (-W x))
      ((μHE[finrank ℝ E - 1]).restrict (reducedBoundary volume ⊤ s)) := by
  have hexp : Continuous fun x => Real.exp (-W x) := (hW.continuous.neg).rexp
  have hexpi : Integrable (fun x => Real.exp (-W x))
      ((μHE[finrank ℝ E - 1]).restrict (reducedBoundary volume ⊤ s)) :=
    ⟨hexp.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun x => (Real.exp_pos _).le)).2
      (weightedPerimeter_eq_lintegral_reducedBoundary_of_ne_top hW hn hs hP ▸ hP.lt_top)⟩
  refine (hexpi.const_mul C).mono' ((hX.aestronglyMeasurable.inner
    measurable_outerNormal.aestronglyMeasurable).mul hexp.aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_reducedBoundary] with x hx
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  gcongr
  exact (norm_inner_le_norm _ _).trans (by rw [norm_outerNormal hx, mul_one]; exact hXC x)

/-- **The weighted Gauss–Green formula for bounded fields.** For a `C¹` weight `W` whose measure
`μ = e^{−W} · volume` is finite, in dimension `n ≥ 2`, a Lebesgue-measurable set `s` of finite
weighted perimeter and a `C¹` vector field `X`, bounded with bounded derivative, with
`DW X ∈ L¹(μ)`: `∫_s div_μ X dμ = ∫_{∂*s} ⟨X, ν_s⟩ e^{−W} dHⁿ⁻¹`, where `div_μ X = div X − DW X`.
The field `X` need not have compact support. -/
theorem integral_weightedDivergence_eq_integral_reducedBoundary_of_bounded
    (hW : ContDiff ℝ 1 W) (hn : 2 ≤ finrank ℝ E) (hμ : Integrable fun x => Real.exp (-W x))
    (hs : NullMeasurableSet s) (hP : weightedPerimeter W ⊤ s ≠ ∞) {X : E → E}
    (hX : ContDiff ℝ 1 X) {C C' : ℝ} (hXC : ∀ x, ‖X x‖ ≤ C) (hXC' : ∀ x, ‖fderiv ℝ X x‖ ≤ C')
    (hWX : Integrable fun x => fderiv ℝ W x (X x) * Real.exp (-W x)) :
    ∫ x, (LinearMap.trace ℝ E (fderiv ℝ X x : E →ₗ[ℝ] E) - fderiv ℝ W x (X x)) *
        Real.exp (-W x) * s.indicator 1 x =
      ∫ x in reducedBoundary volume ⊤ s, ⟪X x, outerNormal volume ⊤ s x⟫ * Real.exp (-W x)
        ∂μHE[finrank ℝ E - 1] := by
  have hs' : NullMeasurableSet s (volume.restrict ((⊤ : Opens E) : Set E)) :=
    hs.mono_ac Measure.restrict_le_self.absolutelyContinuous
  have hu := locallyIntegrableOn_indicator_const hs' (1 : ℝ)
  have hfin := exists_totalVariationOn_ne_top_of_weightedVariation_ne_top hW hu
    (weightedPerimeter_def (W := W) ▸ hP)
  obtain ⟨B, hB, hcut⟩ := exists_cutoff_fderiv_bound (E := E)
  choose g g' hg hg01 hg1 hg0 hgd' hgd _ _ using
    fun k : ℕ => hcut 0 ((k : ℝ) + 1) (by positivity)
  replace hg (k : ℕ) : ContDiff ℝ 1 (g k) := hg k 1
  have hgc (k : ℕ) : HasCompactSupport (g k) :=
    HasCompactSupport.intro (isCompact_closedBall 0 (2 * ((k : ℝ) + 1))) fun x hx =>
      hg0 k x (by simpa [dist_zero_right] using hx)
  have hgI (k : ℕ) (x : E) : g k x ∈ Icc (0 : ℝ) 1 := hg01 k x
  replace hg01 (k : ℕ) (x : E) : |g k x| ≤ 1 := abs_le.2 ⟨by linarith [(hg01 k x).1], (hg01 k x).2⟩
  have hgt (x : E) : Tendsto (g · x) atTop (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop ‖x‖] with k hk
    exact (hg1 k x (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)).symm
  replace hgd (k : ℕ) (x : E) : ‖fderiv ℝ (g k) x‖ ≤ 1 / ((k : ℝ) + 1) * B := by
    rw [(hgd' k x).fderiv, one_div, mul_comm]
    exact hgd k x
  have hright : Tendsto (fun k : ℕ => ∫ x in reducedBoundary volume ⊤ s,
      ⟪g k x • X x, outerNormal volume ⊤ s x⟫ * Real.exp (-W x) ∂μHE[finrank ℝ E - 1])
      atTop (𝓝 (∫ x in reducedBoundary volume ⊤ s,
        ⟪X x, outerNormal volume ⊤ s x⟫ * Real.exp (-W x) ∂μHE[finrank ℝ E - 1])) := by
    refine (tendsto_integral_smul_of_eq_one_ball (R := fun k : ℕ => (k : ℝ) + 1)
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
      (fun k => (hg k).continuous.aestronglyMeasurable)
      (fun k x hx => hg1 k x (mem_closedBall_zero_iff.2 hx.le)) hgI
      (integrable_inner_outerNormal_mul_exp_neg hW hn hs' hP hX.continuous hXC)).congr fun k => ?_
    congr 1 with x
    rw [real_inner_smul_left, smul_eq_mul, mul_assoc]
  refine tendsto_nhds_unique ((tendsto_integral_weightedDivergence_cutoff hW hμ hs hX hXC hXC'
    hWX hB hg hg01 hgt hgd).congr fun k => ?_) hright
  rw [← integral_weightedDivergence_eq_integral_reducedBoundary hW hn hu hfin
    (X := fun x => g k x • X x) ((hg k).smul hX) ((hgc k).smul_right) (subset_univ _)]
  congr 1 with x
  rw [trace_fderiv_smul ((hg k).differentiable one_ne_zero _)
    ((hX.differentiable one_ne_zero) _), map_smul, smul_eq_mul]

end TauCeti
