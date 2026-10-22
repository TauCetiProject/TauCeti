/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.FiniteMeasure
public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.Analysis.CompletelyMonotone.Laplace.Representation
-- Non-public: `Real.exp_neg_one_lt_half` calibrates the radius in the tail estimate.
import Mathlib.Analysis.Complex.ExponentialBounds
-- Non-public: Prokhorov compactness for mass-bounded tight sets of finite measures.
import TauCeti.MeasureTheory.Measure.Prokhorov

/-!
# The continuity theorem for Laplace transforms

For finite measures on `ℝ≥0`, weak convergence is the same as pointwise convergence of the
Laplace transforms on `[0, ∞)`. This is the Laplace-transform analogue of Lévy's continuity
theorem for characteristic functions (Mathlib's `ProbabilityMeasure.tendsto_iff_tendsto_charFun`).

The substantial direction is the existence form: if the Laplace transforms of a sequence of finite
measures converge pointwise on `[0, ∞)` to a function `f` that is right-continuous at `0`, then
`f` is the Laplace transform of a finite measure, and the sequence converges weakly to it. The
continuity of `f` at `0` controls the escape of mass to infinity through the Markov tail bound
`TauCeti.measure_compl_closedBall_le_sub_laplaceTransform_div`, which makes the sequence tight;
Prokhorov's theorem then supplies weak cluster points, and Laplace uniqueness identifies them.

On the side of functions, this is the measure-theoretic counterpart of the closure of completely
monotone functions under pointwise limits: through `TauCeti.RepresentsLaplace`, the representing
measures of the approximants converge weakly to the representing measure of the limit.

## Main declarations

* `Filter.Tendsto.laplaceTransform`: weak convergence of finite measures implies
  convergence of their Laplace transforms at every `t ≥ 0`.
* `TauCeti.isTightMeasureSet_range_of_tendsto_laplaceTransform`: a sequence of finite measures
  whose Laplace transforms converge on `[0, ∞)` to a function right-continuous at `0` is tight.
* `TauCeti.exists_representsLaplace_and_tendsto_of_tendsto_laplaceTransform`: the continuity
  theorem, in existence form.
* `TauCeti.tendsto_iff_forall_tendsto_laplaceTransform`: weak convergence of finite measures on
  `ℝ≥0` is equivalent to pointwise convergence of their Laplace transforms on `[0, ∞)`.

## References

* W. Feller, *An Introduction to Probability Theory and Its Applications*, Vol. II
  (2nd ed., Wiley, 1971), Chapter XIII.1, Theorem 2.
* Mathlib's `Mathlib/MeasureTheory/Measure/LevyConvergence.lean` (R. Degenne): the
  tightness-then-identify-every-ultrafilter-limit argument here adapts its proof of Lévy's
  convergence theorem from characteristic functions to Laplace transforms.
-/

public section

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace TauCeti

/-- **Laplace transforms are weakly continuous.** If finite measures on `ℝ≥0` converge weakly,
then their Laplace transforms converge at every parameter `t ≥ 0`: the kernel `p ↦ e^{-tp}` is a
bounded continuous test function. -/
theorem _root_.Filter.Tendsto.laplaceTransform {ι : Type*} {l : Filter ι}
    {μs : ι → FiniteMeasure ℝ≥0} {μ : FiniteMeasure ℝ≥0} (h : Tendsto μs l (𝓝 μ)) {t : ℝ}
    (ht : 0 ≤ t) :
    Tendsto (fun i => laplaceTransform (μs i) t) l (𝓝 (laplaceTransform μ t)) := by
  simpa [laplaceTransform_apply] using
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp h (laplaceKernelBoundedContinuous ht)

/-- **Tightness from convergent Laplace transforms.** If the Laplace transforms of a sequence of
finite measures on `ℝ≥0` converge on `[0, ∞)` to a function that is right-continuous at `0`, then
the sequence is tight.

This is the Laplace analogue of Mathlib's `isTightMeasureSet_of_tendsto_charFun`. Continuity of
the limit at `0` is what prevents mass from escaping to infinity: without it the Dirac masses at
`n` have transforms converging to the indicator of `{0}` and are not tight. -/
theorem isTightMeasureSet_range_of_tendsto_laplaceTransform {μ : ℕ → Measure ℝ≥0}
    [∀ n, IsFiniteMeasure (μ n)] {f : ℝ → ℝ} (hf : ContinuousWithinAt f (Ici 0) 0)
    (h : ∀ t, 0 ≤ t → Tendsto (fun n => laplaceTransform (μ n) t) atTop (𝓝 (f t))) :
    IsTightMeasureSet (range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
    rcases eq_or_ne ε ∞ with rfl | hε_top
    · exact ⟨1, one_pos, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' hε_top, (ENNReal.ofReal_toReal hε_top).le⟩
  -- Right-continuity of `f` at `0` gives a parameter `s > 0` with `f 0 - f s < δ / 2`.
  obtain ⟨s, hs, hfs⟩ : ∃ s : ℝ, 0 < s ∧ f 0 - f s < δ / 2 := by
    obtain ⟨η, hη, hfη⟩ := Metric.continuousWithinAt_iff.mp hf (δ / 2) (by positivity)
    refine ⟨η / 2, by positivity, ?_⟩
    have hdist := hfη (x := η / 2) (mem_Ici.mpr (by positivity))
      (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
    rw [Real.dist_eq] at hdist
    linarith [neg_abs_le (f (η / 2) - f 0)]
  -- Eventually the Laplace gap at `s` is also below `δ / 2`, so the Markov tail bound puts at
  -- most `δ` outside the ball of radius `s⁻¹`.
  have hgap : ∀ᶠ n in atTop, (μ n).real univ - laplaceTransform (μ n) s < δ / 2 := by
    have hlim := (h 0 le_rfl).sub (h s hs.le)
    simp only [laplaceTransform_zero] at hlim
    exact hlim.eventually (gt_mem_nhds hfs)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hgap
  have hc : 1 / 2 < 1 - Real.exp (-(s * s⁻¹)) := by
    rw [mul_inv_cancel₀ hs.ne']
    linarith [Real.exp_neg_one_lt_half]
  have htail : ∀ n, N ≤ n → μ n (Metric.closedBall 0 s⁻¹)ᶜ ≤ ε := by
    intro n hn
    refine (measure_compl_closedBall_le_sub_laplaceTransform_div (μ n) hs
      (inv_pos.mpr hs)).trans (le_trans (ENNReal.ofReal_le_ofReal ?_) hδε)
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hN n hn]
  -- The finitely many earlier measures are dominated by their sum, which is a single finite
  -- measure on a Polish space and hence tight.
  set ν : Measure ℝ≥0 := ∑ n ∈ Finset.range N, μ n
  obtain ⟨K, hK, hνK⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
      (isTightMeasureSet_singleton (μ := ν)) ε hε
  refine ⟨Metric.closedBall 0 s⁻¹ ∪ K, (isCompact_closedBall 0 s⁻¹).union hK, ?_⟩
  rintro - ⟨n, rfl⟩
  rcases lt_or_ge n N with hn | hn
  · calc μ n (Metric.closedBall 0 s⁻¹ ∪ K)ᶜ ≤ μ n Kᶜ :=
          measure_mono (compl_subset_compl.mpr subset_union_right)
      _ ≤ ν Kᶜ := Measure.le_iff'.mp (Finset.single_le_sum (f := μ)
          (fun _ _ => Measure.zero_le _) (Finset.mem_range.mpr hn)) Kᶜ
      _ ≤ ε := hνK ν rfl
  · exact (measure_mono (compl_subset_compl.mpr subset_union_left)).trans (htail n hn)

/-- **The continuity theorem for Laplace transforms.** If the Laplace transforms of a sequence of
finite measures on `ℝ≥0` converge on `[0, ∞)` to a function `f` that is right-continuous at `0`,
then `f` is the Laplace transform of a finite measure `ν`, and the sequence converges weakly
to `ν`. -/
theorem exists_representsLaplace_and_tendsto_of_tendsto_laplaceTransform
    {μ : ℕ → FiniteMeasure ℝ≥0} {f : ℝ → ℝ} (hf : ContinuousWithinAt f (Ici 0) 0)
    (h : ∀ t, 0 ≤ t → Tendsto (fun n => laplaceTransform (μ n) t) atTop (𝓝 (f t))) :
    ∃ ν : FiniteMeasure ℝ≥0, RepresentsLaplace ν f ∧ Tendsto μ atTop (𝓝 ν) := by
  -- The total masses `laplaceTransform (μ n) 0` converge, so they are bounded.
  obtain ⟨C, hC⟩ := (h 0 le_rfl).bddAbove_range
  have hmass : ∀ ν ∈ range μ, ν.mass ≤ C.toNNReal := by
    rintro - ⟨n, rfl⟩
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal', ← ENNReal.coe_toReal,
      FiniteMeasure.ennreal_mass, ← measureReal_def, ← laplaceTransform_zero]
    exact le_max_of_le_left (hC (mem_range_self n))
  have htight : IsTightMeasureSet {(ν : Measure ℝ≥0) | ν ∈ range μ} := by
    refine (isTightMeasureSet_range_of_tendsto_laplaceTransform hf h).subset ?_
    rintro - ⟨-, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  have hcompact := isCompact_closure_of_isTightMeasureSet_of_mass_le htight hmass
  -- Along every ultrafilter below `atTop` the sequence converges, by compactness, and every such
  -- limit represents `f`.
  have hlim : ∀ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ atTop →
      ∃ ν : FiniteMeasure ℝ≥0, RepresentsLaplace ν f ∧ Tendsto μ U (𝓝 ν) := by
    intro U hU
    obtain ⟨ν, -, hν : Tendsto μ U (𝓝 ν)⟩ := hcompact.ultrafilter_le_nhds (U.map μ)
      (by
        rw [Ultrafilter.coe_map, le_principal_iff, mem_map]
        exact univ_mem' fun n => mem_preimage.mpr (subset_closure (mem_range_self n)))
    exact ⟨ν, representsLaplace_iff.mpr ⟨inferInstance, fun t ht => tendsto_nhds_unique
      ((h t ht).mono_left hU) (hν.laplaceTransform ht)⟩, hν⟩
  -- Laplace uniqueness identifies all these limits, so the whole sequence converges.
  obtain ⟨ν, hνf, -⟩ := hlim (Ultrafilter.of atTop) (Ultrafilter.of_le atTop)
  refine ⟨ν, hνf, (tendsto_iff_ultrafilter _ _ _).mpr fun U hU => ?_⟩
  obtain ⟨ν', hν'f, hν'⟩ := hlim U hU
  rwa [FiniteMeasure.toMeasure_injective (hν'f.unique hνf)] at hν'

/-- **Weak convergence through Laplace transforms.** A sequence of finite measures on `ℝ≥0`
converges weakly to a finite measure `ν` if and only if its Laplace transforms converge to that
of `ν` at every parameter `t ≥ 0`.

This is the Laplace analogue of Mathlib's Lévy convergence theorem
`ProbabilityMeasure.tendsto_iff_tendsto_charFun`. -/
theorem tendsto_iff_forall_tendsto_laplaceTransform {μ : ℕ → FiniteMeasure ℝ≥0}
    {ν : FiniteMeasure ℝ≥0} :
    Tendsto μ atTop (𝓝 ν) ↔
      ∀ t, 0 ≤ t → Tendsto (fun n => laplaceTransform (μ n) t) atTop
        (𝓝 (laplaceTransform ν t)) := by
  refine ⟨fun h t ht => h.laplaceTransform ht, fun h => ?_⟩
  obtain ⟨ν', hν'ν, hν'⟩ := exists_representsLaplace_and_tendsto_of_tendsto_laplaceTransform
    ((continuousOn_Ici_laplaceTransform (ν : Measure ℝ≥0)).continuousWithinAt self_mem_Ici) h
  rwa [FiniteMeasure.toMeasure_injective
    (hν'ν.unique (representsLaplace_iff.mpr ⟨inferInstance, fun _ _ => rfl⟩))] at hν'

end TauCeti
