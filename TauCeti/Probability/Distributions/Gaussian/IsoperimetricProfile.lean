/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Quantile
public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv

/-!
# The Gaussian isoperimetric function

Write `φ = gaussianPDFReal 0 1` for the standard Gaussian density, `Φ = cdf (gaussianReal 0 1)`
for its distribution function and `Φ⁻¹ = (gaussianReal 0 1).quantile` for its quantile. This file
defines the **Gaussian isoperimetric function** `I(u) = φ(Φ⁻¹(u))` for `0 < u < 1`, with
`I(u) = 0` otherwise, and proves its basic properties: `I(Φ(x)) = φ(x)`, the symmetry
`I(1 - u) = I(u)`, continuity, positivity on `(0, 1)`, the unique maximum `φ(0)` at `1 / 2`,
smoothness on `(0, 1)` with `I' = -Φ⁻¹` and `I'' = -1 / I`, and strict concavity on `[0, 1]`.

`I(u)` is the Gaussian perimeter of a half-space of Gaussian measure `u`, and the right-hand side
of the Gaussian isoperimetric inequality. The endpoints are set apart because the quantile takes
the junk value `0` at the levels `0` and `1`, where `φ` would give `φ(0)` instead of `0`.

## Main declarations

* `TauCeti.Probability.gaussianIsoperimetricProfile` — the function `I`;
* `TauCeti.Probability.gaussianIsoperimetricProfile_cdf` — `I(Φ(x)) = φ(x)`;
* `TauCeti.Probability.gaussianIsoperimetricProfile_one_sub` — `I(1 - u) = I(u)`;
* `TauCeti.Probability.continuous_gaussianIsoperimetricProfile` — `I` is continuous on `ℝ`;
* `TauCeti.Probability.gaussianIsoperimetricProfile_pos_iff`,
  `TauCeti.Probability.gaussianIsoperimetricProfile_le`,
  `TauCeti.Probability.gaussianIsoperimetricProfile_lt_of_ne` — positivity exactly on `(0, 1)`
  and the unique maximum `φ(0)` at `1 / 2`;
* `TauCeti.Probability.hasDerivAt_gaussianIsoperimetricProfile`,
  `TauCeti.Probability.hasDerivAt_deriv_gaussianIsoperimetricProfile`,
  `TauCeti.Probability.contDiffOn_gaussianIsoperimetricProfile` — `I' = -Φ⁻¹`, `I'' = -1 / I`, and
  smoothness on `(0, 1)`;
* `TauCeti.Probability.strictConcaveOn_gaussianIsoperimetricProfile`,
  `TauCeti.Probability.locallyLipschitzOn_gaussianIsoperimetricProfile` — strict concavity on
  `[0, 1]` and local Lipschitz continuity on `(0, 1)`.

## References

* E. Milman, J. Neeman, *The Gaussian double-bubble and multi-bubble conjectures*, Ann. of Math.
  (2022), Section 1.2 and equation (1.1).
* M. Ledoux, *Concentration of measure and logarithmic Sobolev inequalities*, Séminaire de
  Probabilités XXXIII (1999), (1.4).
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ContDiff NNReal

namespace TauCeti.Probability

variable {u : ℝ}

/-! ### The Gaussian isoperimetric function -/

/-- The **Gaussian isoperimetric function** `I(u) = φ(Φ⁻¹(u))` for `0 < u < 1`, where `φ` is
the standard Gaussian density and `Φ⁻¹(u)` the quantile of the standard Gaussian law at level
`u`, and `I(u) = 0` otherwise. It is the Gaussian perimeter of a half-space of Gaussian measure
`u`. The endpoints are set apart because the quantile takes the junk value `0` at the levels `0`
and `1`. -/
def gaussianIsoperimetricProfile (u : ℝ) : ℝ :=
  if 0 < u ∧ u < 1 then gaussianPDFReal 0 1 ((gaussianReal 0 1).quantile u) else 0

/-- Unfolding lemma for `gaussianIsoperimetricProfile`. -/
theorem gaussianIsoperimetricProfile_def (u : ℝ) :
    gaussianIsoperimetricProfile u =
      if 0 < u ∧ u < 1 then gaussianPDFReal 0 1 ((gaussianReal 0 1).quantile u) else 0 :=
  (rfl)

/-- On `(0, 1)` the Gaussian isoperimetric function is `φ ∘ Φ⁻¹`. -/
theorem gaussianIsoperimetricProfile_of_mem_Ioo (hu : u ∈ Ioo 0 1) :
    gaussianIsoperimetricProfile u = gaussianPDFReal 0 1 ((gaussianReal 0 1).quantile u) :=
  ite_eq_left_iff.2 fun h => absurd hu h

/-- Outside `(0, 1)` the Gaussian isoperimetric function vanishes. -/
theorem gaussianIsoperimetricProfile_of_notMem_Ioo (hu : u ∉ Ioo 0 1) :
    gaussianIsoperimetricProfile u = 0 :=
  ite_eq_right_iff.2 fun h => absurd h hu

/-- The Gaussian isoperimetric function vanishes at `0`. -/
@[simp]
theorem gaussianIsoperimetricProfile_zero : gaussianIsoperimetricProfile 0 = 0 :=
  gaussianIsoperimetricProfile_of_notMem_Ioo (lt_irrefl 0 ·.1)

/-- The Gaussian isoperimetric function vanishes at `1`. -/
@[simp]
theorem gaussianIsoperimetricProfile_one : gaussianIsoperimetricProfile 1 = 0 :=
  gaussianIsoperimetricProfile_of_notMem_Ioo (lt_irrefl 1 ·.2)

/-- The Gaussian isoperimetric function at `Φ(x)` is `φ(x)`. -/
@[simp]
theorem gaussianIsoperimetricProfile_cdf (x : ℝ) :
    gaussianIsoperimetricProfile (cdf (gaussianReal 0 1) x) = gaussianPDFReal 0 1 x := by
  rw [gaussianIsoperimetricProfile_of_mem_Ioo
      ⟨cdf_gaussianReal_pos 0 one_ne_zero x, cdf_gaussianReal_lt_one 0 one_ne_zero x⟩,
    quantile_cdf_gaussianReal 0 one_ne_zero]

/-- Every level `0 < u < 1` is the value of `Φ` at the quantile. -/
private theorem exists_cdf_eq (hu : u ∈ Ioo 0 1) : ∃ x, cdf (gaussianReal 0 1) x = u :=
  ⟨_, cdf_quantile_gaussianReal 0 one_ne_zero hu⟩

/-- The Gaussian isoperimetric function is symmetric about `1 / 2`. -/
@[simp]
theorem gaussianIsoperimetricProfile_one_sub (u : ℝ) :
    gaussianIsoperimetricProfile (1 - u) = gaussianIsoperimetricProfile u := by
  by_cases hu : u ∈ Ioo 0 1
  · obtain ⟨x, rfl⟩ := exists_cdf_eq hu
    rw [← cdf_gaussianReal_zero_one_neg, gaussianIsoperimetricProfile_cdf,
      gaussianIsoperimetricProfile_cdf, gaussianPDFReal_zero_neg]
  · rw [gaussianIsoperimetricProfile_of_notMem_Ioo hu,
      gaussianIsoperimetricProfile_of_notMem_Ioo fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩]

/-- The Gaussian isoperimetric function is nonnegative. -/
theorem gaussianIsoperimetricProfile_nonneg (u : ℝ) : 0 ≤ gaussianIsoperimetricProfile u := by
  rw [gaussianIsoperimetricProfile_def]
  split_ifs
  exacts [gaussianPDFReal_nonneg _ _ _, le_rfl]

/-- The Gaussian isoperimetric function is positive exactly on `(0, 1)`. -/
@[simp]
theorem gaussianIsoperimetricProfile_pos_iff :
    0 < gaussianIsoperimetricProfile u ↔ u ∈ Ioo 0 1 := by
  by_cases hu : u ∈ Ioo 0 1
  · simpa [gaussianIsoperimetricProfile_of_mem_Ioo hu, hu] using
      gaussianPDFReal_pos _ _ _ one_ne_zero
  · simp [gaussianIsoperimetricProfile_of_notMem_Ioo hu, hu]

/-- The value of the Gaussian isoperimetric function at `1 / 2` is `φ(0) = (2π)^{-1/2}`. -/
@[simp]
theorem gaussianIsoperimetricProfile_half :
    gaussianIsoperimetricProfile 2⁻¹ = gaussianPDFReal 0 1 0 := by
  rw [← one_div, ← cdf_gaussianReal_self 0 one_ne_zero, gaussianIsoperimetricProfile_cdf]

/-- The Gaussian isoperimetric function is at most `φ(0) = (2π)^{-1/2}`. -/
theorem gaussianIsoperimetricProfile_le (u : ℝ) :
    gaussianIsoperimetricProfile u ≤ gaussianPDFReal 0 1 0 := by
  by_cases hu : u ∈ Ioo 0 1
  · rw [gaussianIsoperimetricProfile_of_mem_Ioo hu]
    exact gaussianPDFReal_le_self 0 1 _
  · rw [gaussianIsoperimetricProfile_of_notMem_Ioo hu]
    exact gaussianPDFReal_nonneg _ _ _

/-- The Gaussian isoperimetric function attains its maximum `φ(0)` only at `1 / 2`. -/
theorem gaussianIsoperimetricProfile_lt_of_ne (hu : u ≠ 1 / 2) :
    gaussianIsoperimetricProfile u < gaussianPDFReal 0 1 0 := by
  by_cases hu' : u ∈ Ioo 0 1
  · obtain ⟨x, rfl⟩ := exists_cdf_eq hu'
    have hx : x ≠ 0 := by
      rintro rfl
      exact hu (cdf_gaussianReal_self 0 one_ne_zero)
    rw [gaussianIsoperimetricProfile_cdf, gaussianPDFReal_zero_one, gaussianPDFReal_zero_one]
    have : 0 < x ^ 2 := by positivity
    gcongr ?_ * Real.exp ?_
    linarith
  · rw [gaussianIsoperimetricProfile_of_notMem_Ioo hu']
    exact gaussianPDFReal_pos _ _ _ one_ne_zero

/-! ### Derivatives -/

/-- The Gaussian isoperimetric function agrees with `φ ∘ Φ⁻¹` near every level in `(0, 1)`. -/
private theorem gaussianIsoperimetricProfile_eventuallyEq (hu : u ∈ Ioo 0 1) :
    gaussianIsoperimetricProfile =ᶠ[𝓝 u]
      fun w => gaussianPDFReal 0 1 ((gaussianReal 0 1).quantile w) := by
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw using
    gaussianIsoperimetricProfile_of_mem_Ioo hw

/-- The Gaussian isoperimetric function is smooth on `(0, 1)`. -/
theorem contDiffOn_gaussianIsoperimetricProfile {n : ℕ∞} :
    ContDiffOn ℝ n gaussianIsoperimetricProfile (Ioo 0 1) :=
  ((contDiff_gaussianPDFReal 0 1).comp_contDiffOn
    (contDiffOn_quantile_gaussianReal 0 1)).congr fun _ hw =>
      gaussianIsoperimetricProfile_of_mem_Ioo hw

/-- The derivative of the Gaussian isoperimetric function at `0 < u < 1` is `-Φ⁻¹(u)`. -/
theorem hasDerivAt_gaussianIsoperimetricProfile (hu : u ∈ Ioo 0 1) :
    HasDerivAt gaussianIsoperimetricProfile (-(gaussianReal 0 1).quantile u) u := by
  have h := (hasDerivAt_gaussianPDFReal 0 1 _).comp u
    (hasDerivAt_quantile_gaussianReal 0 1 hu)
  have hpos := gaussianPDFReal_pos 0 1 ((gaussianReal 0 1).quantile u) one_ne_zero
  refine (h.congr_of_eventuallyEq (gaussianIsoperimetricProfile_eventuallyEq hu)).congr_deriv ?_
  field_simp
  simp

/-- The second derivative of the Gaussian isoperimetric function at `0 < u < 1` is `-1 / I(u)`. -/
theorem hasDerivAt_deriv_gaussianIsoperimetricProfile (hu : u ∈ Ioo 0 1) :
    HasDerivAt (deriv gaussianIsoperimetricProfile) (-(gaussianIsoperimetricProfile u)⁻¹) u := by
  rw [gaussianIsoperimetricProfile_of_mem_Ioo hu]
  refine (hasDerivAt_quantile_gaussianReal 0 1 hu).neg.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hu.1 hu.2] with w hw using
    (hasDerivAt_gaussianIsoperimetricProfile hw).deriv

/-! ### Continuity and concavity -/

/-- The Gaussian isoperimetric function tends to `0` at `0` from the right. -/
private theorem tendsto_gaussianIsoperimetricProfile_nhdsGT_zero :
    Tendsto gaussianIsoperimetricProfile (𝓝[>] 0) (𝓝 0) := by
  have hq : Tendsto (gaussianReal 0 1).quantile (𝓝[>] 0) (cocompact ℝ) := by
    have h := tendsto_quantile_gaussianReal_nhdsGT_zero 0 1
    simp only [one_ne_zero, ↓reduceIte] at h
    exact (EReal.tendsto_coe_nhds_bot_iff.1 h).mono_right atBot_le_cocompact
  refine ((tendsto_gaussianPDFReal_cocompact 0 1).comp hq).congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with w hw using
    (gaussianIsoperimetricProfile_of_mem_Ioo hw).symm

/-- The Gaussian isoperimetric function is continuous at `0`. -/
private theorem continuousAt_gaussianIsoperimetricProfile_zero :
    ContinuousAt gaussianIsoperimetricProfile 0 := by
  refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · refine (continuousWithinAt_const : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) _ _)
      |>.congr_of_eventuallyEq ?_ gaussianIsoperimetricProfile_zero
    filter_upwards [self_mem_nhdsWithin] with w (hw : w ≤ 0) using
      gaussianIsoperimetricProfile_of_notMem_Ioo fun h => (h.1.trans_le hw).false
  · rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, gaussianIsoperimetricProfile_zero]
    exact tendsto_gaussianIsoperimetricProfile_nhdsGT_zero

/-- The Gaussian isoperimetric function is continuous on `ℝ`; in particular on `[0, 1]`. -/
theorem continuous_gaussianIsoperimetricProfile : Continuous gaussianIsoperimetricProfile := by
  have h0 := continuousAt_gaussianIsoperimetricProfile_zero
  have h1 : ContinuousAt gaussianIsoperimetricProfile 1 := by
    have h0' : ContinuousAt gaussianIsoperimetricProfile (1 - 1) := by rwa [sub_self]
    have h : ContinuousAt (fun w => gaussianIsoperimetricProfile (1 - w)) 1 :=
      h0'.comp (continuous_const.sub continuous_id).continuousAt
    simpa [gaussianIsoperimetricProfile_one_sub] using h
  refine continuous_iff_continuousAt.2 fun u => ?_
  rcases lt_trichotomy u 0 with hu | rfl | hu
  · refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [Iio_mem_nhds hu] with w hw using
      (gaussianIsoperimetricProfile_of_notMem_Ioo fun h => (h.1.trans hw).false).symm
  · exact h0
  rcases lt_trichotomy u 1 with hu' | rfl | hu'
  · exact (contDiffOn_gaussianIsoperimetricProfile (n := 0)).continuousOn.continuousAt
      (Ioo_mem_nhds hu hu')
  · exact h1
  · refine continuousAt_const.congr (f := fun _ => (0 : ℝ)) ?_
    filter_upwards [Ioi_mem_nhds hu'] with w hw using
      (gaussianIsoperimetricProfile_of_notMem_Ioo fun h => (h.2.trans hw).false).symm

/-- The Gaussian isoperimetric function is strictly concave on `[0, 1]`. -/
theorem strictConcaveOn_gaussianIsoperimetricProfile :
    StrictConcaveOn ℝ (Icc 0 1) gaussianIsoperimetricProfile := by
  refine StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc 0 1)
    continuous_gaussianIsoperimetricProfile.continuousOn ?_
  rw [interior_Icc]
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  intro a ha b hb hab
  rw [(hasDerivAt_gaussianIsoperimetricProfile ha).deriv,
    (hasDerivAt_gaussianIsoperimetricProfile hb).deriv, neg_lt_neg_iff]
  exact Measure.strictMonoOn_quantile_of_noAtoms _ ha hb hab

/-- The Gaussian isoperimetric function is locally Lipschitz on `(0, 1)`. -/
theorem locallyLipschitzOn_gaussianIsoperimetricProfile :
    LocallyLipschitzOn (Ioo 0 1) gaussianIsoperimetricProfile :=
  (strictConcaveOn_gaussianIsoperimetricProfile.concaveOn.subset Ioo_subset_Icc_self
    (convex_Ioo 0 1)).locallyLipschitzOn isOpen_Ioo

end TauCeti.Probability
