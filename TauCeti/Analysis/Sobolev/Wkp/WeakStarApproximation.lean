/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Mollification
public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Local approximation of bounded Sobolev functions

For `u ∈ W^{k+1,∞}(Ω)`, the classical order-`k+1` iterated gradient of the single smooth
approximant `smoothField phi (value (k + 1) u)` equals the mollification of its highest weak
derivative `iteratedGradient k u` wherever the closed bump ball stays inside `Ω`. There it
is bounded by the essential supremum of that weak derivative
(`norm_iteratedGradientChain_smoothField_value_top_le` in `Mollification.lean`). The two
fields agree eventually on any set with a positive thickening contained in `Ω`
(`eventually_eqOn_iteratedGradientChain_smoothField_value`, also in `Mollification.lean`).
Here we prove finite lower-`Lᵖ` convergence on bounded such sets and convergence against
arbitrary integrable test fields through continuous bilinear maps on measurable such sets.
In particular, both apply to compact subsets of `Ω`, by
`IsCompact.exists_thickening_subset_open`. Lower orders of the same approximant follow by
applying these results to `lowerOrder` and using `value_succ`.

The underlying zero-extended field mollifications also converge against integrable tests
on the whole domain. This does not assert convergence of classical derivatives near the
boundary: zero extension need not preserve weak derivatives there. No boundary regularity
or finite measure of `Ω` is assumed, and no full `W^{k,∞}` norm convergence is claimed.

## References

* L. C. Evans, *Partial Differential Equations*, Section 5.3.1.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 4.21.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open ContinuousLinearMap Filter MeasureTheory Metric Set TopologicalSpace
open scoped Convolution ENNReal Topology

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}

variable [CompleteSpace F]

/-- Zero-extended bounded field mollifications converge against integrable test fields on
any measurable subset of `Ω`. Specializing the bilinear map to `lsmul ℝ ℝ` gives scalar tests.
For classical derivatives of one smooth approximant, use the interior theorem below. -/
theorem _root_.ContinuousLinearMap.tendsto_setIntegral_bilin_smoothField_top
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (B : G →L[ℝ] F →L[ℝ] H) {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    (f : Lp F ∞ (mu.restrict Omega)) {s : Set E} (hs : MeasurableSet s)
    (hsO : s ⊆ Omega) {a : E → G} (ha : IntegrableOn a s mu) :
    Tendsto (fun i ↦ ∫ x in s, B (a x) (smoothField (phi i) f x) ∂mu) l
      (𝓝 (∫ x in s, B (a x) (f x) ∂mu)) := by
  have hf := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  have hlim := B.tendsto_integral_bilin_normed_convolution_top hphi
    (ha.integrable_indicator hs) hf
  have hsource (i : I) :
      (fun x ↦ B (s.indicator a x) (((phi i).normed mu ⋆[lsmul ℝ ℝ, mu]
        (Omega : Set E).indicator (f : E → F)) x)) =
      s.indicator (fun x ↦ B (a x) (smoothField (phi i) f x)) := by
    ext x
    by_cases hx : x ∈ s <;> simp [hx, smoothField_def]
  have htarget : (fun x ↦ B (s.indicator a x) ((Omega : Set E).indicator (f : E → F) x)) =
      s.indicator (fun x ↦ B (a x) (f x)) := by
    ext x
    by_cases hx : x ∈ s
    · simp [hx, hsO hx]
    · simp [hx]
  simpa only [hsource, htarget, integral_indicator hs] using hlim

/-- On every bounded subset of `Ω`, zero-extended mollifications of an `Lᵠ` field converge in
`Lᵖ` whenever `1 ≤ p < ∞` and `p ≤ q`, including `q = ∞`. -/
theorem tendsto_eLpNorm_smoothField_sub_restrict {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) (hpq : p ≤ q)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    (f : Lp F q (mu.restrict Omega)) {s : Set E} (hs : Bornology.IsBounded s)
    (hsO : s ⊆ Omega) :
    Tendsto (fun i ↦ eLpNorm (smoothField (phi i) f - (f : E → F)) p (mu.restrict s))
      l (𝓝 0) := by
  have hf := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  have : IsFiniteMeasure (mu.restrict (thickening 1 s)) :=
    isFiniteMeasure_restrict.mpr hs.thickening.measure_lt_top.ne
  have hlim := tendsto_eLpNorm_normed_convolution_sub_restrict hp hphi one_pos
    ((hf.restrict (thickening 1 s)).mono_exponent hpq)
  refine hlim.congr fun i ↦ eLpNorm_congr_ae ?_
  filter_upwards [(ae_restrict_mem Omega.isOpen.measurableSet).filter_mono
    (ae_mono (Measure.restrict_mono_set mu hsO))] with x hx
  simp only [Pi.sub_apply, smoothField_def, indicator_of_mem hx]

/-- For `u ∈ W^{k+1,q}(Ω)`, the classical order-`k+1` iterated gradient of
`smoothField (phi i) (value (k + 1) u)` converges to the highest weak derivative
`iteratedGradient k u` in `Lᵖ(s)` on any bounded set `s` with a positive thickening contained
in `Ω`, whenever `1 ≤ p < ∞` and `p ≤ q`. -/
theorem tendsto_eLpNorm_iteratedGradientChain_smoothField_value_sub_restrict
    {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (hp : p ≠ ∞) (hpq : p ≤ q)
    (k : ℕ) (u : Wkp mu Omega q (k + 1))
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    {s : Set E} (hs : Bornology.IsBounded s) {δ : ℝ} (hδ : 0 < δ)
    (hsO : thickening δ s ⊆ Omega) :
    Tendsto (fun i ↦ eLpNorm
      (iteratedGradientChain (smoothField (phi i) (value (k + 1) u)) k -
        (iteratedGradient k u : E → IteratedGradient E k)) p (mu.restrict s)) l (𝓝 0) := by
  apply (tendsto_eLpNorm_smoothField_sub_restrict hp hpq hphi (iteratedGradient k u)
    hs ((self_subset_thickening hδ s).trans hsO)).congr'
  filter_upwards [eventually_eqOn_iteratedGradientChain_smoothField_value k u hphi hδ
    (s := closure s) (by simpa only [thickening_closure] using hsO)] with i hi
  apply eLpNorm_congr_ae
  filter_upwards [(ae_restrict_mem isClosed_closure.measurableSet).filter_mono
    (ae_mono (Measure.restrict_mono_set mu subset_closure))] with x hx
  simp only [Pi.sub_apply, hi hx]

/-- For `u ∈ W^{k+1,∞}(Ω)`, the classical order-`k+1` iterated gradient of
`smoothField (phi i) (value (k + 1) u)` converges weak-star to `iteratedGradient k u` on
any measurable set `s` with a positive thickening contained in `Ω`, against integrable test
fields through the continuous bilinear map `B`. No boundedness of `s` is required. -/
theorem tendsto_setIntegral_bilin_iteratedGradientChain_smoothField_value_top
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (k : ℕ) (B : G →L[ℝ] IteratedGradient E k →L[ℝ] H)
    (u : Wkp mu Omega ∞ (k + 1))
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    {s : Set E} (hs : MeasurableSet s) {δ : ℝ} (hδ : 0 < δ)
    (hsO : thickening δ s ⊆ Omega) {a : E → G} (ha : IntegrableOn a s mu) :
    Tendsto (fun i ↦ ∫ x in s, B (a x)
      (iteratedGradientChain (smoothField (phi i) (value (k + 1) u)) k x) ∂mu) l
      (𝓝 (∫ x in s, B (a x) (iteratedGradient k u x) ∂mu)) := by
  apply (B.tendsto_setIntegral_bilin_smoothField_top hphi (iteratedGradient k u)
    hs ((self_subset_thickening hδ s).trans hsO) ha).congr'
  filter_upwards [eventually_eqOn_iteratedGradientChain_smoothField_value k u hphi hδ hsO]
    with i hi
  apply setIntegral_congr_fun hs
  intro x hx
  simp only [hi hx]

/-- For `u ∈ W^{k+1,∞}` on the whole space, the classical order-`k+1` iterated gradient of
`smoothField (phi i) (value (k + 1) u)` converges weak-star to `iteratedGradient k u` against
any integrable test field through `B`, without compact-support or finite-measure hypotheses. -/
theorem tendsto_integral_bilin_iteratedGradientChain_smoothField_value_top
    {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (k : ℕ) (B : G →L[ℝ] IteratedGradient E k →L[ℝ] H)
    (u : Wkp mu ⊤ ∞ (k + 1))
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    {a : E → G} (ha : Integrable a mu) :
    Tendsto (fun i ↦ ∫ x, B (a x)
      (iteratedGradientChain (smoothField (phi i) (value (k + 1) u)) k x) ∂mu) l
      (𝓝 (∫ x, B (a x) (iteratedGradient k u x) ∂mu)) := by
  simpa only [Measure.restrict_univ] using
    tendsto_setIntegral_bilin_iteratedGradientChain_smoothField_value_top k B u hphi
      MeasurableSet.univ one_pos (subset_univ _) ha.integrableOn

end TauCeti.Wkp
