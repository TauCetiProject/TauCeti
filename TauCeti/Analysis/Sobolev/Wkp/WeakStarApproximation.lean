/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Mollification
public import TauCeti.MeasureTheory.Function.Lp.WeakStarApproximation
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Analysis.Convolution.Basic

/-!
# Approximation of bounded Sobolev derivative fields

The mollifications of a field in `L^∞(Ω)` are uniformly bounded by its essential supremum,
converge in every finite `Lᵖ` norm on compact subsets of `Ω`, and converge against every
`L¹(Ω)` scalar test function. Applied to the value and each iterated weak derivative of
`u ∈ W^{k,∞}(Ω)`, these results give lower-norm local approximation and weak-star convergence
of the entire derivative jet. The interior differentiation identities in
`TauCeti.Analysis.Sobolev.Wkp.Mollification` identify the mollified fields with classical
derivatives wherever the bump stays inside `Ω`.

No boundary regularity or finite measure of `Ω` is assumed. There is no claim of convergence
in the full `W^{k,∞}` norm.

## References

* L. C. Evans, *Partial Differential Equations*, Section 5.3.1.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Proposition 4.21.
-/

public section

noncomputable section

namespace TauCeti.Wkp

open ContinuousLinearMap Filter MeasureTheory Set TopologicalSpace
open scoped Convolution ENNReal Topology

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure] {Omega : Opens E}

/-- Mollifying a bounded field after zero extension preserves its essential supremum bound,
everywhere on the ambient space. This applies to every weak derivative field of a
`W^{k,∞}` function. -/
theorem norm_smoothField_top_le (phi : ContDiffBump (0 : E))
    (f : Lp F ∞ (mu.restrict Omega)) (x : E) : ‖smoothField phi f x‖ ≤ ‖f‖ := by
  have hb : ∀ᵐ y ∂mu, ‖(Omega : Set E).indicator (f : E → F) y‖ ≤ ‖f‖ := by
    filter_upwards [(ae_restrict_iff' Omega.isOpen.measurableSet).1
      (Lp.ae_norm_le_norm_top f)] with y hy
    by_cases h : y ∈ Omega
    · simpa only [indicator_of_mem h] using hy h
    · simp only [indicator_of_notMem h, norm_zero, norm_nonneg]
  rw [smoothField_def, convolution_lsmul]
  have hbound := (mu.measurePreserving_sub_left x).quasiMeasurePreserving.ae hb
  have hphi : Integrable (phi.normed mu) mu := phi.integrable_normed
  have hi := hphi.mul_const ‖f‖
  calc
    _ ≤ ∫ t, phi.normed mu t * ‖f‖ ∂mu := norm_integral_le_of_norm_le hi (by
      filter_upwards [hbound] with t ht
      simp only [norm_smul, Real.norm_of_nonneg (phi.nonneg_normed t)]
      exact mul_le_mul_of_nonneg_left ht (phi.nonneg_normed t))
    _ = ‖f‖ := by rw [integral_mul_const, phi.integral_normed, one_mul]

variable [CompleteSpace F]

/-- Mollified bounded derivative fields converge against arbitrary `L¹(Ω)` scalar tests.
The convergence is in norm in the field's codomain. -/
theorem tendsto_integral_smul_smoothField_top {I : Type*} {l : Filter I}
    {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    (f : Lp F ∞ (mu.restrict Omega)) {a : E → ℝ} (ha : IntegrableOn a Omega mu) :
    Tendsto (fun i ↦ ∫ x in Omega, a x • smoothField (phi i) f x ∂mu) l
      (𝓝 (∫ x in Omega, a x • f x ∂mu)) := by
  have hf := (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2
    (Lp.memLp f)
  have hlim := tendsto_integral_smul_normed_convolution_top hphi
    (ha.integrable_indicator Omega.isOpen.measurableSet) hf
  simpa only [smoothField_def, ← indicator_smul_left, ← indicator_smul,
    indicator_indicator, inter_self, integral_indicator Omega.isOpen.measurableSet] using hlim

/-- On every compact subset of `Ω`, the mollifications of a bounded derivative field converge
in `Lᵖ` for every finite `p ≥ 1`. -/
theorem tendsto_eLpNorm_smoothField_sub_top {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {I : Type*} {l : Filter I} {phi : I → ContDiffBump (0 : E)}
    (hphi : Tendsto (fun i ↦ (phi i).rOut) l (𝓝 0))
    (f : Lp F ∞ (mu.restrict Omega)) {K : Set E} (hK : IsCompact K) (hKO : K ⊆ Omega) :
    Tendsto (fun i ↦ eLpNorm (smoothField (phi i) f - (f : E → F)) p (mu.restrict K))
      l (𝓝 0) := by
  have hf : MemLp ((Omega : Set E).indicator (f : E → F)) ∞ mu :=
    (memLp_indicator_iff_restrict Omega.isOpen.measurableSet.nullMeasurableSet).2 (Lp.memLp f)
  have hlocal (S : Set E) (hS : IsCompact S) :
      MemLp ((Omega : Set E).indicator (f : E → F)) p (mu.restrict S) := by
    have : IsFiniteMeasure (mu.restrict S) := isFiniteMeasure_restrict.mpr hS.measure_lt_top.ne
    exact (hf.restrict S).mono_exponent le_top
  have hlim := tendsto_eLpNorm_normed_convolution_sub_restrict hp hphi hlocal hK
  refine hlim.congr fun i ↦ eLpNorm_congr_ae ?_
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  simp only [Pi.sub_apply, smoothField_def, indicator_of_mem (hKO hx)]

end TauCeti.Wkp
