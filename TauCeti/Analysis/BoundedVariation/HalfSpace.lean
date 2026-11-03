/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Analysis.BoundedVariation.Translation
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace

/-!
# Sets with a constant normal are half-spaces

Let `u` be locally integrable with locally finite variation on an open set `Ω` of a
finite-dimensional real inner product space, so that `Du = σ_u |Du|` with the polar density `σ_u`
(`TauCeti.polarDensity`). If `⟪h, σ_u⟫ ≥ 0` at `|Du|`-almost every point, the derivative of `u` in
the direction `h` is a nonnegative measure, and `u` is nondecreasing along `h`:
`u x ≤ u (x + h)` for almost every `x` of an open set `V` whose segments `x + [0, 1] h` lie in `Ω`
(`TauCeti.ae_le_comp_add_of_ae_inner_polarDensity_nonneg`).

Let `s` be a null-measurable set with `∫_s div φ ≥ 0` for every test vector field `φ` with
`⟪φ, ν⟫ ≥ 0` pointwise, the distributional form of `Dχ_s = -ν m` for a positive measure `m`.
Testing with `φ (-h)` for nonnegative scalar `φ` shows that `χ_s` is nondecreasing along every `h`
with `⟪h, ν⟫ ≤ 0`, so `s` is almost stable under these translations. Hence `s` agrees almost
everywhere with `∅`, with the whole space or with a half-space `{y | ⟪y, ν⟫ < c}`
(`TauCeti.ae_eq_setOf_inner_lt_of_forall_integral_divergenceCLM_mul_indicator_nonneg`). This
hypothesis needs no finite perimeter, and it is the form in which a blow-up limit at a point of
the reduced boundary is shown to have a constant normal
(`TauCeti.integral_divergenceCLM_mul_indicator_nonneg_of_tendsto_measure_symmDiff_inter`). This is
the rigidity step in the blow-up of a set of finite perimeter: a blow-up limit has a constant
normal, and is therefore a half-space.

In particular a set `s` of locally finite perimeter in the whole space whose outer normal is a
constant vector `ν` at `|Dχ_s|`-almost every point is a half-space up to a null set
(`TauCeti.ae_eq_setOf_inner_lt_of_ae_outerNormal_eq`).

## Main declarations

* `TauCeti.ae_le_comp_add_of_ae_inner_polarDensity_nonneg`: monotonicity along a direction in
  which the derivative measure is nonnegative.
* `TauCeti.ae_eq_setOf_inner_lt_of_forall_integral_divergenceCLM_mul_indicator_nonneg`: a set
  whose distributional normal is the constant `ν` is a half-space up to a null set.
* `TauCeti.ae_eq_setOf_inner_lt_of_ae_outerNormal_eq`: a set of locally finite perimeter with a
  constant outer normal is a half-space up to a null set.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.7.2 (the blow-up of the reduced boundary).
* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory TopologicalSpace Set TestFunction
open scoped ENNReal RealInnerProductSpace Distributions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω V : Opens E}
  {u : E → ℝ} {s : Set E} {h ν : E}

/-- **Monotonicity along a direction of nonnegative derivative.** Let `u` be locally integrable
with locally finite variation on `Ω`, and let `⟪h, σ_u⟫ ≥ 0` at `|Du|`-almost every point, so that
the derivative `⟪h, Du⟫` of `u` in the direction `h` is a nonnegative measure. Then
`u x ≤ u (x + h)` for almost every `x ∈ V`, as soon as the segments `x + [0, 1] h` starting in
`V` lie in `Ω`. -/
theorem ae_le_comp_add_of_ae_inner_polarDensity_nonneg (hu : LocallyIntegrableOn u Ω μ)
    (hfin : ∀ K, IsCompact K → K ⊆ Ω →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ totalVariationOn μ U u ≠ ∞)
    (hVΩ : ∀ t ∈ Icc (0 : ℝ) 1, MapsTo (· + t • h) V Ω)
    (hσ : ∀ᵐ y ∂variationMeasure μ Ω u, 0 ≤ ⟪h, polarDensity μ Ω u y⟫) :
    ∀ᵐ x ∂μ.restrict V, u x ≤ u (x + h) := by
  refine ae_le_comp_add_of_forall_integral_lineDeriv_mul_nonpos hu hVΩ fun φ hφ => ?_
  rw [integral_lineDeriv_mul_eq_neg_integral_mul_inner_polarDensity hu hfin, neg_nonpos]
  exact integral_nonneg_of_ae (hσ.mono fun y hy => mul_nonneg (hφ y) hy)

/-- A null-measurable set `s` with `∫_s div φ ≥ 0` for every test vector field `φ` with
`⟪φ, ν⟫ ≥ 0` pointwise is almost stable under the translation by every `h` with `⟪h, ν⟫ ≤ 0`:
almost every `x ∈ s` has `x + h ∈ s`. -/
private theorem ae_mem_add_of_forall_integral_divergenceCLM_mul_indicator_nonneg
    (hs : NullMeasurableSet s μ)
    (H : ∀ φ : 𝓓((⊤ : Opens E), E), (∀ y, 0 ≤ ⟪φ y, ν⟫) →
      0 ≤ ∫ y, divergenceCLM φ y * s.indicator 1 y ∂μ)
    (hh : ⟪h, ν⟫ ≤ 0) :
    ∀ᵐ x ∂μ, x ∈ s → x + h ∈ s := by
  have hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) μ :=
    LocallyIntegrable.indicator₀ (locallyIntegrable_const (1 : ℝ)) hs
  have hle := ae_le_comp_add_of_forall_integral_lineDeriv_mul_nonpos (Ω := ⊤) (V := ⊤) (h := h)
    (hu.locallyIntegrableOn _) (fun _ _ _ _ => by simp) fun φ hφ => ?_
  · rw [Opens.coe_top, Measure.restrict_univ] at hle
    filter_upwards [hle] with x hx hxs
    by_contra hxh
    simp only [indicator_of_mem hxs, indicator_of_notMem hxh, Pi.one_apply] at hx
    exact zero_lt_one.not_ge hx
  -- Test with the vector field `φ (-h)`, whose divergence is `-∂_h φ`.
  have hφh := H (postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (-h)) φ) fun y => by
    simpa [real_inner_smul_left, inner_neg_left] using mul_nonneg (hφ y) (neg_nonneg.2 hh)
  simpa [lineDerivOp_apply, lineDeriv_neg, integral_neg] using hφh

/-- **A set with a constant distributional normal is a half-space.** Let `s` be null-measurable
with `∫_s div φ ≥ 0` for every test vector field `φ` with `⟪φ, ν⟫ ≥ 0` pointwise, as holds when
the distributional derivative of `χ_s` is `-ν` times a positive measure. Then `s` agrees almost
everywhere with `∅`, with the whole space, or with a half-space `{y | ⟪y, ν⟫ < c}`. -/
theorem ae_eq_setOf_inner_lt_of_forall_integral_divergenceCLM_mul_indicator_nonneg
    (hs : NullMeasurableSet s μ)
    (H : ∀ φ : 𝓓((⊤ : Opens E), E), (∀ y, 0 ≤ ⟪φ y, ν⟫) →
      0 ≤ ∫ y, divergenceCLM φ y * s.indicator 1 y ∂μ) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {y | ⟪y, ν⟫ < c} :=
  ae_eq_setOf_inner_lt_of_forall_inner_nonpos hs fun _ hh =>
    ae_mem_add_of_forall_integral_divergenceCLM_mul_indicator_nonneg hs H hh

/-- **A set with a constant outer normal is a half-space.** Let `s` have locally finite perimeter
in the whole space, with outer normal equal to a constant vector `ν` at `|Dχ_s|`-almost every
point. Then `s` agrees almost everywhere with `∅`, with the whole space, or with a half-space
`{y | ⟪y, ν⟫ < c}`. -/
theorem ae_eq_setOf_inner_lt_of_ae_outerNormal_eq
    (hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) μ)
    (hfin : ∀ K, IsCompact K →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U s ≠ ∞)
    (hν : ∀ᵐ y : (⊤ : Opens E) ∂variationMeasure μ ⊤ (s.indicator 1), outerNormal μ ⊤ s y = ν) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {y | ⟪y, ν⟫ < c} := by
  refine ae_eq_setOf_inner_lt_of_forall_integral_divergenceCLM_mul_indicator_nonneg
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable)
    fun φ hφ => ?_
  rw [show ∫ y, divergenceCLM φ y * s.indicator 1 y ∂μ = _ by
    simpa only [divergenceCLM_apply] using
      integral_trace_fderiv_mul_indicator_eq_integral_inner_outerNormal
        (hu.locallyIntegrableOn _) (fun K hK _ => by simpa [perimeter_def] using hfin K hK)
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport φ.tsupport_subset]
  refine integral_nonneg_of_ae (hν.mono fun y hy => ?_)
  simpa only [Pi.zero_apply, hy] using hφ y

end TauCeti
