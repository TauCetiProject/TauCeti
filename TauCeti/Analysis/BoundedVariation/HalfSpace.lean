/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import TauCeti.Analysis.BoundedVariation.Translation
import TauCeti.MeasureTheory.Measure.Haar.HalfSpace

/-!
# Sets of locally finite perimeter with a constant outer normal

Let `u` be locally integrable with locally finite variation on an open set `Ω` of a
finite-dimensional real inner product space, so that `Du = σ_u |Du|` with the polar density `σ_u`
(`TauCeti.polarDensity`). If `⟪h, σ_u⟫ ≥ 0` at `|Du|`-almost every point, the derivative of `u` in
the direction `h` is a nonnegative measure, and `u` is nondecreasing along `h`:
`u x ≤ u (x + h)` for almost every `x` of an open set `V` whose segments `x + [0, 1] h` lie in `Ω`
(`TauCeti.ae_le_comp_add_of_ae_inner_polarDensity_nonneg`).

For the indicator of a set `s` of locally finite perimeter in the whole space whose outer normal
is a constant vector `ν` at `|Dχ_s|`-almost every point, this says that `s` is almost stable under
the translations by every `h` with `⟪h, ν⟫ ≤ 0`. Hence `s` agrees almost everywhere with `∅`, with
the whole space or with a half-space `{y | ⟪y, ν⟫ < c}`
(`TauCeti.ae_eq_setOf_inner_lt_of_ae_outerNormal_eq`). This is the rigidity step in the blow-up of
a set of finite perimeter at a point of its reduced boundary: a blow-up limit has a constant outer
normal, and is therefore a half-space.

## Main declarations

* `TauCeti.ae_le_comp_add_of_ae_inner_polarDensity_nonneg`: monotonicity along a direction in
  which the derivative measure is nonnegative.
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

open MeasureTheory TopologicalSpace Set
open scoped ENNReal RealInnerProductSpace

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

/-- A set of locally finite perimeter in the whole space whose outer normal is a constant vector
`ν` at `|Dχ_s|`-almost every point is almost stable under the translation by every `h` with
`⟪h, ν⟫ ≤ 0`: almost every `x ∈ s` has `x + h ∈ s`. -/
private theorem ae_mem_add_of_ae_outerNormal_eq
    (hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) μ)
    (hfin : ∀ K, IsCompact K →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U s ≠ ∞)
    (hν : ∀ᵐ y : (⊤ : Opens E) ∂variationMeasure μ ⊤ (s.indicator 1), outerNormal μ ⊤ s y = ν)
    (hh : ⟪h, ν⟫ ≤ 0) :
    ∀ᵐ x ∂μ, x ∈ s → x + h ∈ s := by
  have hle := ae_le_comp_add_of_ae_inner_polarDensity_nonneg (Ω := ⊤) (V := ⊤) (h := h)
    (hu.locallyIntegrableOn _) (fun K hK _ => by simpa [perimeter_def] using hfin K hK)
    (fun _ _ _ _ => by simp) ?_
  · rw [Opens.coe_top, Measure.restrict_univ] at hle
    filter_upwards [hle] with x hx hxs
    by_contra hxh
    simp only [indicator_of_mem hxs, indicator_of_notMem hxh, Pi.one_apply] at hx
    exact zero_lt_one.not_ge hx
  · filter_upwards [hν, ae_outerNormal_eq] with y hy hy'
    rw [← neg_neg (polarDensity μ ⊤ (s.indicator 1) y), ← hy', hy, inner_neg_right]
    exact neg_nonneg.2 hh

/-- **A set with a constant outer normal is a half-space.** Let `s` have locally finite perimeter
in the whole space, with outer normal equal to a constant vector `ν` at `|Dχ_s|`-almost every
point. Then `s` agrees almost everywhere with `∅`, with the whole space, or with a half-space
`{y | ⟪y, ν⟫ < c}`. -/
theorem ae_eq_setOf_inner_lt_of_ae_outerNormal_eq
    (hu : LocallyIntegrable (s.indicator (1 : E → ℝ)) μ)
    (hfin : ∀ K, IsCompact K →
      ∃ U : Opens E, K ⊆ (U : Set E) ∧ perimeter μ U s ≠ ∞)
    (hν : ∀ᵐ y : (⊤ : Opens E) ∂variationMeasure μ ⊤ (s.indicator 1), outerNormal μ ⊤ s y = ν) :
    s =ᵐ[μ] (∅ : Set E) ∨ s =ᵐ[μ] (univ : Set E) ∨ ∃ c : ℝ, s =ᵐ[μ] {y | ⟪y, ν⟫ < c} :=
  ae_eq_setOf_inner_lt_of_forall_inner_nonpos
    ((aemeasurable_indicator_const_iff (1 : ℝ)).1 hu.aestronglyMeasurable.aemeasurable)
    fun _ hh => ae_mem_add_of_ae_outerNormal_eq hu hfin hν hh

end TauCeti
